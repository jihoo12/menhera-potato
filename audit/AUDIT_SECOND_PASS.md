# Second-pass kernel audit — 2026-09-16

Audited starting commit: `39b3fcb0d7710fbe84805dca34cec075d2d548e3`.
The initial working tree was clean. The reported patch was committed, so the
relevant diff was `git show HEAD`, against `4419c64`, rather than an uncommitted
working-tree diff. No external reference kernel was used to decide these fixes;
the repository's existing Agda differential tests were executed.

## 1. Verdict on the previous finding

**Not a bug under the intended context-relative de Bruijn semantics.** The
previous regression does not demonstrate a soundness vulnerability reachable
from a well-scoped AST through `infer(Ctx::empty(), term)`.

It allocates two level-0 neutrals and two environments manually, evaluates
`Var(0)` in each, then calls `conv` at **depth 0**. Neither free variable is
in scope at that depth. Merely having different environment allocations does
not establish that their level-0 entries denote different logical locals.
If they represent the same context, those entries denote the same local; if
they represent different contexts, an explicit common-context renaming is
needed before conversion. Their allocation is possible through the low-level
API, but the asserted interpretation is outside the conversion invariant.

The relevant invariant is: in one logical context of depth d, a free level
l < d identifies its unique binder. Evaluation environments are substitutions
into that context, not globally unique namespaces. Their lengths need not be d.
The source audit gives the following preservation argument:

* `Ctx::bind` assigns the next unused level d. Earlier context values persist.
  Distinct simultaneous locals thus have distinct levels.
* Lookup returns the stored value. `eval`, `apply`, and `inst` substitute values;
  they do not rename a captured local using the closure environment's length.
* Pi, Sigma, lambda and function-eta conversion use **one shared fresh value**
  to instantiate both sides at depth d, then compare at d+1. A local cannot
  escape such an instantiation into the parent conversion: the result is a bool.
* Inductive formation assigns parameter and index neutrals distinct final body
  levels before permuting them into signature order. Its preliminary signature
  context does not escape into the body context. Constructor-use placeholder
  index slots cannot occur in validated field/result syntax.
* Branch construction assigns fields their final levels, reserves IH levels,
  quotes at that telescope depth, and evaluates the resulting Pi telescope in
  the caller context. It does not combine unrelated checking contexts.
* Generic indexed-motive checking allocates two representations at each new
  index level (the chosen index and `Ctx::bind`'s local). These intentionally
  denote the **same** binder. The generic context is local to that check.

I found no checker path that imports two distinct logical locals at the same
level into one conversion context. The closed regression rejecting
`lambda A B x. x : (A B : Type0) -> A -> B` exercises the opposite requirement.
This argument concerns neutral naming, not a proof of the whole kernel: the
separate inductive vulnerabilities below were present with and without IDs.

## 2. Verdict on the patch

The patch added `Neutral.id`, a store counter reset by `clear`, a counter
reference in `ValueBuilder`, allocation in `neut_var`, preservation through
App/Fst/Snd/Case spines, and an ID comparison in `conv`. Quoting still discarded
ID and used only level. It also added the invalid cross-context regression.

**Replaced the patch.** Runtime identity is not necessary for this level-based
representation. A nominal-local design could be correct with explicit renaming
and a matching quotation/context API, but adding an allocation counter alone
changes the existing equality semantics.

`same_logical_context_can_be_reconstructed_for_conversion` constructs two
representations of `A : Type0` using checked types and `Ctx::bind`, checks
`Var(0)` in each, and quotes in one/evaluates in the other. With IDs, conversion
fails; with context-relative levels it succeeds. This is a public-operation
**representation/API completeness counterexample**, not a closed-AST logical
exploit or proof that one ordinary checker invocation reconstructs that context.

Crucially, no fixed-context closed-input false negative caused by IDs was found.
The new checked eta/spine/round-trip probes also pass on the original ID patch.
In a fixed environment quote/eval restores free variables by environment lookup;
newly quoted bound variables are re-instantiated with a shared comparison local.
It would be incorrect to claim all quote/eval round trips fail with IDs.

Operation review:

| Operation | Identity and scoping behavior |
| --- | --- |
| `fresh_var`, context extension | Level denotes the binder in the supplied logical context; allocation is irrelevant. |
| Environment lookup, `eval`, closure `inst`, `apply` | Substitution preserves existing values and captures. Beta does not allocate a replacement for an argument. |
| `fst`, `snd`, application spines | Preserve the neutral head; pair projections return the stored component. |
| Neutral case spines | Preserve the target head; conversion compares motives and all branches. |
| Constructor `case_reduce` | Uses fields in order, with each direct recursive IH immediately after its field; flags are checked first. |
| `quote`, re-evaluation | Index is d-l-1. Re-evaluate free variables in the corresponding context; bound variables are reintroduced at the quoted binder. |
| Pi/Sigma conversion, function eta | Both closures/applications receive the same comparison local. |
| Pair eta | Compares both projections of the same neutral pair. |

The finite tests exercise reflexivity, symmetry and transitivity within three
representations of checked values; function/pair eta in both directions; beta
substitution of an outer capture; application congruence; and typed quote/eval
round trips of variables, applications, projections, lambdas, Pi, Sigma and
neutral cases. Existing tests add dependent Pi/Sigma/pair cases and recursive,
indexed elimination. This is evidence, not a universal equivalence or
normalization theorem for all kernel-reachable values.

## 3. Confirmed counterexamples

All test names below are in `tests/audit_second_pass.rs`.

### Soundness: missing constructor universe bound

Invariant: each constructor field type must inhabit a universe no larger than
the inductive's declared universe. Original `form_family` called `check_is_type`
for each field and discarded the resulting universe.

Minimal declaration accepted from an empty context:

```text
data Bad : Type0 where pack : Type0 -> Bad
```

The field `Type0` inhabits `Type1`. Accepting this declaration violates predicative
MLTT's inductive formation rule. This is an invalid-inductive acceptance exploit;
a full paradox/inhabitant of Empty is not claimed or needed for that classification.
`constructor_field_universe_must_fit_inductive_universe` failed before the fix.
`field_bound_applies_through_constructor_entry_and_allows_large_declarations`
also verifies the direct Con entry path and a valid Type1 declaration.

Fix: infer each field's sort, require `field_level <= declared_level`, then
bind its evaluated type. Parameters are not indiscriminately subjected to this
bound: e.g. `Box (A : Type0) : Type0` with field `A` remains supported.

### Soundness: captured inductive environments are erased

Invariant: substituting distinct captured types into a declaration must retain
those dependencies in its semantic identity and constructor interpretation.
Original `eval(Inductive)` stored only `def` and explicit arguments. `conv`
compared those, while `quote` reused the original definition syntax. There was
no captured environment to substitute or reify.

Closed AST counterexample, sharing the same declaration node D:

```text
F = (lambda A. data D : Type0 where box : A -> D) : Type0 -> Type0
(lambda x. x) : F Nat -> F Empty
```

`infer(empty, Ann(identity, cast_type))` accepted this invalid identity function.
It requires no fabricated semantic values, unchecked expected type or context
mutation. Both instances evaluate to the same `Inductive { def: D, args: [] }`.
`captured_inductive_definitions_cannot_be_conflated` failed before the fix.

Fix: reject declarations referring to caller locals, including references found
through nested syntax, with `UnsupportedInductiveCapture`. Existing well-scoped
checking rejects out-of-range references. Explicit parameterized declarations
remain supported and distinguish `Box Nat` from `Box Empty`.

**Compatibility limitation:** implicit captures are now unsupported, including
otherwise legitimate local declarations. This deliberately restricts accepted
syntax to what the current nominal representation can safely implement. It is
not full closure support. The old formation-only capture test was changed to
assert this explicit rejection; a new positive parameterized Box test covers
the supported replacement. Restoring captures requires carrying and reifying
their substitutions throughout checking, constructors, NBE and quotation.

### Incompleteness: optional constructor indices affect equality

Invariant: validated optional result-index annotations do not change a
constructor's computational meaning. Original evaluation retained user-provided
indices and `conv(Con, Con)` compared their lengths, so omission differed from
supplying the correct canonical index.

For `D : Nat -> Type0`, `c : D zero`, let c0 omit its index annotation and c1
explicitly supply zero. This valid closed term was rejected:

```text
(lambda F x. x) : (F : D zero -> Type0) -> F c0 -> F c1
```

`explicit_constructor_indices_do_not_change_definitional_equality` failed with
`ConversionFailure`. Fix: erase these checked annotations during evaluation,
just as Ann's type is erased. Checking still validates their types and equality
with canonical indices before evaluation. No constructor checking was weakened.
This issue predates and is independent of neutral IDs.

## 4. Changes made

* `src/value.rs`: remove allocation IDs/counter access; document context-relative
  levels and the now-erased constructor annotation payload.
* `src/nbe.rs`: remove counter initialization/reset and ID comparison; document
  conversion's context precondition; erase optional constructor index annotations.
* `src/check.rs`: add `UnsupportedInductiveCapture`, reject captured declarations,
  and enforce the field universe bound. Positivity, recursion flags, motive and
  index validation remain intact.
* `src/term.rs`: document the explicit-parameter requirement.
* `tests/audit.rs`: remove the artificial cross-context soundness assertion.
* `tests/audit_final.rs`: replace the unsafe capture-formation acceptance contract
  with explicit unsupported-capture rejection.
* `tests/audit_second_pass.rs`: eight regressions/property probes, including
  positive controls for explicit parameters and larger universes.
* `AUDIT_SECOND_PASS.md`: this report. Rustfmt also reformatted touched files.

## 5. Verification

Before fixes, the initial three new regressions failed individually. The optional
index regression was subsequently reproduced failing before its evaluator fix.
For isolation, the final eight-test file was also run against an untouched archive
of the original commit in `/tmp/menhera-second-pass-original`: **3 passed,
5 failed**. The failures were capture conflation, two universe-bound assertions,
context reconstruction with IDs, and optional-index equality.

Final `cargo test`: **120 passed, 0 failed, 0 ignored** (exit 0).

| Target | Passed |
| --- | ---: |
| library unit tests | 3 |
| audit | 15 |
| audit_final | 14 |
| audit_inductive | 21 |
| audit_second_pass | 8 |
| differential_test | 7 |
| indexed_family | 8 |
| kernel | 44 |
| binary unit tests / doc tests | 0 / 0 |

Agda was installed and the differential checks actually ran. Formatting of
changed Rust files and `git diff --check` pass. Repository-wide `cargo fmt --check`
also detects pre-existing formatting in untouched `tests/differential_test.rs`;
that unrelated file was left unchanged.

## 6. Remaining trusted-kernel risks

* This is not a proof of soundness, normalization, subject reduction, or
  conversion completeness. Finite tests cannot establish those properties.
* Raw `Store` arenas, `Ctx`, IDs and semantic constructors are public and mutable.
  `check` assumes its context and expected semantic type are valid; `eval` assumes
  checked syntax. Forged/stale/cross-store IDs, cycles or post-check mutation are
  not a validated untrusted-AST boundary and can panic or invalidate assumptions.
  A hardened external interface should seal these capabilities. No such internal
  fabrication was used to classify the two AST-level soundness findings.
* Constructor signature/body permutation and interleaved branch/IH quotation
  remain a significant proof obligation, especially dependent parameters,
  multiple indices and recursive child indices. Existing tests cover examples,
  not all telescopes. Unary indexed motives intentionally support a restricted
  uniform fragment rather than a general dependent indexed recursor.
* Positivity is deliberately syntactic and conservative: only saturated direct
  recursive fields with unchanged parameters are accepted. Its binder walk,
  including nested syntax and result expressions, has not been formally verified.
* Universe normalization/cumulativity was inspected: normalized maxima of
  constants and rigid variable offsets give a conservative pointwise inequality
  check. Arithmetic uses finite u32 counters; resource bounds, overflow behavior,
  recursive traversal costs and arena capacity are not hardened here.
* Case equality is structural, and nominal inductive definitions use arena
  identity rather than structural equality. Completeness outside the supported
  fragment and resource-exhaustion behavior remain separate from logical soundness.

The project should not receive a “trusted” designation on the basis of this audit.
