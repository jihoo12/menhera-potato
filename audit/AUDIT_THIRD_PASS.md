# Third-pass dependent-inductive correctness review

## Revision, scope and result

Audited commit: **`52d6d10d0b51e55bf0c6d73949dfe82210a1a527`**.
The working tree was initially clean. This report describes the review of that
commit and the uncommitted corrections accompanying this report.

I read `AUDIT_SECOND_PASS.md`, then reviewed constructor formation/use, positivity,
indexed motives, branch construction, quotation and case reduction. Following the
user's narrowed scope, this is a review of dependent-inductive consistency, not a
repeat of the entire kernel audit or any external-system testing. Agda was run
locally on two small reference declarations and through the existing test suite.

**Two problems were reproduced and corrected:** a missing positivity check in
constructor result indices admitted a declaration outside the strictly positive
fragment; self-elimination during formation caused recursive revalidation and
stack overflow. The latter is a robustness/unsupported-feature issue, not a
logical false-acceptance result. The new combined telescope tests found no
additional field/IH permutation error. This is not a formal soundness proof.

## Checking boundary and supported fragment

The relevant ordinary entry point is `infer(&mut store, Ctx::empty(), term)`.
New typing probes use finite, well-scoped ASTs allocated normally in one store.
They do not fabricate semantic values, expected types, IDs or typing contexts.
Normal-form preservation checks use the expected type returned by successful
inference. The crash regression uses a local subprocess to isolate stack aborts.

The mathematical boundary assumes valid same-store arena references, immutable
checked syntax, and contexts constructed by the checker. Public mutable arenas,
semantic constructors and `Ctx` do not enforce those assumptions against arbitrary
Rust callers. That previously reported API limitation is not counted as a new
AST-level finding or resolved by these changes.

The implemented dependent-inductive fragment is:

* Closed, nominal single-family declarations, with explicit parameter and index
  telescopes. Later parameters may depend on earlier parameters; indices may
  depend on parameters and earlier indices. Implicit outer-local captures are
  rejected. There is no mutual-inductive declaration facility.
* Constructor fields form a dependent telescope. Result index expressions see
  all fields and parameters. Formal index slots remain in the body layout but
  cannot be referenced by fields or results: varying indices must be represented
  by explicit fields or computed expressions.
* A field is either syntactically self-free or exactly a saturated direct
  application of self, with the original parameters in declaration order and
  self-free index arguments. No function-valued, Sigma-contained or nested
  recursive occurrence is supported. Metadata must agree exactly with this test.
* Field universes must fit the declared universe. Parameters/indices are checked
  as a signature telescope, not treated as runtime constructor fields.
* **After this correction**, constructor result index expressions must also be
  syntactically self-free. This is a conservative restriction: no general
  variance analysis of self-containing index expressions is implemented, even
  for expressions that might be positive in a richer calculus.
* A declaration's eliminator is unavailable while that declaration is being
  formed. Elimination of previously formed datatypes inside a field or result
  expression remains available.
* Parameterized constructors require an expected type or annotation, since
  their syntax omits parameter arguments. Explicit result-index annotations are
  checked and then erased.
* Elimination uses a **unary motive uniform across the entire index telescope**,
  with fixed parameters. Runtime passes only the constructed value, never
  separate indices or parameters. Motives may compute from that value using
  supported elimination; they need not be constant. General indexed motives
  taking indices as explicit arguments, dependent pattern matching and
  fiber-specific motives are not implemented by this syntax.

## Binder/context invariants

All context lists below run outermost to innermost; index zero names the last
entry. Let caller depth be `d`, parameter count `p`, index count `n`, and let
`k` fields precede the field being checked.

| Location | Context / reference |
| --- | --- |
| Parameter type `P_j` | `Gamma, P_0, ..., P_(j-1)` |
| Index type `I_j` | `Gamma, P_0, ..., P_(p-1), I_0, ..., I_(j-1)` |
| Constructor field type `F_k` | `Gamma, self, I_0, ..., I_(n-1), P_0, ..., P_(p-1), F_0, ..., F_(k-1)` |
| Self in `F_k` | index `n + p + k` |
| Parameter `P_j` in `F_k` | index `k + p - 1 - j` |
| Formal index `I_j` in `F_k` | index `k + p + n - 1 - j`, forbidden to occur |
| Earlier field `F_j` in `F_k` | index `k - 1 - j` |
| Caller variable formerly at index `h` | index `h + 1 + n + p + k` |
| Constructor result expressions | Same body layout with `k = total field count`, no IHs |

`form_family` first validates the signature in signature order. It then chooses
index locals at levels `d+1+j` and parameter locals at levels `d+1+n+j`—their
**final body positions**. Signature types are evaluated with these chosen values
in signature order before the complete body context is assembled. Thus the
type of an index can refer to a parameter whose body slot comes later; field
checking only begins after the full body context exists. No partially assembled
body context is used to check such a field.

For result typechecking, `result_env` contains parameters followed by earlier
**computed result index values**, not formal index placeholders. Consequently
an index of type `B a` is checked at the preceding result expression's `a`.

At constructor use, all argument ASTs remain in the unchanged caller context.
`constructor_env` substitutes self, actual indices and parameters into body order,
then appends each checked argument value. It does not add source-level binders
or IHs while checking arguments. In inference without parameters the fresh
formal-index placeholders cannot affect a validated field/result: occurrence
checking forbids their use. In checking with parameters, canonical result indices
are compared against the expected fiber after all fields have been substituted.

## Combined constructor telescope analysis

The new fixture deliberately combines dependencies that separate Nat/Vec tests
would not exercise:

```text
D (A : Type0) (B : A -> Type0) : (a : A) -> B a -> Type0
leaf : (x : A) -> (y : B x) -> D A B x y
step : (x : A) -> (y : B x) -> (r : D A B x y)
    -> (z : B x) -> (s : D A B x z) -> D A B x z
```

`B` depends on parameter `A`; the second index depends on `B` and the first
index; field `z` depends on an earlier field across a recursive field; the two
children can have different second indices. The body base is
`[self, a, b, A, B]`.

| Stored position | Intended expression | Actual de Bruijn references |
| --- | --- | --- |
| field x | A | `Var(1)` |
| field y | B x | `Var(1) Var(0)` |
| field r | D A B x y | `Var(6) Var(3) Var(2) Var(1) Var(0)` |
| field z | B x | `Var(3) Var(2)` |
| field s | D A B x z | `Var(8) Var(5) Var(4) Var(3) Var(0)` |
| step results | x, z | `Var(4), Var(1)` |

The tests instantiate `A = Nat` and `B = Tag`, where `Tag : Nat -> Type0` has
two distinct constructors in each fiber. `Tag zero` and `Tag one` differ as
types; the two tags at zero differ as values. Thus dependencies do not all
collapse to a constant family. Substituting the wrong Tag fiber or the wrong
recursive child is rejected. A closed lambda constructing `leaf x y` confirms
that caller variables survive the body permutation and subsequent beta reduction.

## Branch and IH telescope analysis

For the requested conceptual constructor

```text
c : (x : A) -> (r : D i(x)) -> (y : B x) -> D j(x,r,y)
```

the branch is

```text
(x : A) -> (r : D i(x)) -> (ih_r : M r) -> (y : B x)
-> M (c x r y)
```

When the y domain is quoted, x is index 2, because r and its IH both intervene.
The constructor's stored y type still refers through its original field-only
telescope. `build_branch_type` keeps that substitution environment separate from
its growing branch depth, which is exactly the required distinction.

In general, let `R_k` count recursive fields preceding `F_k`. The field gets
branch level `d+k+R_k`. Its IH, if present, gets the following level. The IH type
is `M(field_value)` using that **same field value**, and is quoted after the field
binder is introduced. Only fields extend `field_env`; an IH only advances branch
depth. Wrapping the already-quoted domains in reverse order produces the Pi
chain without an additional shift.

For the combined fixture the branch is:

```text
x, y, r, IH-r, z, s, IH-s
```

At the completed branch, these are indices `[6,5,4,3,2,1,0]`. In particular:

* z's domain is `Tag x` with x at index 3 when that domain is checked;
* s's domain sees x at index 4 and z at index 0;
* the constructed result uses field indices `[6,5,4,2,1]`, excluding both IHs;
* `IH-r : M r` and `IH-s : M s` refer to children at indices 4 and 1 in the
  completed branch, respectively.

`case_reduce` iterates the same fields and validated flags, applying each field
and then, exactly when flagged, the recursive result for that field. It never
inserts a parameter, a formal index or a second unrelated recursive child.
The tests distinguish the children computationally: selecting the left IH yields
one, selecting the right IH yields two. They also check a manually annotated
branch telescope; replacing z's dependency on x with a dependency on IH-r is
independently well-typed as an alternative function, but correctly rejected as
this constructor's branch.

A dependent motive `M(t) = Q(fold(t)) -> Q(fold(t))` distinguishes neutral children
through case spines while remaining uniform over both indices. Using IH-r at
`M r` succeeds; ascribing it `M s` fails. Accepted normal forms are checked again
at the inferred type and compared with the expected result.

## Indexed-motive boundary

For actual parameters `ps`, generic motive validation constructs:

```text
Gamma, j0 : I0(ps), j1 : I1(ps,j0), ..., t : D ps js
```

Each generic index type is evaluated under parameters and the preceding generic
index values. Quoting the evaluated motive at the enlarged depth weakens caller
references correctly; raw caller syntax is not reinterpreted under extra binders.
The unary body must produce a type with this generic target as well as at the
original target fiber. A neutral motive of domain only `D Nat Tag zero (tag1 zero)`
fails generic validation, before branch arity is checked.

Branch construction supplies M with children at their own fibers. This is
justified by the required uniformity, not by treating a child's indices as equal
to the parent's. Runtime index erasure is compatible with this restricted rule:
branch fields and recursive calls provide the computational data, and there are
no additional runtime index arguments in the motive. This is a reasoned invariant
and tested example, not a proved erasure or substitution theorem.

## Findings and fixes

### Incorrect acceptance: negativity in a result index

Classification: **incorrect acceptance / SOUNDNESS relative to the intended
strictly positive declaration rules; closed AST, checker reachable**.

Minimal example:

```text
data Empty : Type0 where
D : Type0 -> Type0
c : D (D Empty -> Empty)
```

Under the result context `[self, formal_index]`, the inner D is `Var(1)`.
`infer(empty, D_definition)` returned `Ok(...)` at the audited commit.
`check_strict_positivity` only traversed `con.arg_types`; the empty field list
made this constructor pass. `form_family` checked that the result expression
was a type but did not check its self occurrence. A negative occurrence in an
index is still a negative occurrence in the constructor declaration.

This establishes acceptance of an invalid declaration; no inhabitant of Empty
or full inconsistency derivation is claimed. Local Agda also rejects the analogous
declaration specifically for an occurrence to the left of an arrow in a target
index. That comparison corroborates, rather than substitutes for, the missing
check in this implementation.

Before the fix, all five wrappers—Ann, beta application, Fst, Snd and Case—also
hid the negative expression successfully. A second example with two parameters,
two indices and two fields confirmed that the result self index is `p+n+k = 6`.

Fix: `check_strict_positivity` now rejects self occurrences in every result index,
using the existing binder-aware `var_occurs` traversal at `p+n+field_count`.
It does not normalize away occurrences or weaken any existing check. Self-free
function-type indices and field-dependent results still pass. The conservative
self-free requirement is now documented in `ConstructorDef`.

### Robustness: invoking an unfinished eliminator

Classification: **PANIC/ROBUSTNESS, with unsupported self-elimination now rejected**.
This uses closed well-scoped syntax, not internal API fabrication. It did not
produce logical false acceptance.

Minimal shape:

```text
D : Nat -> Type0
base : D zero
step : (r : D zero)
    -> D (case r return Nat of base => zero; step _ _ => zero)
```

While checking the step result, `infer(Case r)` obtains D as the target type and
calls `infer(D_definition)` to validate it. That starts the same formation check
again. Before the fix, the subprocess aborted with:

```text
thread ... has overflowed its stack
fatal runtime error: stack overflow, aborting
```

Fix: reject Case when its target belongs to an inductive currently being formed,
returning `UnsupportedSelfElimination` before revalidation. Under ordinary checker
operations only formation inserts concrete family values as context locals (self);
ordinary binders and formal parameters/indices are neutrals. The helper searches
these enclosing formation frames. This uses an existing context invariant instead
of adding a mutable validation cache. A future change introducing other concrete
context locals must revisit that representation-dependent test.

The nearby positive control computes a result index by eliminating a Nat field,
then constructs and eliminates the resulting indexed value successfully. Thus
elimination in result expressions is not rejected wholesale. Recursive elimination
after a declaration has been formed also continues to pass the combined tests.

## Regression coverage and changes

`tests/audit_third_pass.rs` adds 13 tests:

| Test purpose | Evidence |
| --- | --- |
| Negative result index | Closed declaration rejected; paired Agda negative test |
| Self-free function result index | Declaration/constructor accepted; paired Agda positive test |
| Combined dependent telescope | Both recursive IH selections compute the expected numeral |
| Wrong field / child fiber | Both rejected; adjacent correct construction accepted |
| Caller context | Closed dependent constructor lambda checks and beta-reduces |
| Dependent motive | Correct child's IH accepted, other child's IH rejected |
| Field following an IH | Independently well-typed wrong branch dependency rejected |
| Specialized motive | Generic two-index validation rejects a fixed-fiber motive |
| Recursion metadata | All 32 flag vectors tested; only fields 2 and 4 recursive; wrong lengths rejected |
| Hidden negative result | All five wrappers rejected with a self-free control |
| Self-elimination during formation | Subprocess returns rejection rather than stack abort |
| Already-formed elimination | Nat elimination inside a result expression remains accepted |
| Shifted result self slot | Two parameters, two indices, two fields; negative self rejected, field result accepted |

Production changes are limited to `src/check.rs` (result-index occurrence check,
formation-frame detection and one new error) and documentation in `src/term.rs`.
`build_branch_type`, constructor substitution, the runtime evaluator, conversion,
and existing tests were not changed. Two local reference fixtures were added:
`ResultIndexNegative.agda` and `ResultIndexPositive.agda`.

The new tests were copied to an untouched archive of the audited commit to verify
before-fix behavior: **9 passed, 4 failed**. The failures were the direct negative
index, wrapped negatives, shifted negative index, and stack-overflow regression.
This also confirms the positive telescope probes already worked before the fixes.

## Final verification

`cargo test`: **133 passed, 0 failed, 0 ignored**, exit status 0.
All 13 new tests and all 120 pre-existing tests pass. Local Agda checks ran; they
were not skipped. The stack-overflow regression's child process is part of its
single parent test, not an additional counted test.

| Cargo target | Passed |
| --- | ---: |
| library unit tests | 3 |
| binary unit tests | 0 |
| audit | 15 |
| audit_final | 14 |
| audit_inductive | 21 |
| audit_second_pass | 8 |
| audit_third_pass | 13 |
| differential_test | 7 |
| indexed_family | 8 |
| kernel | 44 |
| doc tests | 0 |

Changed Rust files pass rustfmt checking; `git diff --check` passes.

## Remaining assumptions and assessment

The review found and corrected one invalid-declaration acceptance and one
unsupported-formation crash. It did not uncover another permutation mismatch in
the reviewed constructor/branch telescopes. The positive combined tests and the
manual binder derivation support their internal agreement, but do not prove it
for all possible terms.

Unverified obligations include substitution/weakening for every dependent
signature and body permutation; type preservation of quoting reconstructed branch
telescopes; uniform-motive substitution across arbitrary dependent index tuples;
adequacy of the syntactic positivity/occurrence traversal; and normalization and
subject reduction for the full supported combination. Tests cover representative
telescopes, not an exhaustive enumeration or a machine-checked metatheory.

Unsupported features include implicit inductive captures, general indexed motives,
mutual/inductive-recursive definitions, self-containing result-index expressions,
self-elimination during formation, and recursive fields requiring higher-order or
nested induction hypotheses. Conservative syntactic rejection is not conversion
completeness. Public low-level APIs and unrestricted resource use also remain
outside a sealed trusted checking boundary.

**No formal soundness claim is made.** The two reported defects are corrected;
the passing suite is empirical evidence accompanying the invariant analysis,
not a basis for declaring the kernel formally sound or its entire Rust API trusted.
