# SCOPE fragment: ordinary-term renaming

## Specification stage

This artifact formalizes existing syntax in [the canonical specification](../formal_system.md)
§1.2, context length and extension in §3.1, the Var/Pi/Sigma rules in
§3.2, Lam in §3.3, and relative indices in §7. It proposes no new kernel
rule and makes no semantic change. The canonical specification is unchanged.

Selected statement: for all natural depths n, m, raw ordinary terms t and
maps ρ : Nat → Nat, if every i < n satisfies ρ(i) < m and Scoped n t,
then Scoped m (rename ρ t). The weakening corollary uses ρ = successor
and m = n + 1 (adding a newest context entry).

Only Var, Lam, Pi, App, Univ, Ann, Sigma, Pair, Fst and Snd are represented.
Scope is an independent inductive predicate on raw syntax, not a typing
judgment and not defined by Rust checker acceptance. Contexts are erased to
lengths; this does not assert their types are well-formed. Universe labels
are an arbitrary parameter `Label : Set`, unchanged by term renaming. It
can be instantiated with the raw level expressions of §1.1 or valid level
references; no equality, normalization, ordering or binding of labels is used.

Binder equations: lift ρ 0 = 0; lift ρ (suc i) = suc (ρ i).
Lam's body and Pi/Sigma's second child use lift ρ and scope depth n + 1.
Pi/Sigma domains and every other child stay at depth n. Pair's second
component does not bind. Ann checks scope of both children despite erasure
in evaluation. Renamings need not be injective: the claim is only scope.

Examples required: closed Lam (Var 0); Pi/Sigma with closed universe domain
and Var 0 codomain; rejection of closed Var 0, Lam (Var 1), and Pi/Sigma
with Var 0 domain. Weakening Lam (App (Var 1) (Var 0)) must produce
Lam (App (Var 2) (Var 0)), preserving the locally bound variable.

## Proof and implementation stages

Specification status: existing rules, unchanged. Proof status: **proved
(mechanized)** for the fragment stated above. Implementation status: Agda
syntax, operation and proof implemented; production Rust unchanged. This
milestone adds a mathematical syntax operation, not a Rust renaming function.

Files: [Syntax.agda](agda/Scope/Syntax.agda) defines raw terms, strict natural
order and independent scope evidence; [Renaming.agda](agda/Scope/Renaming.agda)
defines `MapsInto`, `lift`, `rename`, `rename-scoped` and `weaken-scoped`;
[Examples.agda](agda/Scope/Examples.agda) contains positive, negative and
renaming-computation checks. Negative examples are functions to an empty
datatype, checked successfully, rather than deliberately failing modules.

### Complete proof structure

`lift-scoped` proves that a map respecting bounds n → m respects bounds
n+1 → m+1 after lifting. A witness of i < n+1 has two cases: zero maps to
zero, which is below m+1; successor i has a witness i < n, so the hypothesis
gives ρ(i) < m and successor preserves this strict bound.

`rename-scoped` is structural induction on the supplied `Scoped` derivation,
generalized over target depth and renaming:

- Var: apply the `MapsInto` hypothesis to its index-bound witness.
- Lam: apply the induction hypothesis to its body with `lift-scoped`.
- Pi and Sigma: apply the induction hypothesis to the domain with the
  original map, and to the codomain with the lifted map.
- App, Ann and Pair: apply the induction hypotheses to both children with
  the original map.
- Fst and Snd: apply the induction hypothesis to the sole child.
- Univ: its unchanged label is scoped at every term depth.

These exhaust all ten constructors. The recursive calls use strict
subderivations; `rename` itself recurses on strict subterms. For weakening,
i < n implies suc i < suc n by `s<s`, so instantiate `rename-scoped` with
successor. No typing, conversion, normalization or evaluation fact is assumed.

### Dependencies and trust

The fragment has no unresolved mathematical dependencies and uses no
postulates, holes, termination overrides or imported proof libraries.
All three modules enable `--safe --without-K`. The theorem imports only
Agda's builtin naturals through the syntax module; examples additionally
use builtin propositional equality. Trust rests on Agda 2.8.0's type,
positivity, coverage and termination checking and its builtin definitions.
Agda is the metalanguage: its datatypes/functions are not additional
features of the object kernel. This is a syntactic scope-preservation
result, not algorithmic typing soundness or reduction preservation.

### Specification → theorem → implementation correspondence

| Canonical source | Mechanization | Audited Rust correspondence (not refinement proof) |
|---|---|---|
| §1.2 ordinary constructors | `Term`, `Scoped`, all cases of `rename-scoped` | `Term` in `src/term.rs` |
| §3.1 context extension, §3.2 Var, §7 newest index 0 | `Nat` depth, `_<_`, `MapsInto`, `lift-scoped` | `Ctx::bind`, `lookup_type` in `src/check.rs`; `env_lookup` in `src/value.rs` |
| §1.2, §3.2 Pi/Sigma, §3.3 Lam | lifted body/codomain cases | `check`, `infer`, and binder cases of `var_occurs` in `src/check.rs` |
| §1.1 universe expressions independent of term binders | opaque unchanged `Label` | `Term::Univ(LevelId)`; no level algorithm verified |
| Scope consequence of these conventions | `rename-scoped`, `weaken-scoped` | no production syntax-renaming function introduced or certified |

The conceptual embedding maps each represented constructor to the same
canonical constructor and keeps its child order and variable index. At
context length n, index zero is the newest entry; extending the context
shifts older free indices. Neither neutral absolute levels (§1.3/§7) nor
universe levels are term indices. In particular, this proof does not model
quotation's `depth - level - 1` calculation (§4.5).

Raw finite trees abstract away arena sharing. Relating a Rust term to such
a tree requires valid references and finite unfolding. Applying this model
to machine indices additionally requires representable indices/depths and
non-overflowing increments. Those are pending REFINE obligations, not
consequences of Agda's unbounded naturals. No arena identity is identified:
Inductive, Con and Case are absent from this fragment.

### What remains open and next lemma

SCOPE remains **Open** overall. Remaining work includes substitution scope
preservation; an independent typing/context relation and typing weakening
and substitution; environments/closures and their interpretation; neutral
levels and quotation; all inductive declarations, constructors, motives and
branches; and signature/body permutation preserving interpretation. The
canonical constructor order `self | formal indices | params | fields` and
interleaved branch field/IH binders are not reduced to ordinary context
lengths by this theorem. Their closure, forbidden-slot and nominal-identity
conditions require separate treatment. No global soundness, normalization,
canonicity or consistency claim follows.

The natural next lemma is simultaneous substitution scope preservation on
this same fragment: if every i < n maps to a term scoped at m, substituting
into a term scoped at n yields a term scoped at m. Under a binder, map zero
to Var 0 and each successor to the weakened substituted term; the checked
`weaken-scoped` corollary supplies that lifting obligation.

## Validation

Agda 2.8.0 actually ran and checked all three modules successfully:

```sh
agda --no-libraries --safe --without-K -i spec/proofs/agda spec/proofs/agda/Scope/Examples.agda
```

This checks the theorem and the positive, rejection and computation examples.
No standard library or differential harness is needed. Generated `.agdai`
files are already ignored by the repository. See the local
[proof README](agda/README.md) for a cache-independent check command.


Additional validation performed:

- The `--ignore-interfaces` command above passed, checking all new modules
  from source rather than accepting their cached interfaces.
- `cargo test` passed, including the seven `differential_test` tests and the
  other integration suites. The harness actually invoked Agda; none were
  reported ignored. The separate `cargo test --test differential_test`
  command was not repeated because the full suite already ran that target.
- `cargo fmt --check` failed on pre-existing formatting in
  `tests/differential_test.rs` around lines 330, 357 and 455. That file was
  not modified. Cargo also reported its existing unused `vec_val` warning.
- `git diff --check` passed; local Markdown links in the added proof
  documentation and updated ledger were checked for existing targets.

These regression checks supplement the mechanized proof and do not certify
any additional baseline obligation.
