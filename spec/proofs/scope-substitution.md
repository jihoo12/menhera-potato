# SCOPE fragment: ordinary-term simultaneous substitution

## Specification stage

Starting baseline: commit `5321136cc8cfd9901aa1ade08afe774e0b0d2fb3`.
This milestone formalizes a scope consequence of the existing
[canonical specification](../formal_system.md); it changes no canonical rule
or production Rust behavior. Only the ten constructors already present in
[Scope.Syntax](agda/Scope/Syntax.agda) are covered.

Theorem selected before mechanization (now checked): for every `Label : Set`, natural
source/target depths n and m, substitution σ : Nat → Term, and raw term t,
if `(∀ {i} → i < n → Scoped m (σ i))` and `Scoped n t`, then
`Scoped m (subst σ t)`. `Scoped` is the existing independent inductive
scope predicate; it does not mean that a type checker accepts the term.

Define `Substitution = Nat → Term` and name the bound-respecting hypothesis
`SubstScoped n m σ`. Values outside source scope are unconstrained. At a
variable, substitution returns σ(i) directly, without recursively substituting
inside the replacement: this is simultaneous, not iterated substitution.

Binder lifting is:

```
liftSubst σ zero    = var zero
liftSubst σ (suc i) = weaken (σ i)
```

Lam bodies and Pi/Sigma codomains use the lifted substitution. Pi/Sigma
domains and both children of App, Pair and Ann use the original substitution;
Fst/Snd recurse on their sole child; Univ preserves its label. Lifting adds
one newest entry in both source and target contexts. Weakening shifts free
indices of replacement terms while preserving their own bound indices.

Required examples: replacing an open variable by a closed term; lifting
under one and two binders; preservation of the new variable; weakening an
open replacement including one with an internal binder; Pi/Sigma domains
versus codomains; Pair/Ann introducing no binders; rejection of a substitution
whose in-scope image escapes the target depth. These are scope/computation
examples, not object-language typing assertions.

## Proof stage

Status: **Proved (mechanized)**, syntactic scope preservation only.
[Scope.Substitution](agda/Scope/Substitution.agda) supplies:

```agda
subst-scoped : ∀ {n m σ t} → SubstScoped n m σ → Scoped n t → Scoped m (subst σ t)
```

The proof is structural induction on `Scoped n t`, generalized over target
depth and substitution. The helper `liftSubst-scoped` splits on the bound
witness: `z<s` maps to `sc-var z<s`; for `s<s p`, the premise supplies
`Scoped m (σ i)` and `weaken-scoped` gives scope at `suc m`.

All induction cases are discharged:

- Var returns the substitution premise applied to the index-bound witness.
- Lam applies the induction hypothesis to the body using `liftSubst-scoped`.
- Pi/Sigma apply it to the domain with the original premise and to the
  codomain with the lifted premise.
- App/Ann/Pair apply it independently to both children with the original
  premise. In particular, Pair's dependency in typing introduces no syntax
  binder, and Ann's erased annotation still participates in raw scope.
- Fst/Snd apply it to the sole child.
- Univ rebuilds `sc-univ` with its original label.

The operation recurses on strict subterms; the proof recurses on strict
scope subderivations. Replacement terms are not recursive inputs to `subst`.
Agda checked termination, coverage and positivity without overrides.

### Dependencies and assumptions

The existing [renaming proof](scope-renaming.md) supplies
[weaken-scoped](agda/Scope/Renaming.agda): `Scoped m u` implies
`Scoped (suc m) (weaken u)`, with `weaken = rename suc`. This is the only
additional scope theorem needed for lifting. It depends on `rename-scoped`
and `lift-scoped`; all dependencies were rechecked in this run. There are
no unresolved mathematical dependencies for this fragment.

The theorem is parametric in `Label : Set`, unchanged by substitution.
Contexts are only natural-number lengths, indices are unbounded naturals,
and syntax consists of finite raw trees. The quantified scope hypotheses
are the complete preconditions; neither well-typed contexts nor well-typed
substitution images are assumed. No equality on substitutions or function
extensionality is needed. The theorem imports builtin naturals and the two
existing local modules; examples also use builtin equality. All modules
retain `--safe --without-K`, with no postulates, holes, unsolved metas or
unsafe pragmas. Trust remains Agda 2.8.0 and its builtin definitions/checker,
not Rust acceptance or agreement with differential examples.

## Specification correspondence and implementation stage

| Canonical section | Mathematical definition/proof |
|---|---|
| §0 capture-avoiding substitution notation | `Substitution`, simultaneous `subst`; no runtime-equivalence claim |
| §1.2 ten ordinary constructors | exhaustive clauses of `subst` and `subst-scoped` |
| §3.1 context extension, §3.2 Var, §7 relative indices | `SubstScoped`, zero/successor cases of `liftSubst-scoped` |
| §1.2, §3.2 Pi/Sigma, §3.3 Lam | `liftSubst` under exactly bodies/codomains |
| §1.1 universe expressions | opaque unchanged labels; no level theorem |

The canonical specification and `Scope.Syntax` remain unchanged. Index zero
is the newest binder; older entries have successor indices. These are not
absolute neutral levels and not universe levels. Each Agda constructor maps
to its same-named canonical constructor, preserving child order.

Implementation status: the mathematical operation and proof are implemented
in Agda only. No Rust function is added or certified. The canonical §0/§4.7
implementation uses environments and closure instantiation; correspondence
between it and `subst` is still unproved. Arena validity, finite unfolding,
machine bounds, overflow and resource behavior remain REFINE work. Existing
ordinary terms retain their representation and behavior. This proof does
not authorize a semantic change to the kernel.

## Validation

Agda **2.8.0** checked the complete import graph from source successfully:

```sh
agda --ignore-interfaces --no-libraries --safe --without-K -i spec/proofs/agda spec/proofs/agda/Scope/Examples.agda
```

[Examples.agda](agda/Scope/Examples.agda) retains the renaming examples and
adds computation equalities for closed replacement, one/two surrounding
binders, fixed new variables, replacements containing their own binder,
Pi/Sigma domain versus codomain substitution, Pair/Ann without lifting,
and projections. `subst-open-to-closed-scoped` and
`subst-under-binder-scoped` instantiate the main theorem. The two rejection
proofs show the target-depth premise is necessary, using the existing
empty datatype rather than intentionally uncompilable modules.

For example, with σ(i) = App (Var 0) (Univ 0), substituting into
Lam (App (Var 1) (Var 0)) yields
Lam (App (App (Var 1) (Univ 0)) (Var 0)). This checked equality fails if
the outer replacement is not weakened or the new Var 0 is substituted.
These are definitional computations of the mathematical substitution,
not β-reduction or object-language conversion proofs.

## Remaining work and smallest next theorem

Overall **SCOPE remains Open**. This result establishes no substitution
preservation of typing, environment well-formedness, inductive declaration
or constructor-telescope scope, signature/body permutation, NbE, semantic
value relation, conversion, level normalization, quotation scope or Rust
refinement. It also establishes no global soundness, normalization,
canonicity or consistency result.

The smallest natural next lemma is the single-variable instantiation
corollary: if `Scoped (suc n) b` and `Scoped n a`, then substituting with
σ(0) = a and σ(suc i) = Var i yields a term scoped at n. Its substitution
premise follows by zero/successor cases, so it directly reuses `subst-scoped`.
This would connect the simultaneous operation to the binder-removing
notation used in §0 and §3.2 without asserting β-preservation or runtime
closure correctness. Substitution identity/composition laws can follow
as separate milestones.

## Repository validation results

- `cargo test`: passed all 133 tests, with none failed or ignored. This
  included the seven `differential_test` cases and other Agda comparisons;
  Agda was actually invoked. No separate repeat of the differential target
  was needed for this proof-only change.
- `cargo fmt --check`: failed only on pre-existing formatting in unchanged
  `tests/differential_test.rs` around lines 330, 357 and 455. No unrelated
  formatting edits were made. Cargo also reported the existing unused
  `vec_val` warning in that file.
- `git diff --check`: passed. Local Markdown link targets and whitespace
  in the new proof files were checked. Production Rust, canonical syntax
  and rules, and the existing renaming theorem are unchanged.

These checks supplement the Agda proof and establish no additional kernel
metatheory. No checks were skipped due to unavailable tools.
