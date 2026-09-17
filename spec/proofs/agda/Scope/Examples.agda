{-# OPTIONS --safe --without-K #-}

module Scope.Examples where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
-- Nat labels suffice for examples; the theorem is polymorphic in labels.
open import Scope.Syntax Nat
open import Scope.Renaming Nat

data Empty : Set where

closed-identity : Scoped zero (lam (var zero))
closed-identity = sc-lam (sc-var z<s)

pi-codomain-binds : Scoped zero (pi (univ zero) (var zero))
pi-codomain-binds = sc-pi sc-univ (sc-var z<s)

sigma-codomain-binds : Scoped zero (sigma (univ zero) (var zero))
sigma-codomain-binds = sc-sigma sc-univ (sc-var z<s)

no-closed-variable : Scoped zero (var zero) → Empty
no-closed-variable (sc-var ())

no-escaping-variable : Scoped zero (lam (var (suc zero))) → Empty
no-escaping-variable (sc-lam (sc-var (s<s ())))

pi-domain-does-not-bind : Scoped zero (pi (var zero) (univ zero)) → Empty
pi-domain-does-not-bind (sc-pi (sc-var ()) b)

sigma-domain-does-not-bind : Scoped zero (sigma (var zero) (univ zero)) → Empty
sigma-domain-does-not-bind (sc-sigma (sc-var ()) b)

pair-does-not-bind : Scoped zero (pair (univ zero) (var zero)) → Empty
pair-does-not-bind (sc-pair a (sc-var ()))

annotation-is-scoped : Scoped zero (ann (univ zero) (var zero)) → Empty
annotation-is-scoped (sc-ann t (sc-var ()))

weakening-under-binder :
  weaken (lam (app (var 1) (var 0))) ≡ lam (app (var 2) (var 0))
weakening-under-binder = refl

weakened-open-term : Scoped 2 (weaken (lam (app (var 1) (var 0))))
weakened-open-term = weaken-scoped (sc-lam (sc-app (sc-var (s<s z<s)) (sc-var z<s)))

weakening-under-two-binders :
  weaken (lam (lam (app (var 2) (var 1)))) ≡ lam (lam (app (var 3) (var 1)))
weakening-under-two-binders = refl

open import Scope.Substitution Nat

-- Closed replacement; all source indices map to the same closed raw term.
closedSubst : Substitution
closedSubst i = lam (var 0)

closedSubst-scoped : SubstScoped 1 0 closedSubst
closedSubst-scoped p = closed-identity

subst-open-to-closed : subst closedSubst (var 0) ≡ lam (var 0)
subst-open-to-closed = refl

subst-open-to-closed-scoped : Scoped 0 (subst closedSubst (var 0))
subst-open-to-closed-scoped = subst-scoped closedSubst-scoped (sc-var z<s)

-- A non-variable replacement with a free variable at target depth 1.
openSubst : Substitution
openSubst i = app (var 0) (univ 0)

openSubst-scoped : SubstScoped 1 1 openSubst
openSubst-scoped p = sc-app (sc-var z<s) sc-univ

subst-under-binder :
  subst openSubst (lam (app (var 1) (var 0))) ≡
  lam (app (app (var 1) (univ 0)) (var 0))
subst-under-binder = refl

subst-under-binder-scoped :
  Scoped 1 (subst openSubst (lam (app (var 1) (var 0))))
subst-under-binder-scoped =
  subst-scoped openSubst-scoped (sc-lam (sc-app (sc-var (s<s z<s)) (sc-var z<s)))

subst-under-two-binders :
  subst openSubst (lam (lam (pair (var 2) (pair (var 1) (var 0))))) ≡
  lam (lam (pair (app (var 2) (univ 0)) (pair (var 1) (var 0))))
subst-under-two-binders = refl

subst-fixes-new-variable : ∀ (σ : Substitution) → subst σ (lam (var 0)) ≡ lam (var 0)
subst-fixes-new-variable σ = refl

-- Weakening a replacement must also respect binders inside that replacement.
subst-replacement-with-binder :
  subst (λ i → lam (app (var 1) (var 0))) (lam (var 1)) ≡
  lam (lam (app (var 2) (var 0)))
subst-replacement-with-binder = refl

subst-pi :
  subst openSubst (pi (var 0) (pair (var 1) (var 0))) ≡
  pi (app (var 0) (univ 0)) (pair (app (var 1) (univ 0)) (var 0))
subst-pi = refl

subst-sigma :
  subst openSubst (sigma (var 0) (pair (var 1) (var 0))) ≡
  sigma (app (var 0) (univ 0)) (pair (app (var 1) (univ 0)) (var 0))
subst-sigma = refl

subst-pair-ann-no-binders :
  subst openSubst (pair (var 0) (ann (var 0) (var 0))) ≡
  pair (app (var 0) (univ 0)) (ann (app (var 0) (univ 0)) (app (var 0) (univ 0)))
subst-pair-ann-no-binders = refl

subst-projections :
  subst openSubst (pair (fst (var 0)) (snd (var 0))) ≡
  pair (fst (app (var 0) (univ 0))) (snd (app (var 0) (univ 0)))
subst-projections = refl

-- The bound-respecting premise cannot be dropped.
reject-escaping-substitution : SubstScoped 1 0 (λ i → var 0) → Empty
reject-escaping-substitution h = no-closed-variable (h z<s)

reject-escaping-result : Scoped 0 (subst (λ i → var 0) (var 0)) → Empty
reject-escaping-result = no-closed-variable
