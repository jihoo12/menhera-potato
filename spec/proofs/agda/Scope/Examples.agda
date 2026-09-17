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
