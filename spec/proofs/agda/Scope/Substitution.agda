{-# OPTIONS --safe --without-K #-}

module Scope.Substitution (Label : Set) where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Scope.Syntax Label
open import Scope.Renaming Label using (weaken; weaken-scoped)

Substitution : Set
Substitution = Nat → Term

SubstScoped : Nat → Nat → Substitution → Set
SubstScoped n m σ = ∀ {i} → i < n → Scoped m (σ i)

liftSubst : Substitution → Substitution
liftSubst σ zero = var zero
liftSubst σ (suc i) = weaken (σ i)

liftSubst-scoped : ∀ {n m σ} → SubstScoped n m σ →
                   SubstScoped (suc n) (suc m) (liftSubst σ)
liftSubst-scoped h z<s = sc-var z<s
liftSubst-scoped h (s<s p) = weaken-scoped (h p)

subst : Substitution → Term → Term
subst σ (var i) = σ i
subst σ (lam b) = lam (subst (liftSubst σ) b)
subst σ (pi a b) = pi (subst σ a) (subst (liftSubst σ) b)
subst σ (app f a) = app (subst σ f) (subst σ a)
subst σ (univ l) = univ l
subst σ (ann t a) = ann (subst σ t) (subst σ a)
subst σ (sigma a b) = sigma (subst σ a) (subst (liftSubst σ) b)
subst σ (pair a b) = pair (subst σ a) (subst σ b)
subst σ (fst p) = fst (subst σ p)
subst σ (snd p) = snd (subst σ p)

subst-scoped : ∀ {n m σ t} → SubstScoped n m σ → Scoped n t → Scoped m (subst σ t)
subst-scoped h (sc-var p) = h p
subst-scoped h (sc-lam b) = sc-lam (subst-scoped (liftSubst-scoped h) b)
subst-scoped h (sc-pi a b) = sc-pi (subst-scoped h a) (subst-scoped (liftSubst-scoped h) b)
subst-scoped h (sc-app f a) = sc-app (subst-scoped h f) (subst-scoped h a)
subst-scoped h sc-univ = sc-univ
subst-scoped h (sc-ann t a) = sc-ann (subst-scoped h t) (subst-scoped h a)
subst-scoped h (sc-sigma a b) = sc-sigma (subst-scoped h a) (subst-scoped (liftSubst-scoped h) b)
subst-scoped h (sc-pair a b) = sc-pair (subst-scoped h a) (subst-scoped h b)
subst-scoped h (sc-fst p) = sc-fst (subst-scoped h p)
subst-scoped h (sc-snd p) = sc-snd (subst-scoped h p)
