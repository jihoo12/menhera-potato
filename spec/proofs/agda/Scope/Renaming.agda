{-# OPTIONS --safe --without-K #-}

module Scope.Renaming (Label : Set) where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Scope.Syntax Label

Renaming : Set
Renaming = Nat → Nat

MapsInto : Nat → Nat → Renaming → Set
MapsInto n m ρ = ∀ {i} → i < n → ρ i < m

lift : Renaming → Renaming
lift ρ zero = zero
lift ρ (suc i) = suc (ρ i)

lift-scoped : ∀ {n m ρ} → MapsInto n m ρ → MapsInto (suc n) (suc m) (lift ρ)
lift-scoped h z<s = z<s
lift-scoped h (s<s p) = s<s (h p)

rename : Renaming → Term → Term
rename ρ (var i) = var (ρ i)
rename ρ (lam b) = lam (rename (lift ρ) b)
rename ρ (pi a b) = pi (rename ρ a) (rename (lift ρ) b)
rename ρ (app f a) = app (rename ρ f) (rename ρ a)
rename ρ (univ l) = univ l
rename ρ (ann t a) = ann (rename ρ t) (rename ρ a)
rename ρ (sigma a b) = sigma (rename ρ a) (rename (lift ρ) b)
rename ρ (pair a b) = pair (rename ρ a) (rename ρ b)
rename ρ (fst p) = fst (rename ρ p)
rename ρ (snd p) = snd (rename ρ p)

rename-scoped : ∀ {n m ρ t} → MapsInto n m ρ → Scoped n t → Scoped m (rename ρ t)
rename-scoped h (sc-var p) = sc-var (h p)
rename-scoped h (sc-lam b) = sc-lam (rename-scoped (lift-scoped h) b)
rename-scoped h (sc-pi a b) = sc-pi (rename-scoped h a) (rename-scoped (lift-scoped h) b)
rename-scoped h (sc-app f a) = sc-app (rename-scoped h f) (rename-scoped h a)
rename-scoped h sc-univ = sc-univ
rename-scoped h (sc-ann t a) = sc-ann (rename-scoped h t) (rename-scoped h a)
rename-scoped h (sc-sigma a b) = sc-sigma (rename-scoped h a) (rename-scoped (lift-scoped h) b)
rename-scoped h (sc-pair a b) = sc-pair (rename-scoped h a) (rename-scoped h b)
rename-scoped h (sc-fst p) = sc-fst (rename-scoped h p)
rename-scoped h (sc-snd p) = sc-snd (rename-scoped h p)

weaken : Term → Term
weaken = rename suc

weaken-scoped : ∀ {n t} → Scoped n t → Scoped (suc n) (weaken t)
weaken-scoped = rename-scoped (λ p → s<s p)
