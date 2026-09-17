{-# OPTIONS --safe --without-K #-}

module Scope.Syntax (Label : Set) where

open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _<_

data _<_ : Nat → Nat → Set where
  z<s : ∀ {n} → zero < suc n
  s<s : ∀ {i n} → i < n → suc i < suc n

-- Raw, extrinsically scoped syntax; labels have no term-variable binders.
data Term : Set where
  var : Nat → Term
  lam : Term → Term
  pi app ann sigma pair : Term → Term → Term
  univ : Label → Term
  fst snd : Term → Term

data Scoped (n : Nat) : Term → Set where
  sc-var : ∀ {i} → i < n → Scoped n (var i)
  sc-lam : ∀ {b} → Scoped (suc n) b → Scoped n (lam b)
  sc-pi : ∀ {a b} → Scoped n a → Scoped (suc n) b → Scoped n (pi a b)
  sc-app : ∀ {f a} → Scoped n f → Scoped n a → Scoped n (app f a)
  sc-univ : ∀ {l} → Scoped n (univ l)
  sc-ann : ∀ {t a} → Scoped n t → Scoped n a → Scoped n (ann t a)
  sc-sigma : ∀ {a b} → Scoped n a → Scoped (suc n) b → Scoped n (sigma a b)
  sc-pair : ∀ {a b} → Scoped n a → Scoped n b → Scoped n (pair a b)
  sc-fst : ∀ {p} → Scoped n p → Scoped n (fst p)
  sc-snd : ∀ {p} → Scoped n p → Scoped n (snd p)
