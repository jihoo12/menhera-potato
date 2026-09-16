module ResultIndexPositive where

data Empty : Set where

data Nat : Set where
  zero : Nat
  suc : Nat → Nat

data D : Set → Set where
  c : D (Nat → Empty)
