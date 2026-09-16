module NatNegative1 where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

-- Negative case 1: suc applied to a universe (Set) instead of Nat
bad : Nat
bad = suc Set
