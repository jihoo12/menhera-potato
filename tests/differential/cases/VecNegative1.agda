module VecNegative1 where

data Bool : Set where
  true  : Bool
  false : Bool

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

data Vec (A : Set) : Nat -> Set where
  nil  : Vec A zero
  cons : (n : Nat) -> A -> Vec A n -> Vec A (suc n)

-- Negative case 1: constructing Vec Bool zero with cons (wrong index)
bad : Vec Bool zero
bad = cons zero true nil
