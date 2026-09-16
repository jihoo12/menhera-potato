module VecNegative2 where

data Bool : Set where
  true  : Bool
  false : Bool

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

data Vec (A : Set) : Nat -> Set where
  nil  : Vec A zero
  cons : (n : Nat) -> A -> Vec A n -> Vec A (suc n)

-- Negative case 2: recursive arg has wrong index (Vec Bool (suc zero) instead of Vec Bool zero)
bad : Vec Bool (suc (suc zero))
bad = cons zero true (cons (suc zero) true nil)
