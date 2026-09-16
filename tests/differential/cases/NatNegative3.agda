module NatNegative3 where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

natRec : (P : Nat -> Set) -> P zero -> ((n : Nat) -> P n -> P (suc n)) -> (n : Nat) -> P n
natRec P z s zero = z
natRec P z s (suc n) = s n (natRec P z s n)

-- Negative case 3: step case has wrong return type (zero : Nat instead of P (suc n))
-- when P(n) = Nat -> Nat
bad : (n : Nat) -> Nat -> Nat
bad = natRec (\ _ -> Nat -> Nat) (\ x -> x) (\ _ _ -> zero)
