module NatNegative2 where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

natRec : (P : Nat -> Set) -> P zero -> ((n : Nat) -> P n -> P (suc n)) -> (n : Nat) -> P n
natRec P z s zero = z
natRec P z s (suc n) = s n (natRec P z s n)

-- Negative case 2: base case has type Set instead of P zero (Nat)
bad : Nat
bad = natRec (\ _ -> Nat) Set (\ _ ih -> suc ih) zero
