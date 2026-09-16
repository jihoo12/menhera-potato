module NatNegative4 where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

natRec : (P : Nat -> Set) -> P zero -> ((n : Nat) -> P n -> P (suc n)) -> (n : Nat) -> P n
natRec P z s zero = z
natRec P z s (suc n) = s n (natRec P z s n)

-- Negative case 4: target is Set instead of Nat
bad : Nat
bad = natRec (\ _ -> Nat) zero (\ _ ih -> suc ih) Set
