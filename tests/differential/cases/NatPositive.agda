module NatPositive where

-- Natural numbers type
data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

-- Identity / propositional equality
data _≡_ {A : Set} (x : A) : A -> Set where
  refl : x ≡ x

-- Dependent recursor / induction principle
natRec : (P : Nat -> Set) -> P zero -> ((n : Nat) -> P n -> P (suc n)) -> (n : Nat) -> P n
natRec P z s zero = z
natRec P z s (suc n) = s n (natRec P z s n)

-- Addition defined via natRec
add : Nat -> Nat -> Nat
add m n = natRec (\ _ -> Nat) n (\ _ ih -> suc ih) m

-- Computations
two : Nat
two = suc (suc zero)

three : Nat
three = suc (suc (suc zero))

five : Nat
five = suc (suc (suc (suc (suc zero))))

testAdd : add two three ≡ five
testAdd = refl

-- Identity on zero: 0 + 5 ≡ 5 (definitionally)
testAddZero : add zero five ≡ five
testAddZero = refl

-- Higher-order dependent recursion
-- Motive P(n) = Nat -> Nat
addDep : (n : Nat) -> Nat -> Nat
addDep n = natRec (\ _ -> Nat -> Nat) (\ x -> x) (\ _ ih x -> suc (ih x)) n

seven : Nat
seven = suc (suc (suc (suc (suc (suc (suc zero))))))

testAddDep : addDep three (suc (suc (suc (suc zero)))) ≡ seven
testAddDep = refl
