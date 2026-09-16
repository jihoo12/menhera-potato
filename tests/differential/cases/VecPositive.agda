module VecPositive where

data Bool : Set where
  true  : Bool
  false : Bool

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

data Vec (A : Set) : Nat -> Set where
  nil  : Vec A zero
  cons : (n : Nat) -> A -> Vec A n -> Vec A (suc n)

data _≡_ {A : Set} (x : A) : A -> Set where
  refl : x ≡ x

-- Nil type checks
nilBool : Vec Bool zero
nilBool = nil

-- Cons type checks: Vec Bool (suc zero)
oneBool : Vec Bool (suc zero)
oneBool = cons zero true nil

-- Cons type checks: Vec Bool (suc (suc zero))
twoBool : Vec Bool (suc (suc zero))
twoBool = cons (suc zero) false oneBool

-- Head function
head : {A : Set} {n : Nat} -> Vec A (suc n) -> A
head (cons _ a _) = a

-- head oneBool = true (definitionally)
testHead : head oneBool ≡ true
testHead = refl

-- head twoBool = false (definitionally)
testHead2 : head twoBool ≡ false
testHead2 = refl
