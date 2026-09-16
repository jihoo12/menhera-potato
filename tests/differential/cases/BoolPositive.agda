module BoolPositive where

-- Boolean type
data Bool : Set where
  true  : Bool
  false : Bool

-- Identity / propositional equality
data _≡_ {A : Set} (x : A) : A -> Set where
  refl : x ≡ x

-- Case analysis / elimination for Bool
boolCase : (P : Bool -> Set) -> P true -> P false -> (b : Bool) -> P b
boolCase P t f true = t
boolCase P t f false = f

-- negation via case
not : Bool -> Bool
not b = boolCase (\ _ -> Bool) false true b

-- not is involutive
testNotTrue : not true ≡ false
testNotTrue = refl

testNotFalse : not false ≡ true
testNotFalse = refl

-- not . not is identity
testNotInvolutive : (b : Bool) -> not (not b) ≡ b
testNotInvolutive true = refl
testNotInvolutive false = refl
