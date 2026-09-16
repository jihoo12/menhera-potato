module BoolIdxPositive where

data Bool : Set where
  true  : Bool
  false : Bool

data BoolIdx : Bool -> Set where
  btrue  : BoolIdx true
  bfalse : BoolIdx false

data _≡_ {A : Set} (x : A) : A -> Set where
  refl : x ≡ x

-- BoolIdx true type checks
idxTrue : BoolIdx true
idxTrue = btrue

-- BoolIdx false type checks
idxFalse : BoolIdx false
idxFalse = bfalse
