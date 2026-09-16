module BoolIdxNegative1 where

data Bool : Set where
  true  : Bool
  false : Bool

data BoolIdx : Bool -> Set where
  btrue  : BoolIdx true
  bfalse : BoolIdx false

-- Negative case: btrue used at wrong index (BoolIdx false instead of BoolIdx true)
bad : BoolIdx false
bad = btrue
