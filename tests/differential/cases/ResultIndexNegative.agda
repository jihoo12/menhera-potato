module ResultIndexNegative where

data Empty : Set where

data D : Set → Set where
  c : D (D Empty → Empty)
