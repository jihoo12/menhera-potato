module BranchSwapChild where
open import BranchTelescope
-- A2: valid function on the wrong telescope, not an arity error.
wrong : Nat → R → Tree → Bool → Tree → R → R
wrong n il l b r ir = step n l il b r ir
bad = rec (λ _ → R) (pair zero zero) wrong (node seven l false r)
