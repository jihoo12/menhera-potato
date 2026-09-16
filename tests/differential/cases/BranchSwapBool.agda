module BranchSwapBool where
open import BranchTelescope
-- A3: Bool and the neighboring IH are exchanged.
wrong : Nat → Tree → Bool → R → Tree → R → R
wrong n l b il r ir = step n l il b r ir
bad = rec (λ _ → R) (pair zero zero) wrong (node seven l false r)
