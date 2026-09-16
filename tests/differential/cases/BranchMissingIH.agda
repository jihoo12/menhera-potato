module BranchMissingIH where
open import BranchTelescope
-- E3: three binders instead of the four required for two recursive fields.
wrong : Fork → Nat → Fork → Nat
wrong l il r = zero
bad = recFork (λ _ → Nat) zero wrong (fork tip tip)
