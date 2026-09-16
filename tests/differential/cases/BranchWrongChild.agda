module BranchWrongChild where
open import BranchTelescope
-- B2: left IH cannot be used at P(right), even though the outer result is identity.
wrong : (l : Fork) → P l → (r : Fork) → P r → P (fork l r)
wrong l il r ir = (λ (_ : P r) → (λ x → x)) il
bad = recFork P (λ x → x) wrong (fork tip tip)
