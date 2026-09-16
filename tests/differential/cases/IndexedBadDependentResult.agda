module IndexedBadDependentResult where
open import BranchTelescope using (Bool; Nat)
data Bad : (A : Set) → A → Set₁ where
  bad : (b : Bool) → Bad Nat b
