module IndexedBadResult where
open import BranchTelescope using (Bool)
data Bad (A : Set) : Bool → Set where
  bad : (b : Bool) (a : A) → Bad A a
