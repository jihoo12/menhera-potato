module IndexedBadMotive where
open import BranchTelescope using (Nat; zero)
open import IndexedScopes using (Chain)
-- A motive on one fiber is not a motive uniformly over all indices.
wrong : (Chain zero → Set) → {n : Nat} → Chain n → Set
wrong f t = f t
