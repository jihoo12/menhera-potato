module IndexedScopes where
open import BranchTelescope using (Bool; true; false; Nat; zero; suc; _≡_; refl)

data Tagged (A : Set) : Bool → Set where
  tag : (b : Bool) → A → Tagged A b

tagged : Tagged Nat true
tagged = tag true zero

observe : {A : Set} {b : Bool} → Tagged A b → Nat
observe (tag b a) = zero
observe-test : observe tagged ≡ zero
observe-test = refl

-- The index type sees the earlier parameter.
data Empty (A : Set) : A → Set where

-- Two dependent parameters, followed by two dependent indices.
data Rel (A : Set) (a : A) : (B : Set) → B → Set₁ where
  mk : (b : A) → Rel A a A b
rel : Rel Bool true Bool false
rel = mk false

-- Index 2's type is instantiated with result index 1, not its TYPE.
data Witness : (A : Set) → A → Set₁ where
  witness : (b : Bool) → Witness Bool b
w : Witness Bool false
w = witness false

data Chain : Nat → Set where
  base : Chain zero
  link : (n : Nat) → Chain n → Chain (suc n)

fold : {n : Nat} → Chain n → Nat
fold base = zero
fold (link n child) = suc (fold child)
fold-test : fold (link (suc zero) (link zero base)) ≡ suc (suc zero)
fold-test = refl
