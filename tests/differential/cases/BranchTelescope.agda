module BranchTelescope where

-- Same field and branch order as rollback_audit_inductive.rs::Tree.
data Nat : Set where
  zero : Nat
  suc : Nat → Nat

data Bool : Set where
  true false : Bool

record Pair (A B : Set) : Set where
  constructor pair
  field
    fst : A
    snd : B
open Pair

data Tree : Set where
  leaf : Tree
  node : Nat → Tree → Bool → Tree → Tree

-- Direct dependent elimination with the evaluator's interleaved convention.
rec : (P : Tree → Set) → P leaf →
      ((n : Nat) (l : Tree) → P l → (b : Bool) (r : Tree) → P r → P (node n l b r)) →
      (t : Tree) → P t
rec P base step leaf = base
rec P base step (node n l b r) = step n l (rec P base step l) b r (rec P base step r)

R = Pair Nat Nat
step : Nat → Tree → R → Bool → Tree → R → R
step n l il true r ir = pair n n
step n l il false r ir = pair (fst il) (snd ir)

two = suc (suc zero)
five = suc (suc (suc (suc (suc zero))))
seven = suc (suc five)
l = node two leaf true leaf
r = node five leaf true leaf

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

-- A1 and A4: normalization observes the two distinct IHs.
a1 : rec (λ _ → R) (pair zero zero) step (node seven l false r) ≡ pair two five
a1 = refl
a4 : rec (λ _ → R) (pair zero zero) step (node seven r false l) ≡ pair five two
a4 = refl

-- B1: genuinely dependent motive, matching the binary Fork fixture.
data Fork : Set where
  tip : Fork
  fork : Fork → Fork → Fork

data Q : Fork → Set where
P : Fork → Set
P t = Q t → Q t

recFork : (M : Fork → Set) → M tip →
          ((l : Fork) → M l → (r : Fork) → M r → M (fork l r)) → (t : Fork) → M t
recFork M base step tip = base
recFork M base step (fork l r) = step l (recFork M base step l) r (recFork M base step r)

bStep : (l : Fork) → P l → (r : Fork) → P r → P (fork l r)
bStep l il r ir = (λ (_ : P l) → (λ x → x)) il

b1 : recFork P (λ x → x) bStep (fork tip tip) ≡ (λ x → x)
b1 = refl
