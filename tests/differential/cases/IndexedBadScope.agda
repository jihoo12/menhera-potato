module IndexedBadScope where
-- First parameter cannot refer to a later index binder.
data Bad (p : i) : (i : Set) → Set₁ where
