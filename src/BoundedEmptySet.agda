module BoundedEmptySet where

open import Axioms
open import Logic

-- Bounded empty set (Bes)

∅ : ℝ → Set
∅ x = x ≢ x

Bes : Bound ∅
Bes = exist r₁ (λ x ∅x → ⊥-elim (∅x (refl x)))
