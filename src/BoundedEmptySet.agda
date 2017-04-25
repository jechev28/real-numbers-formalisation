
module BoundedEmptySet where

open import RealNumbersAxioms
open import LogicDefinitions

-- Bounded empty set (Bes)

∅ : ℝ → Set
∅ x = x ≢ x

Bes : Bound ∅
Bes = exist r₁ (λ x ∅x → ⊥-elim (∅x (refl x)))
