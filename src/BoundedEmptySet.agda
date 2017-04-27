
module BoundedEmptySet where

open import LogicDefinitions
open import RealNumbersAxioms

-- Bounded empty set (Bes)

∅ : ℝ → Set
∅ x = x ≢ x

Bes : Bound ∅
Bes = exist r₁ (λ x ∅x → ⊥-elim (∅x (refl x)))
