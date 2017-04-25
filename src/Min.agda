
module Min where

open import RealNumbersAxioms
open import EqProperties
open import LogicDefinitions
open import Properties
open import ClassicLogic

≤-∨-not : (x y : ℝ) → (x ≤ y) ∨ (¬ (x ≤ y))
≤-∨-not x y = pem

-- Minimum Between Two Reales.

min : ℝ → ℝ → ℝ
min x y = case (λ _ → x) (λ _ → y) ( ≤-∨-not x y )

minxy-l : (x y : ℝ) → x ≤ y → min x y ≡ x
minxy-l x y x≤y with ≤-∨-not x y
... | inj₁ p = refl x
... | inj₂ p = ⊥-elim (p x≤y)

minxy-r : (x y : ℝ) → x ≥ y → min x y ≡ y
minxy-r x y x≥y with ≤-∨-not x y
... | inj₁ p = case (λ h →
               case (λ h' → ⊥-elim (>-asym h' h)) (λ h₁ → h₁) (x≥y) )
               (λ h → h)
               (p)
... | inj₂ p = refl y
