module AbsoluteValue where

open import Axioms
open import EqReasoning
open import EqProperties
open import Exp
open import Logic
open import Min
open import Nat
open import Properties


case-abs : (x : ℝ) → (x < r₀) ∨ (x ≥ r₀)
case-abs x = case prf₁ (case prf₂ prf₃) (trichotomy x r₀)

  where
   prf₁ : x > r₀ ∧ ¬ x ≡ r₀ ∧ ¬ x < r₀ → x < r₀ ∨ x ≥ r₀
   prf₁ (x>0 , h) = inj₂ (inj₁ x>0)

   prf₂ : ¬ x > r₀ ∧ x ≡ r₀ ∧ ¬ x < r₀ → x < r₀ ∨ x ≥ r₀
   prf₂ (x≯0 , x=0 , x≮0) = inj₂ (inj₂ x=0)

   prf₃ : ¬ x > r₀ ∧ ¬ x ≡ r₀ ∧ x < r₀ → x < r₀ ∨ x ≥ r₀
   prf₃ (x≯0 , x≠0 , x<0) = inj₁ x<0

-- Definition absolute value

abs : ℝ → ℝ
abs x = case left right (case-abs x)

  where
   left : x < r₀ → ℝ
   left x<0 = - x

   right : x ≥ r₀ → ℝ
   right x≥0 = x

abs-0 : abs r₀ ≡ r₀
abs-0 = case prf₁ prf₂ (case-abs r₀)

  where
   prf₁ : r₀ < r₀ → abs r₀ ≡ r₀
   prf₁ 0<0 = ⊥-elim (<-irrefl 0<0)

   prf₂ : r₀ ≥ r₀ → abs r₀ ≡ r₀
   prf₂ (inj₁ 0>0) = ⊥-elim (>-irrefl 0>0)
   prf₂ (inj₂ 0=0) = {!!}




-- Distance (or metric) between two points.
-- Mathematical Analysis. Apostol, Tom. M. 1974. Pag. 60.

-- dist : ℝ → ℝ → ℝ
-- dist x y = abs (x - y)

-- d-refl : (x y : ℝ)   → (dist x y ≡ r₀) → (x ≡ y)
-- d-refl x y h = {!!}
