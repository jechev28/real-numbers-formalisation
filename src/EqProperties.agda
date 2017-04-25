
module EqProperties where

open import RealNumbersAxioms

subst : (P : ℝ → Set) → {x y : ℝ} → x ≡ y → P x → P y
subst P (refl x) Px = Px

subst₂ : (P : ℝ → ℝ → Set) → {x₁ x₂ y₁ y₂ : ℝ} → x₁ ≡ x₂ → y₁ ≡ y₂ → P x₁ y₁ → P x₂ y₂
subst₂ P (refl x) (refl y) h = h

≡-sym : {x y : ℝ} → x ≡ y → y ≡ x
≡-sym (refl x) = refl x

≡-trans : {x y z : ℝ} → x ≡ y → y ≡ z → x ≡ z
≡-trans (refl z) (refl .z) = refl z
