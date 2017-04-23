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
case-abs x with trichotomy x r₀
... | inj₁ (x>0 , _)              = inj₂ (inj₁ x>0)
... | inj₂ (inj₁ (_ , x≡0 , _))   = inj₂ (inj₂ x≡0)
... | inj₂ (inj₂ (x₁ , x₂ , x<0)) = inj₁ x<0

-- Definition absolute value

abs : ℝ → ℝ
abs x with case-abs x
... | inj₁ _ = - x
... | inj₂ _ = x

-- Properties of the absolute value.

abs-0 : abs r₀ ≡ r₀
abs-0 with case-abs r₀
abs-0 | inj₁ 0<0 = ⊥-elim (<-irrefl 0<0)
abs-0 | inj₂ h = refl r₀

x>0→absx=x : (x : ℝ) → x > r₀ → abs x ≡ x
x>0→absx=x x x>0 with case-abs x
... | inj₁ p = ⊥-elim (≥→≮ (inj₁ x>0) p)
... | inj₂ p = refl x

x<0→absx=-x : (x : ℝ) → x < r₀ → abs x ≡ - x
x<0→absx=-x x x<0 with case-abs x
... | inj₁ p = refl (- x)
... | inj₂ p = ⊥-elim (≥→≮ p x<0)

abs-minus : (x : ℝ) → abs (- x) ≡ abs x
abs-minus x with case-abs (- x)
... | inj₁ p = ≡-sym (p-helper p)

  where
   p-helper : - x < r₀ → abs x ≡ - (- x)
   p-helper -x<0 =
     abs x   ≡⟨ x>0→absx=x x (-x<0→x>0 x -x<0) ⟩
     x       ≡⟨ ≡-sym mul--x ⟩
     - (- x) ∎

... | inj₂ p = case prf1 prf2 p

  where
   prf1 : - x > r₀ → - x ≡ abs x
   prf1 -x>0 = ≡-sym (x<0→absx=-x x (-x>0→x<0 -x>0))

   prf2 : - x ≡ r₀ → - x ≡ abs x
   prf2 -x=0 =
     - x       ≡⟨ -x=0 ⟩
     r₀        ≡⟨ ≡-sym abs-0 ⟩
     abs r₀    ≡⟨ subst ((λ w → abs r₀ ≡ abs w)) (≡-sym (-x=0→x=0 x -x=0)) (refl (abs r₀)) ⟩
     abs x     ∎
