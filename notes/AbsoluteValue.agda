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

abs≥x : (x : ℝ) → abs x ≥ x
abs≥x x with case-abs x
... | inj₁ p = inj₁ (>-+-cancel-r  (p₁-helper (>-*-cancel-l (>-inve-r₀ (>-trans 2>1 1>0)) (p₂-helper (p₃-helper p))) ))

  where
   p₁-helper : r₀ > (ℕ2ℝ 2 * x) → - x + x > x + x
   p₁-helper 0>2 = subst₂ (λ t₁ t₂ → t₁ > t₂) (≡-sym p₁₁-helper) 2x=x+x 0>2

    where
     p₁₁-helper : - x + x ≡ r₀
     p₁₁-helper =
         - x + x ≡⟨ +-comm (- x) x ⟩
          x - x  ≡⟨ +-inve x ⟩
          r₀     ∎

   p₂-helper : r₀ > (ℕ2ℝ 2 ⁻¹ * ℕ2ℝ 2) * x → ℕ2ℝ 2 ⁻¹ * r₀ > ℕ2ℝ 2 ⁻¹ * (ℕ2ℝ 2 * x)
   p₂-helper h = subst₂ (λ t₁ t₂ → t₁ > t₂) (≡-sym p₂₂-helper) (*-asso (ℕ2ℝ 2 ⁻¹) (ℕ2ℝ 2) x) h

     where
      p₂₂-helper : ℕ2ℝ 2 ⁻¹ * r₀ ≡ r₀
      p₂₂-helper =
          ℕ2ℝ 2 ⁻¹ * r₀ ≡⟨ *-comm (ℕ2ℝ 2 ⁻¹) r₀ ⟩
          r₀ * ℕ2ℝ 2 ⁻¹ ≡⟨ *-left-zero ⟩
          r₀             ∎
   p₃-helper : r₀ > x → r₀ > (ℕ2ℝ 2 ⁻¹ * ℕ2ℝ 2) * x
   p₃-helper 0>x = subst₂ (λ t₁ t₂ → t₁ > t₂) (refl r₀) (≡-sym p₃₃-helper) 0>x

     where
      p₃₃-helper : ℕ2ℝ 2 ⁻¹ * ℕ2ℝ 2 * x ≡ x
      p₃₃-helper =
          (ℕ2ℝ 2 ⁻¹ * ℕ2ℝ 2) * x ≡⟨ subst (λ w → (ℕ2ℝ 2 ⁻¹ * ℕ2ℝ 2) * x ≡ w * x) (*-comm (ℕ2ℝ 2 ⁻¹)
                                            (ℕ2ℝ 2)) (refl ((ℕ2ℝ 2 ⁻¹ * ℕ2ℝ 2) * x)) ⟩
          (ℕ2ℝ 2 * ℕ2ℝ 2 ⁻¹) * x ≡⟨ subst (λ w → (ℕ2ℝ 2 * ℕ2ℝ 2 ⁻¹) * x ≡ w * x) (*-inve (ℕ2ℝ 2) 2≢0)
                                            (refl ((ℕ2ℝ 2 * ℕ2ℝ 2 ⁻¹) * x)) ⟩
          r₁ * x ≡⟨ *-comm r₁ x ⟩
          x * r₁ ≡⟨ *-neut x ⟩
          x             ∎

... | inj₂ p = inj₂ (refl x)
