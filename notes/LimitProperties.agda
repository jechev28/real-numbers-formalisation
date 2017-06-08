module LimitProperties where

open import AbsoluteValueDefinition
open import DistanceDefinition
open import DistanceProperties
open import EqProperties
open import EqReasoning
open import Exp
open import Limit
open import LogicDefinitions
open import Min
open import Nat
open import OrderedFieldProperties
open import RealNumbersAxioms


-- Square root function.

postulate
  sqrt : ℝ → ℝ
  sqrt-inve :  (x : ℝ) → x ≥ r₀ → sqr (sqrt x) ≡ x
  sqrt-pos : (x : ℝ) → x > r₀ → sqrt x > r₀

postulate
    dis-produc : (x y z w : ℝ) → dist (x * z) (y * w) ≡ dist x y * dist z w
    trans-<-* : {x y z w : ℝ} → x ≥ r₀ → y > r₀ → z ≥ r₀ → w > r₀ → x < y → z < w → x * z < y * w

-- The limit of a product is the product of the limits.

*-lim : (a L₁ L₂ : ℝ) → (f₁ f₂ : ℝ → ℝ) → lim f₁ a L₁ → lim f₂ a L₂ → lim (λ x → f₁ x * f₂ x) a (L₁ * L₂)
*-lim a L₁ L₂ f₁ f₂ h1 h2 ε ε>0 = a₁-helper (h1 (sqrt ε) (sqrt-pos ε ε>0)) (h2 (sqrt ε) (sqrt-pos ε ε>0))

-- Choose δ = min {δ₁, δ₂}

  where
   a₁-helper : ∃ᵣ (λ δ → δ > r₀ → (x : ℝ) → dist x a < δ → dist (f₁ x) L₁ < sqrt ε) →
    ∃ᵣ (λ δ → δ > r₀ → (x : ℝ) → dist x a < δ → dist (f₂ x) L₂ < sqrt ε) → ∃ᵣ (λ δ → δ > r₀ → (x : ℝ) →
    dist x a < δ → dist (f₁ x * f₂ x) (L₁ * L₂) < ε)
   a₁-helper (exist δ₁ l₁) (exist δ₂ l₂) = exist (min δ₁ δ₂) a₂-helper

    where
     a₂-helper : min δ₁ δ₂ > r₀ → (x : ℝ) → dist x a < min δ₁ δ₂ → dist (f₁ x * f₂ x) (L₁ * L₂) < ε
     a₂-helper δ>0 x h3 = ≤-<-trans (inj₂ (dis-produc (f₁ x) L₁ (f₂ x) L₂))
                          (a₃-helper (trans-<-* (d-pos (f₁ x) L₁) (sqrt-pos ε ε>0)
                          (d-pos (f₂ x) L₂) (sqrt-pos ε ε>0) (l₁ (case arf1 arf2 (≤-∨ δ₁ δ₂)) x
                          (case arf3 arf4 (≤-∨ δ₁ δ₂))) (l₂ (case arf5 arf6 (≤-∨ δ₁ δ₂)) x
                          (case arf7 arf8 (≤-∨ δ₁ δ₂)))))

      where
       a₃-helper : dist (f₁ x) L₁ * dist (f₂ x) L₂ < sqrt ε * sqrt ε → dist (f₁ x) L₁ * dist (f₂ x) L₂ < ε
       a₃-helper h4 = subst₂ (λ t₁ t₂ → t₁ < t₂) (refl (dist (f₁ x) L₁ * dist (f₂ x) L₂)) (sqrt-inve ε (inj₁ ε>0)) h4


       arf1 : δ₁ ≤ δ₂ → δ₁ > r₀
       arf1 h5 = >-≡→>-1 δ>0 (minxy-l δ₁ δ₂ h5)

       arf2 : δ₂ ≤ δ₁ → δ₁ > r₀
       arf2 h6 = ≥->-trans (≤-to-≥ h6) (>-≡→>-1 δ>0 (minxy-r δ₁ δ₂ (≤-to-≥ h6)))

       arf3 : δ₁ ≤ δ₂ → dist x a < δ₁
       arf3 h7 = <-≡→< h3 (minxy-l δ₁ δ₂ h7)

       arf4 : δ₂ ≤ δ₁ → dist x a < δ₁
       arf4 h8 = case arf41 arf42 h8

        where
         arf41 : δ₂ < δ₁ → dist x a < δ₁
         arf41 δ₂<δ₁ = <-trans (<-≡→< h3 (minxy-r δ₁ δ₂ (inj₁ δ₂<δ₁))) δ₂<δ₁

         arf42 : δ₂ ≡ δ₁ → dist x a < δ₁
         arf42 δ₂≡δ₁ = <-≡→< h3 (minxy-l δ₁ δ₂ (inj₂ (≡-sym δ₂≡δ₁)))

       arf5 : δ₁ ≤ δ₂ → δ₂ > r₀
       arf5 h9 = ≥->-trans (≤-to-≥ h9) (>-≡→>-1 δ>0 (minxy-l δ₁ δ₂ h9))

       arf6 : δ₂ ≤ δ₁ → δ₂ > r₀
       arf6 h10 = >-≡→>-1 δ>0 (minxy-r δ₁ δ₂ (≤-to-≥ h10))

       arf7 : δ₁ ≤ δ₂ → dist x a < δ₂
       arf7 h11 = case arf71 arf72 h11

        where
         arf71 : δ₁ < δ₂ → dist x a < δ₂
         arf71 δ₁<δ₂ = <-trans (<-≡→< h3 (minxy-l δ₁ δ₂ h11)) δ₁<δ₂

         arf72 : δ₁ ≡ δ₂ → dist x a < δ₂
         arf72 δ₁≡δ₂ = <-≡→< h3 (minxy-r δ₁ δ₂ (inj₂ (δ₁≡δ₂)))

       arf8 : δ₂ ≤ δ₁ → dist x a < δ₂
       arf8 h12 = <-≡→< h3 (minxy-r δ₁ δ₂ (≤-to-≥ h12))

-- The limit of the power of a function is the limit of the function raised to the power.

^-lim : (a L : ℝ) → (n : ℕ) → (f : ℝ → ℝ) → lim f a L →
                                  lim (λ x → (f x) ^ (succ n)) a (L ^ (succ n))
^-lim a L zero f h1 ε ε>0 = a₁-helper (h1 ε ε>0)

  where
   a₁-helper : ∃ᵣ (λ δ → δ > r₀ → (x : ℝ) → dist x a < δ → dist (f x) L < ε) →
               ∃ᵣ (λ δ → δ > r₀ → (x : ℝ) → dist x a < δ →
                                    dist (f x ^ succ zero) (L ^ succ zero) < ε)
   a₁-helper (exist δ l) = exist δ a₁₂-helper

    where
     a₁₂-helper : δ > r₀ → (x : ℝ) → dist x a < δ →
                                       dist (f x ^ succ zero) (L ^ succ zero) < ε
     a₁₂-helper δ>0 x h2 = subst₂ (λ t₁ t₂ → t₁ < t₂) a₁₃-helper (refl ε) (l δ>0 x h2)

      where
       a₁₃-helper : dist (f x) L ≡ dist (f x * r₁) (L * r₁)
       a₁₃-helper =
         dist (f x) L             ≡⟨ subst (λ w → dist (f x) L ≡ dist w L)
                                   (≡-sym (x^1≡x (f x))) (refl (dist (f x) L)) ⟩
         dist (f x * r₁) L        ≡⟨ subst (λ w → dist (f x * r₁) L ≡ dist (f x * r₁) w)
                                   (≡-sym (*-neut L)) (refl (dist (f x * r₁) L)) ⟩
         dist (f x * r₁) (L * r₁) ∎

^-lim a L (succ n) f h1 = *-lim a L (L ^ succ n) (λ z → f z) (λ z → f z ^ succ n)
                          h1 (^-lim a L n f h1)

