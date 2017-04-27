
module Limit where

open import AbsoluteValueDefinition
open import DistanceDefinition
open import DistanceProperties
open import EqReasoning
open import EqProperties
open import Exp
open import LogicDefinitions
open import Min
open import Nat
open import OrderedFieldProperties
open import RealNumbersAxioms

-- Auxiliary properties.

x>0-to-x/2>0 : (x : ℝ) → x > r₀ → x * (ℕ2ℝ 2) ⁻¹ > r₀
x>0-to-x/2>0 x x>0 = >-∧-* (x>0 , (>-inve-r₀ (>-trans 2>1 1>0)))

1/2x+1/2x=x : (x : ℝ) → x * (ℕ2ℝ 2) ⁻¹ + x * (ℕ2ℝ 2) ⁻¹ ≡ x
1/2x+1/2x=x x =
  x * (ℕ2ℝ 2) ⁻¹ + x * (ℕ2ℝ 2) ⁻¹
    ≡⟨ subst (λ w → x * (ℕ2ℝ 2) ⁻¹ + x * (ℕ2ℝ 2) ⁻¹ ≡ x * (r₁ + w) ⁻¹ + x * (ℕ2ℝ 2) ⁻¹) (+-neut r₁)
             (refl (x * (ℕ2ℝ 2) ⁻¹ + x * (ℕ2ℝ 2) ⁻¹)) ⟩
  x * (r₁ + r₁) ⁻¹ + x * (ℕ2ℝ 2) ⁻¹
    ≡⟨ subst (λ w → x * (r₁ + r₁) ⁻¹ + x * (ℕ2ℝ 2) ⁻¹ ≡ x * (r₁ + r₁) ⁻¹ + x * (r₁ + w) ⁻¹) (+-neut r₁)
             (refl (x * (r₁ + r₁) ⁻¹ + x * (ℕ2ℝ 2) ⁻¹)) ⟩
  x * (r₁ + r₁) ⁻¹ + x * (r₁ + r₁) ⁻¹
    ≡⟨ ≡-sym (*-dist-r ((r₁ + r₁) ⁻¹) x x) ⟩
  (x + x) * (r₁ + r₁) ⁻¹
    ≡⟨ subst (λ w → (x + x) * (r₁ + r₁) ⁻¹ ≡ w * (r₁ + r₁) ⁻¹) (≡-sym 2x=x+x)
             (refl ((x + x) * (r₁ + r₁) ⁻¹)) ⟩
  ((ℕ2ℝ 2) * x) * (r₁ + r₁) ⁻¹
    ≡⟨ subst (λ w → ((ℕ2ℝ 2) * x) * (r₁ + r₁) ⁻¹ ≡ ((r₁ + w) * x) * (r₁ + r₁) ⁻¹) (+-neut r₁)
             (refl (((ℕ2ℝ 2) * x) * (r₁ + r₁) ⁻¹)) ⟩
  ((r₁ + r₁) * x) * (r₁ + r₁) ⁻¹
    ≡⟨ subst (λ w → ((r₁ + r₁) * x) * (r₁ + r₁) ⁻¹ ≡ w * (r₁ + r₁) ⁻¹) (*-comm (r₁ + r₁) x)
             (refl (((r₁ + r₁) * x) * (r₁ + r₁) ⁻¹)) ⟩
  (x * (r₁ + r₁)) * (r₁ + r₁) ⁻¹
    ≡⟨ *-asso x (r₁ + r₁) ((r₁ + r₁) ⁻¹) ⟩
  x * ((r₁ + r₁) * (r₁ + r₁) ⁻¹)
    ≡⟨ subst (λ w → x * ((r₁ + r₁) * (r₁ + r₁) ⁻¹) ≡ x * w) (*-inve (r₁ + r₁) p-helper)
             (refl (x * ((r₁ + r₁) * (r₁ + r₁) ⁻¹))) ⟩
  x * r₁
    ≡⟨ *-neut x ⟩
  x   ∎

  where
   p-helper : (r₁ + r₁) ≢ r₀
   p-helper h = >→≢ (>-trans (x+1>x r₁) 1>0) h

-- Limit definition.
-- Calculus: Concepts and Contexts. Stewart James, 2001. Appendix D.

lim : (ℝ → ℝ) → ℝ → ℝ → Set
lim f a L = (ε : ℝ) → ε > r₀ →
            ∃ᵣ (λ δ → δ > r₀ → (x : ℝ) → dist x a < δ → dist (f x) L < ε)

------------------------------------------------------------------------------
-- Limit Laws.
-- Calculus: Concepts and Contexts. Stewart James, 2001. Section 2.3.

-- The limit of a constant is the constant.

cte-lim : (a L k : ℝ) → (f : ℝ → ℝ) → lim (λ _ → k) a k
cte-lim a L k f ε ε>0 = exist ε p-helper

  where
  p-helper : ε > r₀ → (x : ℝ) → dist x a < ε → dist k k < ε
  p-helper ε>0 x h = subst₂ (λ t₁ t₂ → t₁ < t₂)
                            (≡-sym (∧-proj₂ (d-refl k k)
                            (refl k)))
                            (refl ε)
                            (>-to-< ε>0)

-- The limit of a sum is the sum of the limits.

+-lim : (a L₁ L₂ : ℝ) → (f₁ f₂ : ℝ → ℝ) → lim f₁ a L₁ → lim f₂ a L₂ →
        lim (λ x → f₁ x + f₂ x) a (L₁ + L₂)
+-lim a L₁ L₂ f₁ f₂ h1 h2 ε ε>0 =
  p₁-helper (h1 (ε * ℕ2ℝ 2 ⁻¹) (x>0-to-x/2>0 ε ε>0))
            (h2 (ε * ℕ2ℝ 2 ⁻¹) (x>0-to-x/2>0 ε ε>0))

-- Choose δ = min {δ₁, δ₂}

  where
  p₁-helper : ∃ᵣ (λ δ → δ > r₀ → (x : ℝ) →
              dist x a < δ → dist (f₁ x) L₁ < ε * (ℕ2ℝ 2) ⁻¹) →
              ∃ᵣ (λ δ → δ > r₀ → (x : ℝ) → dist x a < δ → dist (f₂ x) L₂ < ε * (ℕ2ℝ 2) ⁻¹) →
              ∃ᵣ (λ δ → δ > r₀ → (x : ℝ) →
              dist x a < δ → dist (f₁ x + f₂ x) (L₁ + L₂) < ε)
  p₁-helper (exist δ₁ l₁) (exist δ₂ l₂) = exist (min δ₁ δ₂) p₂-helper

    where
    p₂-helper : min δ₁ δ₂ > r₀ → (x : ℝ) → dist x a < min δ₁ δ₂ →
                dist (f₁ x + f₂ x) (L₁ + L₂) < ε
    p₂-helper δ>0 x h₃ = ≤-<-trans (dis-des (f₁ x) L₁ (f₂ x) L₂) (p₃-helper (<-<-+ (l₁ (case arf₁ arf₂ (≤-∨ δ₁ δ₂)) x
                          (case arf₃ arf₄ (≤-∨ δ₁ δ₂))) (l₂ (case arf₅ arf₆ (≤-∨ δ₁ δ₂)) x (case arf₇ arf₈ (≤-∨ δ₁ δ₂))) ))

       where
       p₃-helper : dist (f₁ x) L₁ + dist (f₂ x) L₂ < ε * (ℕ2ℝ 2) ⁻¹ + ε * (ℕ2ℝ 2) ⁻¹ → dist (f₁ x) L₁ + dist (f₂ x) L₂ < ε
       p₃-helper h₄ = subst₂ (λ t₁ t₂ → t₁ < t₂) (refl (dist (f₁ x) L₁ + dist (f₂ x) L₂)) (1/2x+1/2x=x ε) h₄

       arf₁ : δ₁ ≤ δ₂ → δ₁ > r₀
       arf₁ h₅ = >-≡→>-1 δ>0 (≡-trans (refl (min δ₁ δ₂)) (minxy-l δ₁ δ₂ h₅))

       arf₂ : δ₂ ≤ δ₁ → δ₁ > r₀
       arf₂ h₆ = ≥->-trans (≤-to-≥ h₆) (>-≡→>-1 δ>0 (minxy-r δ₁ δ₂ (≤-to-≥ h₆)))

       arf₃ : δ₁ ≤ δ₂ → dist x a < δ₁
       arf₃ h₇ = <-≡→< h₃ (minxy-l δ₁ δ₂ h₇)

       arf₄ : δ₂ ≤ δ₁ → dist x a < δ₁
       arf₄ h₈ = case arf₄₁ arf₄₂ h₈

         where
         arf₄₁ : δ₂ < δ₁ → dist x a < δ₁
         arf₄₁ δ₂<δ₁ = <-trans (<-≡→< h₃ (minxy-r δ₁ δ₂ (inj₁ (<-to-> δ₂<δ₁)))) δ₂<δ₁

         arf₄₂ : δ₂ ≡ δ₁ → dist x a < δ₁
         arf₄₂ δ₂≡δ₁ = <-≡→< h₃ (minxy-l δ₁ δ₂ (inj₂ (≡-sym δ₂≡δ₁)))


       arf₅ : δ₁ ≤ δ₂ → δ₂ > r₀
       arf₅ h₉ = ≥->-trans (≤-to-≥ h₉) (>-≡→>-1 δ>0 (minxy-l δ₁ δ₂ h₉))

       arf₆ : δ₂ ≤ δ₁ → δ₂ > r₀
       arf₆ h₁₀ = >-≡→>-1 δ>0 (minxy-r δ₁ δ₂ (≤-to-≥ h₁₀))

       arf₇ : δ₁ ≤ δ₂ → dist x a < δ₂
       arf₇ h₁₁ = case arf₇₁ arf₇₂ h₁₁

         where
         arf₇₁ : δ₁ < δ₂ → dist x a < δ₂
         arf₇₁ δ₁<δ₂ = <-trans (<-≡→< h₃ (minxy-l δ₁ δ₂ h₁₁)) δ₁<δ₂

         arf₇₂ : δ₁ ≡ δ₂ → dist x a < δ₂
         arf₇₂ δ₁≡δ₂ = <-≡→< h₃ (minxy-r δ₁ δ₂ (inj₂ (δ₁≡δ₂)))

       arf₈ : δ₂ ≤ δ₁ → dist x a < δ₂
       arf₈ h₁₂ = <-≡→< h₃ (minxy-r δ₁ δ₂ (≤-to-≥ h₁₂))
