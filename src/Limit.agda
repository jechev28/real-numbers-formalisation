module Limit where

open import Axioms
open import EqReasoning
open import EqProperties
open import Exp
open import Logic
open import Min
open import Nat
open import Properties

-- Distance (or metric) between two points.
-- Mathematical Analysis. Apostol, Tom. M. 1974. Pag. 60.

-- Function distance between two points.
postulate
  dist : ℝ → ℝ → ℝ

-- Properties of the dist function.
postulate
  d-pos  : (x y : ℝ) → dist x y ≥ r₀
  d-sym  : (x y : ℝ) → dist x y ≡ dist y x
  d-refl : (x y : ℝ) → (dist x y ≡ r₀) ↔ (x ≡ y)
  d-tri  : (x y z : ℝ) → dist x y ≤ dist x z + dist z y

-- Pending to prove.
postulate
  dis-des : (x y z w : ℝ) → dist (x + z) (y + w) ≤ dist x y + dist z w

-- Previous properties.

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
lim f a L = (ε : ℝ) → ε > r₀ → ∃ᵣ (λ δ → δ > r₀ → (x : ℝ) → dist x a < δ → dist (f x) L < ε)

-- Limit Laws.
-- Calculus: Concepts and Contexts. Stewart James, 2001. Section 2.3.

-- The limit of a constant is the constant.

cte-lim : (a L k : ℝ) → (f : ℝ → ℝ) → lim (λ _ → k) a k
cte-lim a L k f ε ε>0 = exist ε p-helper

  where
   p-helper : ε > r₀ → (x : ℝ) → dist x a < ε → dist k k < ε
   p-helper ε>0 x h = subst₂ (λ t₁ t₂ → t₁ < t₂) (≡-sym (∧-proj₂ (d-refl k k) (refl k))) (refl ε) (>-to-< ε>0)

-- The limit of a sum is the sum of the limits.

+-lim : (a L₁ L₂ : ℝ) → (f₁ f₂ : ℝ → ℝ) → lim f₁ a L₁ → lim f₂ a L₂ → lim (λ x → f₁ x + f₂ x) a (L₁ + L₂)
+-lim a L₁ L₂ f₁ f₂ h1 h2 ε ε>0 = a₁-helaer (h1 (ε * ℕ2ℝ 2 ⁻¹) (x>0-to-x/2>0 ε ε>0))
                                      (h2 (ε * ℕ2ℝ 2 ⁻¹) (x>0-to-x/2>0 ε ε>0))

-- Choose δ = min {δ₁, δ₂}

  where
   a₁-helaer : ∃ᵣ (λ δ → δ > r₀ → (x : ℝ) → dist x a < δ → dist (f₁ x) L₁ < ε * (ℕ2ℝ 2) ⁻¹) →
    ∃ᵣ (λ δ → δ > r₀ → (x : ℝ) → dist x a < δ → dist (f₂ x) L₂ < ε * (ℕ2ℝ 2) ⁻¹) → ∃ᵣ (λ δ → δ > r₀ → (x : ℝ) →
    dist x a < δ → dist (f₁ x + f₂ x) (L₁ + L₂) < ε)
   a₁-helaer (exist δ₁ l₁) (exist δ₂ l₂) = exist (min δ₁ δ₂) a₂-helaer

    where
     a₂-helaer : min δ₁ δ₂ > r₀ → (x : ℝ) → dist x a < min δ₁ δ₂ → dist (f₁ x + f₂ x) (L₁ + L₂) < ε
     a₂-helaer δ>0 x h3 = ≤-<-trans (dis-des (f₁ x) L₁ (f₂ x) L₂) (a₃-helaer (<-<-+ (l₁ (case arf1 arf2 (≤-∨ δ₁ δ₂)) x
                          (case arf3 arf4 (≤-∨ δ₁ δ₂))) (l₂ (case arf5 arf6 (≤-∨ δ₁ δ₂)) x (case arf7 arf8 (≤-∨ δ₁ δ₂))) ))

       where
        a₃-helaer : dist (f₁ x) L₁ + dist (f₂ x) L₂ < ε * (ℕ2ℝ 2) ⁻¹ + ε * (ℕ2ℝ 2) ⁻¹ → dist (f₁ x) L₁ + dist (f₂ x) L₂ < ε
        a₃-helaer h4 = subst₂ (λ t₁ t₂ → t₁ < t₂) (refl (dist (f₁ x) L₁ + dist (f₂ x) L₂)) (1/2x+1/2x=x ε) h4

        arf1 : δ₁ ≤ δ₂ → δ₁ > r₀
        arf1 h5 = >-≡→> δ>0 (≡-trans (refl (min δ₁ δ₂)) (minxy-l δ₁ δ₂ h5))

        arf2 : δ₂ ≤ δ₁ → δ₁ > r₀
        arf2 h6 = ≥->-trans (≤-to-≥ h6) (>-≡→> δ>0 (minxy-r δ₁ δ₂ (≤-to-≥ h6)))

        arf3 : δ₁ ≤ δ₂ → dist x a < δ₁
        arf3 h7 = <-≡→< h3 (minxy-l δ₁ δ₂ h7)

        arf4 : δ₂ ≤ δ₁ → dist x a < δ₁
        arf4 h8 = case arf41 arf42 h8

         where
          arf41 : δ₂ < δ₁ → dist x a < δ₁
          arf41 δ₂<δ₁ = <-trans (<-≡→< h3 (minxy-r δ₁ δ₂ (inj₁ (<-to-> δ₂<δ₁)))) δ₂<δ₁

          arf42 : δ₂ ≡ δ₁ → dist x a < δ₁
          arf42 δ₂≡δ₁ = <-≡→< h3 (minxy-l δ₁ δ₂ (inj₂ (≡-sym δ₂≡δ₁)))


        arf5 : δ₁ ≤ δ₂ → δ₂ > r₀
        arf5 h9 = ≥->-trans (≤-to-≥ h9) (>-≡→> δ>0 (minxy-l δ₁ δ₂ h9))

        arf6 : δ₂ ≤ δ₁ → δ₂ > r₀
        arf6 h10 = >-≡→> δ>0 (minxy-r δ₁ δ₂ (≤-to-≥ h10))

        arf7 : δ₁ ≤ δ₂ → dist x a < δ₂
        arf7 h11 = case arf71 arf72 h11

         where
          arf71 : δ₁ < δ₂ → dist x a < δ₂
          arf71 δ₁<δ₂ = <-trans (<-≡→< h3 (minxy-l δ₁ δ₂ h11)) δ₁<δ₂

          arf72 : δ₁ ≡ δ₂ → dist x a < δ₂
          arf72 δ₁≡δ₂ = <-≡→< h3 (minxy-r δ₁ δ₂ (inj₂ (δ₁≡δ₂)))

        arf8 : δ₂ ≤ δ₁ → dist x a < δ₂
        arf8 h12 = <-≡→< h3 (minxy-r δ₁ δ₂ (≤-to-≥ h12))
