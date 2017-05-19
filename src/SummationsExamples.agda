
module SummationsExamples where

open import EqProperties
open import EqReasoning
open import Exp
open import LogicDefinitions
open import Nat
open import OrderedFieldProperties
open import RealNumbersAxioms

-- Aₙ = 1 + 3 + 5 + ... + 2n - 1.

A : ℕ → ℝ
A zero     = r₀
A (succ n) = A n + (ℕ2ℝ 2) * (ℕ2ℝ n) + r₁

-- Demonstration that Aₙ = n².

A-con : (n : ℕ) → A n ≡ sqr (ℕ2ℝ n)
A-con zero = p-helper
  where
  p-helper : A zero ≡ sqr (ℕ2ℝ zero)
  p-helper =
    A zero         ≡⟨ refl r₀ ⟩
    r₀             ≡⟨ ≡-sym r₀-sqr ⟩
    sqr (ℕ2ℝ zero) ∎

A-con (succ n) = p-helper
  where
  p-helper : A (succ n) ≡ sqr (ℕ2ℝ (succ n))
  p-helper =
    A (succ n)                       ≡⟨ refl (A n + ℕ2ℝ 2 * ℕ2ℝ n + r₁) ⟩
    A n + ℕ2ℝ 2 * ℕ2ℝ n + r₁         ≡⟨ subst (λ w → A n + ℕ2ℝ 2 * ℕ2ℝ n + r₁ ≡
                                                     w + ℕ2ℝ 2 * ℕ2ℝ n + r₁)
                                              (A-con n)
                                              (refl (A n + ℕ2ℝ 2 * ℕ2ℝ n + r₁))
                                     ⟩
    sqr (ℕ2ℝ n) + ℕ2ℝ 2 * ℕ2ℝ n + r₁ ≡⟨ ≡-sym (PST1 (ℕ2ℝ n)) ⟩
    sqr (ℕ2ℝ n + r₁)                 ≡⟨ subst (λ w → sqr (ℕ2ℝ n + r₁) ≡ sqr w)
                                              (+-comm (ℕ2ℝ n) r₁)
                                              (refl (sqr (ℕ2ℝ n + r₁)))
                                     ⟩
    sqr (r₁ + ℕ2ℝ n)                 ∎

-- Bₙ(r) = 1 + r + r² + r³ + ... + rⁿ. r∈ℝ, n∈ℕ.

B : ℝ → ℕ → ℝ
B r zero     = r₁
B r (succ n) = B r n + r ^ (succ n)

--  Demonstration of the value of geometric progression:
-- 1 + r + r² + r³ + ... + rⁿ = (1 - rⁿ⁺¹)(1 - r)⁻¹. r∈ℝ, n∈ℕ.

B-con : (r : ℝ) → (n : ℕ) → ¬ ( r ≡ r₁) → B r n ≡ (ℕ2ℝ 1 - r ^ (succ n)) * (ℕ2ℝ 1 - r) ⁻¹
B-con r zero r≠r₁ = ≡-sym p-helper

  where
   p-helper : (r₁ + r₀ - r * r₁) * (r₁ + r₀ - r) ⁻¹ ≡ r₁
   p-helper =
     (r₁ + r₀ - r * r₁) * (r₁ + r₀ - r) ⁻¹
       ≡⟨ subst (λ w → (r₁ + r₀ - r * r₁) * (r₁ + r₀ - r) ⁻¹ ≡ (r₁ + r₀ - w) * (r₁ + r₀ - r) ⁻¹)
       (*-neut r) (refl ((r₁ + r₀ - r * r₁) * (r₁ + r₀ - r) ⁻¹)) ⟩
     (r₁ + r₀ - r) * (r₁ + r₀ - r) ⁻¹
       ≡⟨ subst (λ w → (r₁ + r₀ - r) * (r₁ + r₀ - r) ⁻¹ ≡ (w - r) * (r₁ + r₀ - r) ⁻¹) (+-neut r₁)
       (refl ((r₁ + r₀ - r) * (r₁ + r₀ - r) ⁻¹)) ⟩
     (r₁ - r) * (r₁ + r₀ - r) ⁻¹
       ≡⟨ subst (λ w → (r₁ - r) * (r₁ + r₀ - r) ⁻¹ ≡ (r₁ - r) * (w - r) ⁻¹) (+-neut r₁)
       (refl ((r₁ - r) * (r₁ + r₀ - r) ⁻¹)) ⟩
     (r₁ - r) * (r₁ - r) ⁻¹
       ≡⟨ *-inve (r₁ - r) (p₁-helper) ⟩
     r₁ ∎

    where
     p₁-helper : ¬ (r₁ - r ≡ r₀)
     p₁-helper h = p₁₁-helper p₁₂-helper

      where
       p₁₁-helper : r ≡ r₁ → ⊥
       p₁₁-helper r≡r₁ = r≠r₁ r≡r₁

       p₁₂-helper : r ≡ r₁
       p₁₂-helper =
         r              ≡⟨ ≡-sym (+-neut r) ⟩
         r + r₀         ≡⟨ subst (λ w → r + r₀ ≡ r + w) (≡-sym (h)) (refl (r + r₀)) ⟩
         r + (r₁ - r)   ≡⟨ subst (λ w → r + (r₁ - r) ≡ r + w) (+-comm r₁ (- r)) (refl (r + (r₁ - r))) ⟩
         r + (- r + r₁) ≡⟨ ≡-sym (+-asso r (- r) r₁) ⟩
         (r - r) + r₁     ≡⟨ subst (λ w → r - r + r₁ ≡ w + r₁) (+-inve r) (refl (r - r + r₁)) ⟩
         r₀ + r₁        ≡⟨ +-comm r₀ r₁ ⟩
         r₁ + r₀        ≡⟨ +-neut r₁ ⟩
         r₁             ∎

B-con r (succ n) r≠r₁ = p-helper

  where
   p-helper : B r (succ n) ≡ (ℕ2ℝ 1 - r ^ succ (succ n)) * (ℕ2ℝ 1 - r) ⁻¹
   p-helper =
     B r n + r ^ succ n
       ≡⟨ subst (λ w → B r n + r ^ succ n ≡ w + r ^ succ n) (B-con r n r≠r₁) (refl (B r n + r ^ succ n)) ⟩
     (ℕ2ℝ 1 - r ^ succ n) * (ℕ2ℝ 1 - r) ⁻¹ + r ^ succ n
       ≡⟨ subst (λ w → (ℕ2ℝ 1 - r ^ succ n) * (ℕ2ℝ 1 - r) ⁻¹ + r ^ succ n ≡ (ℕ2ℝ 1 - r ^ succ n) * (ℕ2ℝ 1 - r) ⁻¹ + w)
       (≡-sym (*-neut (r ^ succ n))) (refl ((r₁ + r₀ - r * r ^ n) * (r₁ + r₀ - r) ⁻¹ + r * r ^ n)) ⟩
     (ℕ2ℝ 1 - r ^ succ n) * (ℕ2ℝ 1 - r) ⁻¹ + r ^ succ n * r₁
       ≡⟨ subst (λ w → (ℕ2ℝ 1 - r ^ succ n) * (ℕ2ℝ 1 - r) ⁻¹ + r ^ succ n * r₁ ≡ (ℕ2ℝ 1 - r ^ succ n) * (ℕ2ℝ 1 - r) ⁻¹
       + r ^ succ n * w) 1≡1⁻¹ (refl ((r₁ + r₀ - r * r ^ n) * (r₁ + r₀ - r) ⁻¹ + r * r ^ n * r₁)) ⟩
     (ℕ2ℝ 1 - r ^ succ n) * (ℕ2ℝ 1 - r) ⁻¹ + r ^ succ n * r₁ ⁻¹
       ≡⟨ +-fractional p₁-helper 1≢0 ⟩
     ((ℕ2ℝ 1 - r ^ succ n) * r₁ + (ℕ2ℝ 1 - r) * r ^ succ n) * ((ℕ2ℝ 1 - r) * r₁) ⁻¹
       ≡⟨ subst (λ w → ((ℕ2ℝ 1 - r ^ succ n) * r₁ + (ℕ2ℝ 1 - r) * r ^ succ n) * ((ℕ2ℝ 1 - r) * r₁) ⁻¹ ≡ (w + (ℕ2ℝ 1 - r)
       * r ^ succ n) * ((ℕ2ℝ 1 - r) * r₁) ⁻¹) (*-neut ((ℕ2ℝ 1 - r ^ succ n))) (refl (((r₁ + r₀ - r * r ^ n)
       * r₁ + (r₁ + r₀ - r) * (r * r ^ n)) * ((r₁ + r₀ - r) * r₁) ⁻¹)) ⟩
     (ℕ2ℝ 1 - r ^ succ n + (ℕ2ℝ 1 - r) * r ^ succ n) * ((ℕ2ℝ 1 - r) * r₁) ⁻¹
       ≡⟨ subst (λ w → (ℕ2ℝ 1 - r ^ succ n + (ℕ2ℝ 1 - r) * r ^ succ n) * ((ℕ2ℝ 1 - r) * r₁) ⁻¹ ≡ (ℕ2ℝ 1 - r ^ succ n
       + (ℕ2ℝ 1 - r) * r ^ succ n) * w ⁻¹) (*-neut (ℕ2ℝ 1 - r)) (refl ((r₁ + r₀ - r * r ^ n + (r₁ + r₀ - r) * (r * r ^ n))
       * ((r₁ + r₀ - r) * r₁) ⁻¹)) ⟩
     (ℕ2ℝ 1 - r ^ succ n + (ℕ2ℝ 1 + - r) * r ^ succ n) * (ℕ2ℝ 1 - r) ⁻¹
       ≡⟨ subst (λ w → (ℕ2ℝ 1 - r ^ succ n + (ℕ2ℝ 1 + - r) * r ^ succ n) * (ℕ2ℝ 1 - r) ⁻¹ ≡ (ℕ2ℝ 1 - r ^ succ n + w)
       * (ℕ2ℝ 1 - r) ⁻¹) (*-dist-r (r ^ succ n) (ℕ2ℝ 1) (- r)) (refl ((r₁ + r₀ - r * r ^ n + (r₁ + r₀ + - r)
       * (r * r ^ n)) * (r₁ + r₀ - r) ⁻¹)) ⟩
     (ℕ2ℝ 1 - r ^ succ n + (ℕ2ℝ 1 * r ^ succ n + - r * r ^ succ n)) * (ℕ2ℝ 1 - r) ⁻¹
       ≡⟨ subst (λ w → (ℕ2ℝ 1 - r ^ succ n + (ℕ2ℝ 1 * r ^ succ n + - r * r ^ succ n)) * (ℕ2ℝ 1 - r) ⁻¹ ≡ (ℕ2ℝ 1 - r ^ succ n
       + (w + - r * r ^ succ n)) * (ℕ2ℝ 1 - r) ⁻¹) (*-comm (ℕ2ℝ 1) (r ^ succ n)) (refl ((r₁ + r₀ - r * r ^ n + ((r₁ + r₀)
       * (r * r ^ n) + - r * (r * r ^ n))) * (r₁ + r₀ - r) ⁻¹)) ⟩
     (ℕ2ℝ 1 - r ^ succ n + (r ^ succ n * ℕ2ℝ 1 + - r * r ^ succ n)) * (ℕ2ℝ 1 - r) ⁻¹
       ≡⟨ subst (λ w → (ℕ2ℝ 1 - r ^ succ n + (r ^ succ n * ℕ2ℝ 1 + - r * r ^ succ n)) * (ℕ2ℝ 1 - r) ⁻¹ ≡ (ℕ2ℝ 1
       - r ^ succ n + (r ^ succ n * w + - r * r ^ succ n)) * (ℕ2ℝ 1 - r) ⁻¹) (+-neut r₁) (refl ((r₁ + r₀ - r * r ^ n
       + (r * r ^ n * (r₁ + r₀) + - r * (r * r ^ n))) * (r₁ + r₀ - r) ⁻¹)) ⟩
     (ℕ2ℝ 1 - r ^ succ n + (r ^ succ n * r₁ + - r * r ^ succ n)) * (ℕ2ℝ 1 - r) ⁻¹
       ≡⟨ subst (λ w → (ℕ2ℝ 1 - r ^ succ n + (r ^ succ n * r₁ + - r * r ^ succ n)) * (ℕ2ℝ 1 - r) ⁻¹ ≡ (ℕ2ℝ 1 - r ^ succ n
       + (w + - r * r ^ succ n)) * (ℕ2ℝ 1 - r) ⁻¹) (*-neut (r ^ succ n)) (refl ((r₁ + r₀ - r * r ^ n + (r * r ^ n * r₁
       + - r * (r * r ^ n))) * (r₁ + r₀ - r) ⁻¹)) ⟩
     (ℕ2ℝ 1 - r ^ succ n + (r ^ succ n + - r * r ^ succ n)) * (ℕ2ℝ 1 - r) ⁻¹
       ≡⟨ subst (λ w → (ℕ2ℝ 1 - r ^ succ n + (r ^ succ n + - r * r ^ succ n)) * (ℕ2ℝ 1 - r) ⁻¹ ≡ w * (ℕ2ℝ 1 - r) ⁻¹)
       (+-asso (ℕ2ℝ 1) (- r ^ succ n) (r ^ succ n + - r * r ^ succ n)) (refl ((r₁ + r₀ + - (r * r ^ n)
       + (r * r ^ n + - r * (r * r ^ n))) * (r₁ + r₀ - r) ⁻¹)) ⟩
     (ℕ2ℝ 1 + (- r ^ succ n + (r ^ succ n + - r * r ^ succ n))) * (ℕ2ℝ 1 - r) ⁻¹
       ≡⟨ subst (λ w → (ℕ2ℝ 1 + (- (r ^ succ n) + (r ^ succ n + - r * r ^ succ n))) * (ℕ2ℝ 1 - r) ⁻¹ ≡ (ℕ2ℝ 1 + w)
       * (ℕ2ℝ 1 - r) ⁻¹) (≡-sym (+-asso (- (r ^ succ n)) (r ^ succ n) (- r * r ^ succ n))) (refl ((r₁ + r₀ + (- (r * r ^ n)
       + (r * r ^ n + - r * (r * r ^ n)))) * (r₁ + r₀ - r) ⁻¹)) ⟩
     (ℕ2ℝ 1 + ((- r ^ succ n + r ^ succ n) + - r * r ^ succ n)) * (ℕ2ℝ 1 - r) ⁻¹
       ≡⟨ subst (λ w → (ℕ2ℝ 1 + (- (r ^ succ n) + r ^ succ n + - r * r ^ succ n)) * (ℕ2ℝ 1 - r) ⁻¹ ≡
       (ℕ2ℝ 1 + (w + - r * r ^ succ n)) * (ℕ2ℝ 1 - r) ⁻¹) (+-comm (- (r ^ succ n)) (r ^ succ n)) (refl ((r₁ + r₀ + (- (r * r ^ n)
       + r * r ^ n + - r * (r * r ^ n))) * (r₁ + r₀ - r) ⁻¹)) ⟩
     (ℕ2ℝ 1 + ((r ^ succ n + - r ^ succ n) + - r * r ^ succ n)) * (ℕ2ℝ 1 - r) ⁻¹
       ≡⟨ subst (λ w → (ℕ2ℝ 1 + (r ^ succ n + - (r ^ succ n) + - r * r ^ succ n)) * (ℕ2ℝ 1 - r) ⁻¹ ≡ (ℕ2ℝ 1
       + (w + - r * r ^ succ n)) * (ℕ2ℝ 1 - r) ⁻¹) (+-inve (r ^ succ n)) (refl ((r₁ + r₀ + (r * r ^ n + - (r * r ^ n)
       + - r * (r * r ^ n))) * (r₁ + r₀ - r) ⁻¹)) ⟩
     (ℕ2ℝ 1 + (r₀ + - r * r ^ succ n)) * (ℕ2ℝ 1 - r) ⁻¹
       ≡⟨ subst (λ w → (ℕ2ℝ 1 + (r₀ + - r * r ^ succ n)) * (ℕ2ℝ 1 - r) ⁻¹ ≡ (ℕ2ℝ 1 + w) * (ℕ2ℝ 1 - r) ⁻¹)
       (+-comm r₀ (- r * r ^ succ n)) (refl ((r₁ + r₀ + (r₀ + - r * (r * r ^ n))) * (r₁ + r₀ - r) ⁻¹)) ⟩
     (ℕ2ℝ 1 + (- r * r ^ succ n + r₀)) * (ℕ2ℝ 1 - r) ⁻¹
       ≡⟨ subst (λ w → (ℕ2ℝ 1 + (- r * r ^ succ n + r₀)) * (ℕ2ℝ 1 - r) ⁻¹ ≡ (ℕ2ℝ 1 + w) * (ℕ2ℝ 1 - r) ⁻¹)
       (+-neut (- r * r ^ succ n)) (refl ((r₁ + r₀ + (- r * (r * r ^ n) + r₀)) * (r₁ + r₀ - r) ⁻¹)) ⟩
     (ℕ2ℝ 1 + - r * r ^ succ n) * (ℕ2ℝ 1 - r) ⁻¹
       ≡⟨ subst (λ w → (ℕ2ℝ 1 + - r * r ^ succ n) * (ℕ2ℝ 1 - r) ⁻¹ ≡ (ℕ2ℝ 1 + w) * (ℕ2ℝ 1 - r) ⁻¹) mul-xy
       (refl ((r₁ + r₀ + - r * (r * r ^ n)) * (r₁ + r₀ - r) ⁻¹)) ⟩
     (ℕ2ℝ 1 - r ^ succ (succ n)) * (ℕ2ℝ 1 - r) ⁻¹ ∎

    where
     p₁-helper : ¬ (r₁ + r₀ - r ≡ r₀)
     p₁-helper h = p₁₁-helper p₁₂-helper

      where
       p₁₁-helper : r ≡ r₁ → ⊥
       p₁₁-helper r≡r₁ = r≠r₁ r≡r₁

       p₁₂-helper : r ≡ r₁
       p₁₂-helper =
         r                 ≡⟨ ≡-sym (+-neut r) ⟩
         r + r₀            ≡⟨ subst (λ w → r + r₀ ≡ r + w) (≡-sym h) (refl (r + r₀)) ⟩
         r + (r₁ + r₀ - r) ≡⟨ subst (λ w → r + (r₁ + r₀ - r) ≡ r + (w - r)) (+-neut r₁) (refl (r + (r₁ + r₀ - r))) ⟩
         r + (r₁ - r)      ≡⟨ subst (λ w → r + (r₁ - r) ≡ r + w) (+-comm r₁ (- r)) (refl (r + (r₁ - r))) ⟩
         r + (- r + r₁)    ≡⟨ ≡-sym (+-asso r (- r) r₁) ⟩
         r - r + r₁        ≡⟨ subst (λ w → r - r + r₁ ≡ w + r₁) (+-inve r) (refl (r - r + r₁)) ⟩
         r₀ + r₁           ≡⟨ +-comm r₀ r₁ ⟩
         r₁ + r₀           ≡⟨ +-neut r₁ ⟩
         r₁                ∎
