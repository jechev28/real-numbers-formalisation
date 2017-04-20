module Completeness where

open import Axioms
open import EqReasoning
open import EqProperties
open import Logic
open import PoProperties
open import Properties
open import Nat

-- Example 1.

A : ℝ → Set
A x = x ≤ ℕ2ℝ 2

-- A is bounded above by 2. A maximum is equal to 2.
-- As A = (- ∞, 2], then the set of upper bounds of A is (2, + ∞).
-- sup A = 2, sup A ∈ A.

UBA : UpperBound A (ℕ2ℝ 2)
UBA x (inj₁ x<2) = inj₁ x<2
UBA x (inj₂ x≡2) = inj₂ x≡2

UBA3 : UpperBound A (ℕ2ℝ 3)
UBA3 x (inj₁ x<2) = inj₁ (<-trans x<2 (<-+-left (<-+-left (>-to-< (subst₂ (λ t₁ t₂ → t₁ > t₂)
                    (≡-sym (+-neut r₁)) (refl r₀) 1>0)))))
UBA3 x (inj₂ x≡2) = inj₁ (≡-<→< x≡2 (<-+-left (<-+-left (>-to-< (subst₂ (λ t₁ t₂ → t₁ > t₂)
                    (≡-sym (+-neut r₁)) (refl r₀) 1>0)))))

bar : Bound A
bar = exist (ℕ2ℝ 2) UBA

UBAx : (x : ℝ) → UpperBound A x → ℕ2ℝ 2 ≤ x
UBAx x A2 = A2 (ℕ2ℝ 2) (inj₂ (refl (ℕ2ℝ 2)))

LbA : ∃ᵣ (λ x → Lub A (ℕ2ℝ 2))
LbA = exist (ℕ2ℝ 2) (UBA , UBAx)

-- Example 2.

B : ℝ → Set
B x = x < (ℕ2ℝ 5)

-- B is bounded above by 5. B has no maximum.
-- As B = (- ∞, 5), then the set of upper bounds of B is [5, + ∞).
-- sup B = 5, sup B ∉ B.

UBB5 : UpperBound B (ℕ2ℝ 5)
UBB5 x B2 = inj₁ B2

UBB6 : UpperBound B (ℕ2ℝ 6)
UBB6 x B6 = inj₁ (<-trans B6 (<-+-left (<-+-left (<-+-left (<-+-left (<-+-left (>-to-< (subst₂ (λ t₁ t₂ → t₁ > t₂)
             (≡-sym (+-neut r₁)) (refl r₀) 1>0))))))))

bar1 : Bound B
bar1 = exist (ℕ2ℝ 5) UBB5

-- UBB5≤ub : (ub : ℝ) → UpperBound B ub → (ℕ2ℝ 5) ≤ ub
-- UBB5≤ub ub Bub = case prf1 (case prf2 prf3) ( ⊕⊕→∨∨ (trichotomy ub (ℕ2ℝ 5)) )

--   where
--    prf1 : ub > ℕ2ℝ 5 → ℕ2ℝ 5 < ub ∨ ℕ2ℝ 5 ≡ ub
--    prf1 h₁ = inj₁ (>-to-< h₁)

--    prf2 : ub ≡ ℕ2ℝ 5 → ℕ2ℝ 5 < ub ∨ ℕ2ℝ 5 ≡ ub
--    prf2 h₂ = inj₂ (≡-sym h₂)

--    prf3 : ub < ℕ2ℝ 5 → ℕ2ℝ 5 < ub ∨ ℕ2ℝ 5 ≡ ub
--    prf3 h₃ = inj₁ (⊥-elim (<→≱ p₁-helper (≤-to-≥ p₂-helper)))

--      where
--       p₁-helper : ub < (ub + (ℕ2ℝ 5)) * (ℕ2ℝ 2)⁻¹
--       p₁-helper = p₁₁-helper
--                     (p₁₂-helper
--                      (p₁₃-helper
--                       (p₁₄-helper
--                        (p₁₅-helper (p₁₆-helper (p₁₇-helper (<-+-left h₃)))))))

--        where
--         p₁₁-helper : ub * ℕ2ℝ 2 < (ub + ℕ2ℝ 5) * ℕ2ℝ 2 ⁻¹ * ℕ2ℝ 2 → ub < (ub + ℕ2ℝ 5) * (ℕ2ℝ 2)⁻¹
--         p₁₁-helper h₃₁ = >-to-< (>-*-cancel-r (>-trans 2>1 1>0) (<-to-> h₃₁))

--         p₁₂-helper : ub * ℕ2ℝ 2 < (ub + ℕ2ℝ 5) * (ℕ2ℝ 2 ⁻¹ * ℕ2ℝ 2 ) → ub * ℕ2ℝ 2 < (ub + ℕ2ℝ 5) * ℕ2ℝ 2 ⁻¹ * ℕ2ℝ 2
--         p₁₂-helper h₃₂ = subst₂ (λ t₁ t₂ → t₁ < t₂) (refl (ub * ℕ2ℝ 2)) (≡-sym (*-asso (ub + ℕ2ℝ 5) (ℕ2ℝ 2 ⁻¹) (ℕ2ℝ 2))) h₃₂

--         p₁₃-helper : ub * ℕ2ℝ 2 < (ub + ℕ2ℝ 5) * ( ℕ2ℝ 2 * ℕ2ℝ 2 ⁻¹ ) → ub * ℕ2ℝ 2 < (ub + ℕ2ℝ 5) * (ℕ2ℝ 2 ⁻¹ * ℕ2ℝ 2 )
--         p₁₃-helper = subst₂ (λ t₁ t₂ → t₁ < t₂) (refl (ub * ℕ2ℝ 2)) p₁₃₁-helper

--           where
--            p₁₃₁-helper : (ub + ℕ2ℝ 5) * (ℕ2ℝ 2 * ℕ2ℝ 2 ⁻¹) ≡ (ub + ℕ2ℝ 5) * (ℕ2ℝ 2 ⁻¹ * ℕ2ℝ 2)
--            p₁₃₁-helper = subst (λ w → (ub + ℕ2ℝ 5) * (ℕ2ℝ 2 * ℕ2ℝ 2 ⁻¹) ≡ (ub + ℕ2ℝ 5) * w) (*-comm (ℕ2ℝ 2)
--                         (ℕ2ℝ 2 ⁻¹)) (refl ((ub + ℕ2ℝ 5) * (ℕ2ℝ 2 * ℕ2ℝ 2 ⁻¹)))

--         p₁₄-helper :  ub * ℕ2ℝ 2 < (ub + ℕ2ℝ 5) * r₁ → ub * ℕ2ℝ 2 < (ub + ℕ2ℝ 5) * (ℕ2ℝ 2 * ℕ2ℝ 2 ⁻¹)
--         p₁₄-helper = subst₂ (λ t₁ t₂ → t₁ < t₂) (refl (ub * ℕ2ℝ 2)) (subst (λ w → (ub + ℕ2ℝ 5) * r₁ ≡ (ub + ℕ2ℝ 5) * w)
--                     (≡-sym (*-inve (ℕ2ℝ 2) (>→≢ (>-trans 2>1 1>0)))) (refl ((ub + ℕ2ℝ 5) * r₁)))

--         p₁₅-helper :  ub * ℕ2ℝ 2 < (ub + ℕ2ℝ 5) → ub * ℕ2ℝ 2 < (ub + ℕ2ℝ 5) * r₁
--         p₁₅-helper = subst₂ (λ t₁ t₂ → t₁ < t₂) (refl (ub * ℕ2ℝ 2)) (≡-sym (*-neut (ub + ℕ2ℝ 5)))

--         p₁₆-helper : ℕ2ℝ 2 * ub < (ub + ℕ2ℝ 5) → ub * ℕ2ℝ 2 < (ub + ℕ2ℝ 5)
--         p₁₆-helper = subst₂ (λ t₁ t₂ → t₁ < t₂) (*-comm (ℕ2ℝ 2) ub) (refl (ub + ℕ2ℝ 5))

--         p₁₇-helper : ub + ub < (ub + ℕ2ℝ 5) → ℕ2ℝ 2 * ub < (ub + ℕ2ℝ 5)
--         p₁₇-helper = subst₂ (λ t₁ t₂ → t₁ < t₂) (≡-sym 2x=x+x) (refl (ub + ℕ2ℝ 5))

--       p₂-helper : (ub + (ℕ2ℝ 5)) * (ℕ2ℝ 2)⁻¹ ≤ ub
--       p₂-helper = Bub ((ub + ℕ2ℝ 5) * ℕ2ℝ 2 ⁻¹) (p₂₁-helper (p₂₂-helper (p₂₃-helper (p₂₄-helper (p₂₅-helper
--                   (p₂₆-helper (<-+-cong-r h₃)))))))

--         where
--          p₂₁-helper : ((ub + ℕ2ℝ 5) * ℕ2ℝ 2 ⁻¹) * ℕ2ℝ 2 < ℕ2ℝ 5 * ℕ2ℝ 2 → ((ub + ℕ2ℝ 5) * ℕ2ℝ 2 ⁻¹) < ℕ2ℝ 5
--          p₂₁-helper h₄ = >-to-< (>-*-cancel-r (>-trans 2>1 1>0) (<-to-> h₄))

--          p₂₂-helper : ((ub + ℕ2ℝ 5) * ℕ2ℝ 2 ⁻¹) * ℕ2ℝ 2 < ℕ2ℝ 2 * ℕ2ℝ 5 → ((ub + ℕ2ℝ 5) * ℕ2ℝ 2 ⁻¹) * ℕ2ℝ 2 < ℕ2ℝ 5 * ℕ2ℝ 2
--          p₂₂-helper h₅ = subst₂ (λ t₁ t₂ → t₁ < t₂) (refl ((ub + ℕ2ℝ 5) * ℕ2ℝ 2 ⁻¹ * ℕ2ℝ 2)) (*-comm (ℕ2ℝ 2) (ℕ2ℝ 5)) h₅

--          p₂₃-helper : (ub + ℕ2ℝ 5) * (ℕ2ℝ 2 ⁻¹ * ℕ2ℝ 2) < ℕ2ℝ 5 + ℕ2ℝ 5 → ((ub + ℕ2ℝ 5) * ℕ2ℝ 2 ⁻¹) * ℕ2ℝ 2 < ℕ2ℝ 2 * ℕ2ℝ 5
--          p₂₃-helper h₆ = subst₂ (λ t₁ t₂ → t₁ < t₂) (≡-sym (*-asso (ub + ℕ2ℝ 5) (ℕ2ℝ 2 ⁻¹) (ℕ2ℝ 2))) (≡-sym 2x=x+x) h₆

--          p₂₄-helper : (ub + ℕ2ℝ 5) * (ℕ2ℝ 2 * ℕ2ℝ 2 ⁻¹) < ℕ2ℝ 5 + ℕ2ℝ 5 → (ub + ℕ2ℝ 5) * (ℕ2ℝ 2 ⁻¹ * ℕ2ℝ 2) < ℕ2ℝ 5 + ℕ2ℝ 5
--          p₂₄-helper h₇ = subst₂ (λ t₁ t₂ → t₁ < t₂) p-helper (refl (ℕ2ℝ 5 + ℕ2ℝ 5)) h₇

--            where
--             p-helper : (ub + ℕ2ℝ 5) * (ℕ2ℝ 2 * ℕ2ℝ 2 ⁻¹) ≡ (ub + ℕ2ℝ 5) * (ℕ2ℝ 2 ⁻¹ * ℕ2ℝ 2)
--             p-helper = subst (λ w → (ub + ℕ2ℝ 5) * (ℕ2ℝ 2 * ℕ2ℝ 2 ⁻¹) ≡ (ub + ℕ2ℝ 5) * w) (*-comm (ℕ2ℝ 2) (ℕ2ℝ 2 ⁻¹))
--                        (refl ((ub + ℕ2ℝ 5) * (ℕ2ℝ 2 * ℕ2ℝ 2 ⁻¹)))

--          p₂₅-helper : (ub + ℕ2ℝ 5) * r₁ < ℕ2ℝ 5 + ℕ2ℝ 5 → (ub + ℕ2ℝ 5) * (ℕ2ℝ 2 * ℕ2ℝ 2 ⁻¹) < ℕ2ℝ 5 + ℕ2ℝ 5
--          p₂₅-helper = subst₂ (λ t₁ t₂ → t₁ < t₂) p-helper (refl (ℕ2ℝ 5 + ℕ2ℝ 5))

--            where
--             p-helper : (ub + ℕ2ℝ 5) * r₁ ≡ (ub + ℕ2ℝ 5) * (ℕ2ℝ 2 * ℕ2ℝ 2 ⁻¹)
--             p-helper = subst (λ w → (ub + ℕ2ℝ 5) * r₁ ≡ (ub + ℕ2ℝ 5) * w) (≡-sym (*-inve (ℕ2ℝ 2) (>→≢ (>-trans 2>1 1>0))))
--                        (refl ((ub + ℕ2ℝ 5) * r₁))

--          p₂₆-helper : ub + ℕ2ℝ 5 < ℕ2ℝ 5 + ℕ2ℝ 5 → (ub + ℕ2ℝ 5) * r₁ < ℕ2ℝ 5 + ℕ2ℝ 5
--          p₂₆-helper h₈ = subst₂ (λ t₁ t₂ → t₁ < t₂) p-helper (refl (ℕ2ℝ 5 + ℕ2ℝ 5)) h₈

--            where
--             p-helper : ub + ℕ2ℝ 5 ≡ (ub + ℕ2ℝ 5) * r₁
--             p-helper = subst (λ w → ub + ℕ2ℝ 5 ≡ w) (≡-sym (*-neut (ub + ℕ2ℝ 5))) (refl (ub + ℕ2ℝ 5))

-- LbB5 : ∃ᵣ (λ x → Lub B (ℕ2ℝ 5))
-- LbB5 = exist (ℕ2ℝ 5) (UBB5 , UBB5≤ub)

-------------------------------------------------------------------------

-- Completeness Examples

example-1 : ∃ᵣ (λ sup → Lub A sup)
example-1 = completeness A bar (exist (ℕ2ℝ 2) (inj₂ (refl (ℕ2ℝ 2))))

example-2 : ∃ᵣ (λ sup → Lub B sup)
example-2 = completeness B bar1 (exist (ℕ2ℝ 4) (<-+-left (<-+-left (<-+-left (>-to-< (subst₂ (λ t₁ t₂ → t₁ > t₂)
            (refl (ℕ2ℝ 2)) (≡-sym (+-neut r₁)) 2>1))))))
