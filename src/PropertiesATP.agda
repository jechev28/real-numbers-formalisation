
module PropertiesATP where

open import RealNumbersAxioms
open import LogicDefinitions

postulate ≡-<-trans : {x y z : ℝ} → x ≡ y → y < z → x < z
{-# ATP prove ≡-<-trans #-}

postulate 01-dichotomy : {x y : ℝ} → x ≢ y → (x > y) ∨ (x < y)
{-# ATP prove 01-dichotomy #-}

postulate ≡-+-cong-r : {x y z : ℝ} → x ≡ y → x + z ≡ y + z
{-# ATP prove ≡-+-cong-r #-}

postulate ≡-*-cong-r : {x y : ℝ} (z : ℝ)→ x ≡ y → x * z ≡ y * z
{-# ATP prove ≡-*-cong-r #-}

postulate ≡-*-cong-l : {x y : ℝ} (z : ℝ) → x ≡ y → z * x ≡ z * y
{-# ATP prove ≡-*-cong-l #-}

postulate >-+-cong-r : {x y z : ℝ} → x > y → x + z > y + z
{-# ATP prove >-+-cong-r #-}

postulate <-to-minus : {x y : ℝ} → y < x → x - y > r₀
{-# ATP prove <-to-minus #-}

postulate minus-to-< : {x y : ℝ} → x - y > r₀ → y < x
{-# ATP prove minus-to-< #-}

postulate *-dist-minus : (x y z : ℝ) → x * (y - z) ≡ x * y - x * z
{-# ATP prove *-dist-minus #-}

postulate >-∧-*-cong-l : {x y z : ℝ} → (x > y) ∧ (z > r₀) → z * x > z * y
{-# ATP prove >-∧-*-cong-l <-to-minus minus-to-< *-dist-minus #-}

postulate >-*-cong-l : {x y z : ℝ} → z > r₀ → x > y → z * x > z * y
{-# ATP prove >-*-cong-l >-∧-*-cong-l #-}

postulate >-*-cong-r : {x y z : ℝ} → z > r₀ → x > y → x * z > y * z
{-# ATP prove >-*-cong-r >-∧-*-cong-l #-}

postulate >-∧-*-cong-r : {x y z : ℝ} → (x > y) ∧ (z > r₀) → (x * z) > (y * z)
{-# ATP prove >-∧-*-cong-r >-*-cong-r #-}

postulate >->-cong-r : {x y z w : ℝ} → (x > y) ∧ (y > r₀) → (z > w) ∧ (w > r₀) → x * z > y * w
{-# ATP prove >->-cong-r >-∧-*-cong-r >-∧-*-cong-l #-}

postulate ≥-+-cong-r : {x y z : ℝ} → x ≥ y → x + z ≥ y + z
{-# ATP prove ≥-+-cong-r ≡-+-cong-r >-+-cong-r #-}

postulate ≥-*-cong-r : {x y z : ℝ} → z > r₀ → x ≥ y → x * z ≥ y * z
{-# ATP prove ≥-*-cong-r >-*-cong-r ≡-*-cong-r #-}

postulate ≡-+-cancel-r : {x y z : ℝ} → x + z ≡ y + z → x ≡ y
{-# ATP prove ≡-+-cancel-r #-}

postulate ≡-*-cancel-r : {x y z : ℝ} → z ≢ r₀ → x * z ≡ y * z → x ≡ y
{-# ATP prove ≡-*-cancel-r #-}

postulate >-+-cancel-r : {x y z : ℝ} → x + z > y + z → x > y
{-# ATP prove >-+-cancel-r >-+-cong-r #-}

postulate *-right-zero : {x : ℝ} → x * r₀ ≡ r₀
{-# ATP prove *-right-zero #-}

postulate >-to-< : {x y : ℝ} → x > y → y < x
{-# ATP prove >-to-< #-}

postulate <-to-> : {x y : ℝ} → x < y → y > x
{-# ATP prove <-to-> #-}

postulate <-trans : {x y z : ℝ} → x < y → y < z → x < z
{-# ATP prove <-trans #-}

postulate <-+-cong-l : {x y z : ℝ} → x < y → z + x < z + y
{-# ATP prove <-+-cong-l #-}

postulate <-+-cong-r : {x y z : ℝ} → x < y → x + z < y + z
{-# ATP prove <-+-cong-r #-}

postulate ≤-to-≥ : {x y : ℝ} → x ≤ y → y ≥ x
{-# ATP prove ≤-to-≥ #-}

postulate *-left-zero : {x : ℝ} → r₀ * x ≡ r₀
{-# ATP prove *-left-zero #-}

postulate >-r₀-produc : {x : ℝ} → x > r₀ → x * x > r₀
{-# ATP prove >-r₀-produc #-}

postulate <-r₀-produc : {x : ℝ} → x < r₀ → x * x > r₀
{-# ATP prove <-r₀-produc #-}

postulate *-∨-zero : {x y : ℝ} → (x ≡ r₀) ∨ (y ≡ r₀) → x * y ≡ r₀
{-# ATP prove *-∨-zero #-}

postulate *-negation : {x : ℝ} → - x ≡ (- r₁) * x
{-# ATP prove *-negation #-}

postulate mul-xy : {x y : ℝ} → (- x) * y ≡ - (x * y)
{-# ATP prove mul-xy #-}

postulate mulx-y : {x y : ℝ} → x * (- y) ≡ - (x * y)
{-# ATP prove mulx-y #-}

postulate mul--x : {x : ℝ} → - (- x) ≡ x
{-# ATP prove mul--x #-}

postulate mul-x+y : ∀ {x y} → - (x + y) ≡ - x + (- y)
{-# ATP prove mul-x+y #-}

postulate mul-x-y : {x y : ℝ} → (- x) * (- y) ≡ x * y
{-# ATP prove mul-x-y #-}

-- -- E is not able to prove ownership

postulate ─-neut : {x : ℝ} → r₀ - x ≡ - x
{-# ATP prove ─-neut #-}

postulate opp-<-> : {x : ℝ} → x < r₀ → - x > r₀
{-# ATP prove opp-<-> #-}

postulate mulxx : {x : ℝ} → x < r₀ → x * x > r₀
{-# ATP prove mulxx #-}

postulate mulxx>0 : {x y : ℝ} → (x > r₀) ∨ (x < r₀) → x * x > r₀
{-# ATP prove mulxx>0 >-r₀-produc <-r₀-produc #-}

postulate <-*-cong-l : {x y z : ℝ} → z > r₀ → x < y → z * x < z * y
{-# ATP prove <-*-cong-l >-*-cong-l #-}

postulate r₀-sqr : sqr r₀ ≡ r₀
{-# ATP prove r₀-sqr #-}

postulate r₁-sqr : sqr r₁ ≡ r₁
{-# ATP prove r₁-sqr #-}

postulate >-sqr : {x : ℝ} → ¬ (x ≡ r₀) → sqr x > r₀
{-# ATP prove >-sqr #-}

postulate 1>0 : r₁ > r₀
{-# ATP prove 1>0 #-}

postulate 1≥0 : r₁ ≥ r₀
{-# ATP prove 1≥0 #-}

postulate x+1>x : (x : ℝ) → x + r₁ > x
{-# ATP prove x+1>x #-}

postulate x<x+1 : (x : ℝ) → x < x + r₁
{-# ATP prove x<x+1 #-}

postulate >-inve-r₀ : {x : ℝ} → x > r₀ → x ⁻¹ > r₀
{-# ATP prove >-inve-r₀ #-}

postulate >-*-cancel-r : {x y z : ℝ} → z > r₀ → x * z > y * z → x > y
{-# ATP prove >-*-cancel-r >-*-cong-r #-}

postulate >-*-cancel-l : {x y z : ℝ} → z > r₀ → z * x > z * y → x > y
{-# ATP prove >-*-cancel-l >-*-cancel-r #-}

postulate ≥-+-cancel-r : {x y z : ℝ} → x + z ≥ y + z → x ≥ y
{-# ATP prove ≥-+-cancel-r #-}

postulate *-dist-r : {x y z : ℝ} → (y + z) * x ≡ y * x + z * x
{-# ATP prove *-dist-r #-}

postulate *-inve-product≡1 : {x y : ℝ} → ¬ (x ≡ r₀) → ¬ (y ≡ r₀) → (x ⁻¹ * y ⁻¹) * (x * y) ≡ r₁
{-# ATP prove *-inve-product≡1 #-}

postulate *-inve-product : {x y : ℝ} → ¬ (x ≡ r₀) → ¬ (y ≡ r₀) → ¬ ((x * y) ≡ r₀) → (x * y) ⁻¹ ≡ x ⁻¹ * y ⁻¹
{-# ATP prove *-inve-product *-inve-product≡1 #-}

-- One is equal to its multiplicative inverse.

postulate 1≡1⁻¹ : r₁ ≡ r₁ ⁻¹
{-# ATP prove 1≡1⁻¹ #-}

-- Pending

-- postulate 2>1 : ℕ2ℝ 2 > r₁
-- {-# ATP prove 2>1 #-}

-- postulate 2x=x+x : {x : ℝ} → (ℕ2ℝ 2) * x ≡ x + x
-- {-# ATP prove 2x=x+x #-}

-- Application of the Archimedean property.
-- D.Bridges-1999-Page-105-Exercise-25.

-- Pending

-- postulate nx>y : (x y : ℝ) → x > r₀ → ∃ₙ (λ n → ℕ2ℝ n * x > y)
-- {-# ATP prove nx>y #-}

