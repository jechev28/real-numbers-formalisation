module PoProperties where

open import Axioms
open import EqProperties
open import Logic
open import Properties

≥-refl : {x : ℝ} → x ≥ x
≥-refl {x} = inj₂ (refl x)

≥-trans : {x y z : ℝ} → x ≥ y → y ≥ z → x ≥ z
≥-trans {x} {y} {z} x≥y y≥z = case prf₁ prf₂ x≥y
  where
    prf₁ : x > y → (x > z) ∨ (x ≡ z)
    prf₁ x>y = case prf₁₁ prf₁₂ y≥z
     where
       prf₁₁ : y > z → (x > z) ∨ (x ≡ z)
       prf₁₁ y>z = inj₁ (>-trans x>y y>z)

       prf₁₂ : y ≡ z → (x > z) ∨ (x ≡ z)
       prf₁₂ y≡z = inj₁ (>-≡→>-2 x>y y≡z)

    prf₂ : x ≡ y → (x > z) ∨ (x ≡ z)
    prf₂ x≡y = case prf₂₁ prf₂₂ y≥z
     where
       prf₂₁ : y > z → (x > z) ∨ (x ≡ z)
       prf₂₁ y>z = inj₁ (≡->→> x≡y y>z)

       prf₂₂ : y ≡ z → (x > z) ∨ (x ≡ z)
       prf₂₂ y≡z = inj₂ (≡-trans x≡y y≡z)

≤-+-left : {x y z : ℝ} → x ≤ y → z + x ≤ z + y
≤-+-left {x} {y} {z} x≤y = case prf₁ prf₂ x≤y

  where
   prf₁ : x < y → z + x < z + y ∨ z + x ≡ z + y
   prf₁ x<y = inj₁ (<-+-left x<y)

   prf₂ : x ≡ y → z + x < z + y ∨ z + x ≡ z + y
   prf₂ x=y = inj₂ (≡-+-cong-l x=y)

≤-+-right : {x y z : ℝ} → x ≤ y → x + z ≤ y + z
≤-+-right {x} {y} {z} x≤y = case prf₁ prf₂ x≤y

  where
   prf₁ : x < y → x + z < y + z ∨ x + z ≡ y + z
   prf₁ x<y = inj₁ (<-+-right x<y)

   prf₂ : x ≡ y → x + z < y + z ∨ x + z ≡ y + z
   prf₂ x=y = inj₂ (≡-+-cong-r x=y)

≤-trans : {x y z : ℝ} → x ≤ y → y ≤ z → x ≤ z
≤-trans {x} {y} {z} x≤y y≤z = case prf₁ prf₂ x≤y

  where
    prf₁ : x < y → (x < z) ∨ (x ≡ z)
    prf₁ x<y = case prf₁₁ prf₁₂ y≤z
     where
       prf₁₁ : y < z → (x < z) ∨ (x ≡ z)
       prf₁₁ y<z = inj₁ (<-trans x<y y<z)

       prf₁₂ : y ≡ z → (x < z) ∨ (x ≡ z)
       prf₁₂ y≡z = inj₁ (<-=-→-< x<y y≡z)

    prf₂ : x ≡ y → (x < z) ∨ (x ≡ z)
    prf₂ x≡y = case prf₂₁ prf₂₂ y≤z
     where
       prf₂₁ : y < z → (x < z) ∨ (x ≡ z)
       prf₂₁ y<z = inj₁ (≡-<→< x≡y y<z)

       prf₂₂ : y ≡ z → (x < z) ∨ (x ≡ z)
       prf₂₂ y≡z = inj₂ (≡-trans x≡y y≡z)

≤-≤-+ : {x y z w : ℝ} → x ≤ y → z ≤ w → x + z ≤ y + w
≤-≤-+ {x} {y} {z} {w} x≤y z≤w = ≤-trans (≤-+-right x≤y) (≤-+-left z≤w)
