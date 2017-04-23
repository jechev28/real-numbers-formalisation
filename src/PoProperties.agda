module PoProperties where

open import Axioms
open import DemorganLaws
open import EqProperties
open import Logic
open import Properties

≥-refl : {x : ℝ} → x ≥ x
≥-refl {x} = inj₂ (refl x)

≥-trans : {x y z : ℝ} → x ≥ y → y ≥ z → x ≥ z
≥-trans {x} {y} {z} x≥y y≥z = case prf1 prf2 x≥y
  where
    prf1 : x > y → (x > z) ∨ (x ≡ z)
    prf1 x>y = case prf11 prf12 y≥z
     where
       prf11 : y > z → (x > z) ∨ (x ≡ z)
       prf11 y>z = inj₁ (>-trans x>y y>z)

       prf12 : y ≡ z → (x > z) ∨ (x ≡ z)
       prf12 y≡z = inj₁ (>-≡→>-2 x>y y≡z)

    prf2 : x ≡ y → (x > z) ∨ (x ≡ z)
    prf2 x≡y = case prf21 prf22 y≥z
     where
       prf21 : y > z → (x > z) ∨ (x ≡ z)
       prf21 y>z = inj₁ (≡->→> x≡y y>z)

       prf22 : y ≡ z → (x > z) ∨ (x ≡ z)
       prf22 y≡z = inj₂ (≡-trans x≡y y≡z)

≤-+-left : {x y z : ℝ} → x ≤ y → z + x ≤ z + y
≤-+-left {x} {y} {z} x≤y = case prf1 prf2 x≤y

  where
   prf1 : x < y → z + x < z + y ∨ z + x ≡ z + y
   prf1 x<y = inj₁ (<-+-left x<y)

   prf2 : x ≡ y → z + x < z + y ∨ z + x ≡ z + y
   prf2 x=y = inj₂ (≡-+-cong-l x=y)

≤-+-right : {x y z : ℝ} → x ≤ y → x + z ≤ y + z
≤-+-right {x} {y} {z} x≤y = case prf1 prf2 x≤y

  where
   prf1 : x < y → x + z < y + z ∨ x + z ≡ y + z
   prf1 x<y = inj₁ (<-+-right x<y)

   prf2 : x ≡ y → x + z < y + z ∨ x + z ≡ y + z
   prf2 x=y = inj₂ (≡-+-cong-r x=y)

≤-trans : {x y z : ℝ} → x ≤ y → y ≤ z → x ≤ z
≤-trans {x} {y} {z} x≤y y≤z = case prf1 prf2 x≤y

  where
    prf1 : x < y → (x < z) ∨ (x ≡ z)
    prf1 x<y = case prf11 prf12 y≤z
     where
       prf11 : y < z → (x < z) ∨ (x ≡ z)
       prf11 y<z = inj₁ (<-trans x<y y<z)

       prf12 : y ≡ z → (x < z) ∨ (x ≡ z)
       prf12 y≡z = inj₁ (<-=-→-< x<y y≡z)

    prf2 : x ≡ y → (x < z) ∨ (x ≡ z)
    prf2 x≡y = case prf21 prf22 y≤z
     where
       prf21 : y < z → (x < z) ∨ (x ≡ z)
       prf21 y<z = inj₁ (≡-<→< x≡y y<z)

       prf22 : y ≡ z → (x < z) ∨ (x ≡ z)
       prf22 y≡z = inj₂ (≡-trans x≡y y≡z)

≤-≤-+ : {x y z w : ℝ} → x ≤ y → z ≤ w → x + z ≤ y + w
≤-≤-+ {x} {y} {z} {w} x≤y z≤w = ≤-trans (≤-+-right x≤y) (≤-+-left z≤w)
