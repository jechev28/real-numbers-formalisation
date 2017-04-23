module PoProperties where

open import Axioms
open import DemorganLaws
open import EqProperties
open import Logic
open import Properties

>-≡→>-2 : {x y z : ℝ} → x > y → y ≡ z → x > z
>-≡→>-2 x>y (refl x) = x>y

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
