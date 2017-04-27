-- Properties of distance

module DistancePropertiesATP where

open import AbsoluteValueProperties
open import DistanceDefinition
open import LogicDefinitions
open import RealNumbersAxioms

postulate d-refl : (x y : ℝ) → (dist x y ≡ r₀) ↔ (x ≡ y)
{-# ATP prove d-refl abs-0 x>0→absx=x x<0→absx=-x #-}

postulate d-pos : (x y : ℝ) → dist x y ≥ r₀
{-# ATP prove d-pos abs-0 x>0→absx=x x<0→absx=-x #-}

postulate d-sym : (x y : ℝ) → dist x y ≡ dist y x
{-# ATP prove d-sym abs-0 x>0→absx=x x<0→absx=-x #-}

postulate d-tri : (x y z : ℝ) → dist x y ≤ dist x z + dist z y
{-# ATP prove d-tri abs-tri #-}

postulate dis-des : (x y z w : ℝ) → dist (x + z) (y + w) ≤ dist x y + dist z w
{-# ATP prove dis-des abs-tri #-}
