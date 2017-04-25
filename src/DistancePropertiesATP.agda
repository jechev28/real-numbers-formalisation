-- Properties of distance

module DistancePropertiesATP where

open import DistanceDefinition
open import AbsoluteValueProperties
open import Properties
open import RealNumbersAxioms

postulate dis-des : (x y z w : ℝ) → dist (x + z) (y + w) ≤ dist x y + dist z w
{-# ATP prove dis-des abs-tri #-}
