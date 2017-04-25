
module DistanceDefinition where

open import AbsoluteValueDefinition
open import RealNumbersAxioms

-- Distance (or metric) between two points.
-- Mathematical Analysis. Apostol, Tom. M. 1974. p. 60.

dist : ℝ → ℝ → ℝ
dist x y = abs (x - y)
