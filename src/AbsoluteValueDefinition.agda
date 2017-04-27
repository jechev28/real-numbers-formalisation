
module AbsoluteValueDefinition where

open import RealNumbersAxioms
open import LogicDefinitions
open import OrderedFieldProperties

-- Absolute value definition.

abs : ℝ → ℝ
abs x with x<0∨x≥0 x
... | inj₁ _ = - x
... | inj₂ _ = x
