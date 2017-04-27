
module AbsoluteValueDefinition where

open import LogicDefinitions
open import OrderedFieldProperties
open import RealNumbersAxioms

-- Absolute value definition.

abs : ℝ → ℝ
abs x with x<0∨x≥0 x
... | inj₁ _ = - x
... | inj₂ _ = x
