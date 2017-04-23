module PoReasoning where
open import Axioms
open import PoProperties

infixr 2 _≥⟨_⟩_
infix  3 _▲

_≥⟨_⟩_ : ∀ x {y z} → x ≥ y → y ≥ z → x ≥ z
_ ≥⟨ x≥y ⟩ y≥z = ≥-trans x≥y y≥z

_▲ : ∀ x → x ≥ x
_▲ _ = ≥-refl
