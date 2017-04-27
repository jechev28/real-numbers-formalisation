
module EqReasoning where

open import EqProperties
open import RealNumbersAxioms

infixr 2 _≡⟨_⟩_
infix  3 _∎

_≡⟨_⟩_ : ∀ x {y z} → x ≡ y → y ≡ z → x ≡ z
_ ≡⟨ x≡y ⟩ y≡z = ≡-trans x≡y y≡z

_∎ : ∀ x → x ≡ x
_∎ x = refl x
