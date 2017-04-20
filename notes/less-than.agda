module less-than where

open import Axioms
open import Logic
open import Nat
open import Properties
open import EqProperties
open import EqReasoning

-- _<_ : ℝ → ℝ → Set    -- As defined by Axioms.agda
-- y < x = x - y > r₀

_<'_ : ℝ → ℝ → Set     -- As defined by Coq 8.4pl4
y <' x = x > y

-- <' ≡ <

<'≡< : {x y : ℝ} → y <' x → x - y > r₀
<'≡< {x} {y} y<'x = >-+-cancel-r (p1-helper (>-+-cong-r y<'x))

  where
   p1-helper : x + r₀ > y + r₀ → x - y + y > r₀ + y
   p1-helper h1 = subst₂ (λ t₁ t₂ → t₁ > t₂) p11-helper (+-comm y r₀) h1

    where
     p11-helper : x + r₀ ≡ x - y + y
     p11-helper =
       x + r₀ ≡⟨ subst (λ w → x + r₀ ≡ x + w) (≡-sym (+-inve y)) (refl (x + r₀)) ⟩
       x + (y - y) ≡⟨ subst (λ w → x + (y - y) ≡ x + w) (+-comm y (- y)) (refl (x + (y - y))) ⟩
       x + (- y + y) ≡⟨ ≡-sym (+-asso x (- y) y) ⟩
       x - y + y  ∎
