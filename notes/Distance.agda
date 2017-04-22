module Distance where

open import AbsoluteValue
open import Axioms
open import EqReasoning
open import EqProperties
open import Logic
open import Nat
open import Properties

-- Previous properties.

-x=0→x=0 : (x : ℝ) → - x ≡ r₀ → x ≡ r₀
-x=0→x=0 x -x=0 = ≡-*-cancel-r (<→≢(x>0→-x<0 1>0)) p-helper

  where
   p-helper : x * - r₁ ≡ r₀ * - r₁
   p-helper =
     x * - r₁   ≡⟨ *-comm x (- r₁) ⟩
     - r₁ * x   ≡⟨ mul-xy ⟩
     - (r₁ * x) ≡⟨ subst (λ w → - (r₁ * x) ≡ - w) (*-comm r₁ x) (refl (- (r₁ * x))) ⟩
     - (x * r₁) ≡⟨ subst (λ w → - (x * r₁) ≡ - w) (*-neut x) (refl (- (x * r₁))) ⟩
     - x        ≡⟨ -x=0 ⟩
     r₀         ≡⟨ ≡-sym *-right-zero ⟩
     - r₁ * r₀  ≡⟨ *-comm (- r₁) r₀ ⟩
     r₀ * - r₁      ∎

x-y=0→x=y : (x y : ℝ) → x - y ≡ r₀ → x ≡ y
x-y=0→x=y x y h =
     x             ≡⟨ ≡-sym (+-neut x) ⟩
     x + r₀        ≡⟨ subst (λ w → x + r₀ ≡ x + w) (≡-sym (+-inve y)) (refl (x + r₀)) ⟩
     x + (y - y)   ≡⟨ subst (λ w → x + (y - y) ≡ x + w) (+-comm y (- y)) (refl (x + (y - y))) ⟩
     x + (- y + y) ≡⟨ ≡-sym (+-asso x (- y) y) ⟩
     (x - y) + y   ≡⟨ subst (λ w → (x - y) + y ≡ w + y) h (refl ((x - y) + y)) ⟩
     r₀ + y        ≡⟨ +-comm r₀ y ⟩
     y + r₀        ≡⟨ +-neut y ⟩
     y      ∎

-- Distance (or metric) between two points.
-- Mathematical Analysis. Apostol, Tom. M. 1974. Pag. 60.

dist : ℝ → ℝ → ℝ
dist x y = abs (x - y)

d-refl : (x y : ℝ) → (dist x y ≡ r₀) ↔ (x ≡ y)
d-refl x y = d-refl-r , d-refl-l

  where
   d-refl-r : (dist x y ≡ r₀) → (x ≡ y)
   d-refl-r h with case-abs (x - y)
   ... | inj₁ p = ⊥-elim (≡→≮ (-x=0→x=0 (x - y) h) (>-to-< p))
   ... | inj₂ p = x-y=0→x=y x y h

   d-refl-l : (x ≡ y) → (dist x y ≡ r₀)
   d-refl-l x=y =
     dist x y    ≡⟨ subst (λ w → dist x y ≡ abs (x - w)) (≡-sym x=y) (refl (dist x y)) ⟩
     abs (x - x) ≡⟨ subst (λ w → abs (x - x) ≡ abs w) (+-inve x) (refl (abs (x - x))) ⟩
     abs r₀      ≡⟨ abs-0 ⟩
     r₀      ∎
