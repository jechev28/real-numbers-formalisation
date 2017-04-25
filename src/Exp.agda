
module Exp where

open import RealNumbersAxioms
open import EqProperties
open import EqReasoning
open import LogicDefinitions
open import Nat
open import Properties

infixr 8 _^_

_^_ : ℝ → ℕ → ℝ
x ^ zero     = r₁
x ^ (succ n) = x * (x ^ n)

x^1≡x : (x : ℝ) → x ^ (succ zero) ≡ x
x^1≡x x = *-neut x

1^n : (n : ℕ) → r₁ ^ n ≡ r₁
1^n zero     = refl r₁
1^n (succ n) = p-helper

  where
    p-helper : r₁ * r₁ ^ n ≡ r₁
    p-helper =
     r₁ * r₁ ^ n ≡⟨ *-comm r₁ (r₁ ^ n) ⟩
     r₁ ^ n * r₁ ≡⟨ *-neut (r₁ ^ n) ⟩
     r₁ ^ n      ≡⟨ 1^n n ⟩
     r₁          ∎

-- Rules of exponentiation.

x^sum : (x : ℝ) (m n : ℕ) → x ^ (m +ₙ n) ≡ (x ^ m) * (x ^ n)
x^sum x zero n = p-helper

  where
    p-helper : x ^ n ≡ r₁ * x ^ n
    p-helper =
     x ^ n      ≡⟨ ≡-sym (*-neut (x ^ n)) ⟩
     x ^ n * r₁ ≡⟨ *-comm (x ^ n) r₁ ⟩
     r₁ * x ^ n ∎

x^sum x (succ m) n = p-helper

  where
    p-helper : x * x ^ (m +ₙ n) ≡ x * x ^ m * x ^ n
    p-helper =
     x * x ^ (m +ₙ n)    ≡⟨ ≡-*-cong-l x (x^sum x m n) ⟩
     x * (x ^ m * x ^ n) ≡⟨ ≡-sym (*-asso x (x ^ m) (x ^ n)) ⟩
     x * x ^ m * x ^ n   ∎

x^mul : (x y : ℝ) (m : ℕ) → (x * y) ^ m ≡ (x ^ m) * (y ^ m)
x^mul x y zero = ≡-sym p-helper

  where
    p-helper : r₁ * r₁ ≡ r₁
    p-helper =
     r₁ * r₁    ≡⟨ subst (λ w → r₁ * r₁ ≡ r₁ * w) 1≡1⁻¹ (refl (r₁ * r₁)) ⟩
     r₁ * r₁ ⁻¹ ≡⟨ *-inve r₁ 1≢0 ⟩
     r₁         ∎

x^mul x y (succ m) = p-helper

  where
    p-helper : x * y * (x * y) ^ m ≡ x * x ^ m * (y * y ^ m)
    p-helper =
      x * y * (x * y) ^ m
       ≡⟨ subst (λ w → x * y * (x * y) ^ m ≡ x * y * w) (x^mul x y m) (refl (x * y * (x * y) ^ m)) ⟩
      x * y * (x ^ m * y ^ m)
       ≡⟨ *-asso x y (x ^ m * y ^ m) ⟩
      x * (y * (x ^ m * y ^ m))
       ≡⟨ subst (λ w → x * (y * (x ^ m * y ^ m)) ≡ x * w) (≡-sym (*-asso y (x ^ m) (y ^ m))) (refl (x * (y * (x ^ m * y ^ m)))) ⟩
      x * (y * x ^ m * y ^ m)
       ≡⟨ subst (λ w → x * (y * x ^ m * y ^ m) ≡ x * (w * y ^ m)) (*-comm y (x ^ m)) (refl (x * (y * x ^ m * y ^ m))) ⟩
      x * (x ^ m * y * y ^ m)
       ≡⟨ subst (λ w → x * (x ^ m * y * y ^ m) ≡ x * w) (*-asso (x ^ m) y (y ^ m)) (refl (x * (x ^ m * y * y ^ m))) ⟩
      x * (x ^ m * (y * y ^ m))
       ≡⟨ ≡-sym (*-asso x (x ^ m) (y * y ^ m)) ⟩
      x * x ^ m * (y * y ^ m) ∎

x^m^n : (x : ℝ) (m n : ℕ) → (x ^ m) ^ n ≡ x ^ (m *ₙ n)
x^m^n x zero n = 1^n n
x^m^n x (succ m) n = p-helper

  where
    p-helper : (x * x ^ m) ^ n ≡ x ^ (n +ₙ (m *ₙ n))
    p-helper =
     (x * x ^ m) ^ n
       ≡⟨ x^mul x (x ^ m) n ⟩
     x ^ n * (x ^ m) ^ n
       ≡⟨ subst (λ w → x ^ n * (x ^ m) ^ n ≡ x ^ n * w) (x^m^n x m n) (refl (x ^ n * (x ^ m) ^ n)) ⟩
     x ^ n * x ^ (m *ₙ n)
       ≡⟨ ≡-sym (x^sum x n (m *ₙ n)) ⟩
     x ^ (n +ₙ (m *ₙ n)) ∎
