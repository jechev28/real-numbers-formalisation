module Axioms where

open import Logic
open import Nat

-- Basics constants.

postulate
  ℝ   : Set
  r₀  : ℝ
  r₁  : ℝ
  _+_ : ℝ → ℝ → ℝ
  -_  : ℝ → ℝ
  _*_ : ℝ → ℝ → ℝ
  _⁻¹  : ℝ → ℝ

infix  5 ∃ᵣ
infixl 6 _+_
infixl 7 _*_
infix  8 _⁻¹
infixl 4 _≡_
infix  8 -_
infix  8 sqr

-- Equality.
data _≡_ : ℝ → ℝ → Set where
  refl : (x : ℝ) → x ≡ x

_≢_ :  ℝ → ℝ → Set
x ≢ y = ¬ x ≡ y

{-# ATP definition _≢_ #-}

-- Field axioms

-- Addition axioms.

postulate
  +-comm : (x y : ℝ)   →     x + y ≡ y + x
  +-asso : (x y z : ℝ) → x + y + z ≡ x + (y + z)
  +-neut : (x : ℝ)     →    x + r₀ ≡ x
  +-inve : (x : ℝ)     → x + (- x) ≡ r₀

{-# ATP axiom +-comm +-asso +-neut +-inve #-}

-- Multiplication axioms.

postulate
  *-comm : (x y : ℝ)   →     x * y ≡ y * x
  *-asso : (x y z : ℝ) → (x * y) * z ≡ x * (y * z)
  *-neut : (x : ℝ)     →    x * r₁ ≡ x
  *-inve : (x : ℝ)     → x ≢ r₀ → x * (x ⁻¹) ≡ r₁

{-# ATP axiom *-comm *-asso *-neut *-inve #-}

-- Distributivity axiom.

postulate
  *-dist : (x y z : ℝ) → x * (y + z) ≡ x * y + x * z

{-# ATP axiom *-dist #-}

-- Order axioms and definitions.

infixl 4 _>_ _≥_ _<_ _≤_ _≮_ _≯_
infixl 6 _-_

postulate
  _>_ : ℝ → ℝ → Set

postulate
  >-trans    : {x y z : ℝ} → x > y  → y > z → x > z
  >-+-left   : {x y z : ℝ} → x > y  → z + x > z + y
  >-∧-*      : {x y : ℝ}   → (x > r₀) ∧ (y > r₀) → x * y > r₀

{-# ATP axiom >-trans >-+-left >-∧-* #-}

-- Substraction.

_-_ : ℝ → ℝ → ℝ
x - y = x + (- y)

{-# ATP definition _-_ #-}

_<_ : ℝ → ℝ → Set
y < x = x > y

{-# ATP definition _<_ #-}

_≥_ : ℝ → ℝ → Set
x ≥ y = (x > y) ∨ (x ≡ y)

{-# ATP definition _≥_ #-}

_≤_ : ℝ → ℝ → Set
x ≤ y = (x < y) ∨ (x ≡ y)

{-# ATP definition _≤_ #-}

_≮_ : ℝ → ℝ → Set
x ≮ y = ¬ x < y

{-# ATP definition _≮_ #-}

_≯_ : ℝ → ℝ → Set
x ≯ y = ¬ x > y

{-# ATP definition _≯_ #-}

_≰_ : ℝ → ℝ → Set
x ≰ y = ¬ x ≤ y

{-# ATP definition _≰_ #-}

_≱_ : ℝ → ℝ → Set
x ≱ y = ¬ x ≥ y

{-# ATP definition _≱_ #-}

sqr : ℝ → ℝ
sqr x = x * x

{-# ATP definition sqr #-}

-- Trichotomy
-- Exactly one of the relations x = y, x < y, x > y holds. (Apostol-1974)

-- From Wikipedia
-- (https://en.wikipedia.org/wiki/Trichotomy_(mathematics),
-- 2016-11-28):
-- In mathematical notation, this is
--
--   ∀ x ∈ X ∀ y ∈ X ( ( x < y ∧ ¬ ( y < x ) ∧ ¬ ( x = y ) ) ∨
--                       ( ¬ ( x < y ) ∧ y < x ∧ ¬ ( x = y ) ) ∨
--                       ( ¬ ( x < y ) ∧ ¬ ( y < x ) ∧ x = y )
--                   )

postulate
  trichotomy : (x y : ℝ) → ((x > y) ∧ ¬ (x ≡ y) ∧ ¬ (x < y)) ∨
                            (¬ (x > y) ∧ (x ≡ y) ∧ ¬ (x < y)) ∨
                            (¬ (x > y) ∧ ¬ (x ≡ y) ∧ (x < y))

{-# ATP axiom trichotomy #-}

-- The Nontriviality Assumption (1≢0).
-- Real Analysis. H. L. Royden and P.M. Fitzpatrick. Fourth edition 2010.

postulate
  1≢0 : r₁ ≢ r₀

{-# ATP axiom 1≢0 #-}

-- Injection from N to R.

ℕ2ℝ : ℕ → ℝ
ℕ2ℝ zero     = r₀
ℕ2ℝ (succ n) = r₁ + ℕ2ℝ n

-- Existential.

data ∃ᵣ (P : ℝ → Set) : Set where
  exist : (x : ℝ) → P x → ∃ᵣ P

∃ᵣ-proj₁ : (P : ℝ → Set) → ∃ᵣ P → ℝ
∃ᵣ-proj₁ P (exist x _) = x

∃ᵣ-proj₂ : (P : ℝ → Set) → (h : ∃ᵣ P) → P (∃ᵣ-proj₁ P h)
∃ᵣ-proj₂ P (exist x Px) = Px

data ∃ₙ (P : ℕ → Set) : Set where
  exist : (n : ℕ) → P n → ∃ₙ P

-- Adapted from Coq proof assistant (8.4pl4). https://coq.inria.fr/distrib/current/stdlib/Coq.Reals.Raxioms.html

-- Definitions.

UpperBound : (ℝ → Set) → ℝ → Set
UpperBound E ub = (x : ℝ) → E x → x ≤ ub

Bound : (ℝ → Set) → Set
Bound E = ∃ᵣ (λ ub → UpperBound E ub)

Lub : (ℝ → Set) → ℝ → Set
Lub E sup = (UpperBound E sup) ∧ ((ub : ℝ) → UpperBound E ub → sup ≤ ub)

-- Axiom Completeness.

postulate
  completeness : (E : ℝ → Set) → Bound E → ∃ᵣ (λ x → E x) → ∃ᵣ (λ sup → Lub E sup)
