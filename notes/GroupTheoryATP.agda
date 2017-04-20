module  GroupTheoryATP where

infix 8  _⁻¹
infixl 7 _*_
infixl 4 _≡_

postulate
  G   : Set
  ε   : G
  _*_ : G → G → G
  _⁻¹ : G → G

-- Equality.
data _≡_ : G → G → Set where
  refl : {x : G} → x ≡ x

≡-sym : {x y : G} → x ≡ y → y ≡ x
≡-sym (refl) = refl

subst : (P : G → Set) → {x y : G} → x ≡ y → P x → P y
subst P (refl) Px = Px

≡-trans : {x y z : G} → x ≡ y → y ≡ z → x ≡ z
≡-trans (refl) (refl) = refl

postulate
  assoc        : ∀ a b c → a * b * c ≡ a * (b * c)
  leftIdentity : ∀ a → ε * a ≡ a
  leftInverse  : ∀ a → a ⁻¹ * a ≡ ε
{-# ATP axiom assoc leftIdentity leftInverse #-}

-- rightIdentityUnique : ∀ r → (∀ a → a * r ≡ a) → r ≡ ε
-- rightIdentityUnique r h = ≡-trans (≡-sym (leftIdentity r)) (h ε)

postulate rightIdentity : ∀ a → a * ε ≡ a
{-# ATP prove rightIdentity #-}

postulate leftCancellation : ∀ {a b c} → a * b ≡ a * c → b ≡ c
{-# ATP prove leftCancellation #-}

-- postulate rightIdentityUnique : ∀ r → (∀ a → a * r ≡ a) → r ≡ ε
-- {-# ATP prove rightIdentityUnique #-}
