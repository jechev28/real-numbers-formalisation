module NExp where

infixl 4 _≡_
infixl 6 _+_
infixl 7 _*_
infixr 8 _^_

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

data _≡_ : ℕ → ℕ → Set where
  refl : {x : ℕ} → x ≡ x

≡-sym : {x y : ℕ} → x ≡ y → y ≡ x
≡-sym refl = refl

≡-trans : {x y z : ℕ} → x ≡ y → y ≡ z → x ≡ z
≡-trans refl refl = refl

subst : (P : ℕ → Set) → {x y : ℕ} → x ≡ y → P x → P y
subst P refl Px = Px

infixr 2 _≡⟨_⟩_
infix  3 _∎

_≡⟨_⟩_ : ∀ x {y z} → x ≡ y → y ≡ z → x ≡ z
_ ≡⟨ x≡y ⟩ y≡z = ≡-trans x≡y y≡z

_∎ : ∀ x → x ≡ x
_∎ _ = refl

_+_ : ℕ → ℕ → ℕ
zero + n     = n
(succ m) + n = succ (m + n)

_*_ : ℕ → ℕ → ℕ
zero * n     = zero
(succ m) * n = n + (m * n)

_^_ : ℕ → ℕ → ℕ
x ^ zero     = (succ zero)
x ^ (succ n) = x * (x ^ n)

≡-*-cong-l : {x y : ℕ} (z : ℕ) → x ≡ y → z * x ≡ z * y
≡-*-cong-l {x} {y} z h =
  z * x ≡⟨ subst (λ w → (z * x) ≡ z * w) h refl ⟩
  z * y ∎

postulate
  *-asso : (x y z : ℕ) → x * y * z ≡ x * (y * z)

+-neut : (x : ℕ) → x + zero ≡ x
+-neut zero     = refl
+-neut (succ x) = subst (λ w → succ (x + zero) ≡ succ w) (+-neut x) refl

fo1 : (x m n : ℕ) → x ^ (m + n) ≡ (x ^ m) * (x ^ n)
fo1 x zero n     = ≡-sym (+-neut (x ^ n))
fo1 x (succ m) n = p-helper

  where
   p-helper : x * x ^ (m + n) ≡ x * x ^ m * x ^ n
   p-helper =
     x * x ^ (m + n)     ≡⟨ ≡-*-cong-l x (fo1 x m n) ⟩
     x * (x ^ m * x ^ n) ≡⟨ ≡-sym (*-asso x (x ^ m) (x ^ n)) ⟩
     x * x ^ m * x ^ n   ∎
