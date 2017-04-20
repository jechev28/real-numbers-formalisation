module Ncomp where

open import Nat
open import Logic

-- Equality in ℕ.
data _≡ₙ_ : ℕ → ℕ → Set where
  refl : (n : ℕ) → n ≡ₙ n

data ∃ₙ (P : ℕ → Set) : Set where
  exist : (n : ℕ) → P n → ∃ₙ P

data _≤´_ : ℕ → ℕ → Set where
  z≤n : ∀ n                 → zero  ≤´ n
  s≤s : ∀ m n → (m≤n : m ≤´ n) → succ m ≤´ succ n

-- p≤p : ∀ m n → succ m ≤´ succ n → m ≤´ n
-- p≤p m n h = {!!}

_<´_ : ℕ → ℕ → Set
m <´ n = succ m ≤´ n

_≥´_ : ℕ → ℕ → Set
m ≥´ n = n ≤´ m

_>´_ : ℕ → ℕ → Set
m >´ n = n <´ m

m≤s : ∀ m n → m ≤´ n → m ≤´ succ n
m≤s .0 n (z≤n .n) = z≤n (succ n)
m≤s .(succ m) .(succ n) (s≤s m n m≤´n) = s≤s m (succ n) (m≤s m n m≤´n)

s≤n : ∀ m n → succ m ≤´ n → m ≤´ n
s≤n zero .(succ n) (s≤s .0 n x) = z≤n (succ n)
s≤n (succ m) .(succ n) (s≤s .(succ m) n x) = s≤s m n (s≤n m n x)

-- m≤succm : ∀ m → m ≤´ succ m
-- m≤succm m = {!!}

-- succm>m : ∀ m → succ m >´ m
-- succm>m = {!!}

m<s : ∀ m n → m ≤´ n → m <´ succ n
m<s .0 n (z≤n .n) = s≤s zero n (z≤n n)
m<s .(succ m) .(succ n) (s≤s m n x) = s≤s (succ m) (succ n) (m<s m n x)

m<n : ∀ m n → succ m ≤´ n → m <´ n
m<n m .(succ n) (s≤s .m n x) = s≤s m n x

-- p≤n : ∀ m n → m ≤´ n → succ m ≤´ n
-- p≤n m n h = {!!}

UpperBound´ : (ℕ → Set) → ℕ → Set
UpperBound´ A ub = (n : ℕ) → A n → n ≤´ ub

Bound´ : (ℕ → Set) → Set
Bound´ A = ∃ₙ (λ ub → UpperBound´ A ub)

Lub´ : (ℕ → Set) → ℕ → Set
Lub´ A sup = (UpperBound´ A sup) ∧ ((ub : ℕ) → UpperBound´ A ub → sup ≤´ ub)

-- Example 1.

A : ℕ → Set
A n = n ≤´ 2

foo1 : UpperBound´ A 2
foo1 .0 (z≤n .2) = z≤n (succ (succ zero))
foo1 .(succ m) (s≤s m .1 Aa) = s≤s m 1 Aa

foo2 : UpperBound´ A 3
foo2 .0 (z≤n .2) = z≤n (succ (succ (succ zero)))
foo2 .(succ m) (s≤s m .1 B2) = m≤s (succ m) (succ (succ zero)) (s≤s m (succ zero) B2)

foo3 : (n : ℕ) → UpperBound´ A n → 2 ≤´ n
foo3 n A2 = A2 (succ (succ zero))
               (s≤s (succ zero) (succ zero) (s≤s zero zero (z≤n zero)))

bar1 : Bound´ A
bar1 = exist 2 foo1

foo4 : Lub´ A 2
foo4 = foo1 , foo3

-- Example 2.

B : ℕ → Set
B n = n <´ 2

f1 : UpperBound´ B 1
f1 n (s≤s .n .1 Bn) = Bn

f2 : UpperBound´ B 2
f2 .0 (s≤s .0 .1 (z≤n .1)) = z≤n (succ (succ zero))
f2 .(succ m) (s≤s .(succ m) .1 (s≤s m .0 Bn)) = s≤s m 1 (m≤s m 0 Bn)

f3 : UpperBound´ B 3
f3 .0 (s≤s .0 .1 (z≤n .1)) = z≤n 3
f3 .(succ m) (s≤s .(succ m) .1 (s≤s m .0 Bn)) = m≤s (succ m) 2 (s≤s m 1 (m≤s m 0 Bn))

bar2 : Bound´ B
bar2 = exist 2 f2

postulate
  notl->-≤ : {x y : ℕ} → ¬ (x >´ y) → x ≤´ y
  notr-<-≤ : {x y : ℕ} → (x <´ y) → ¬ (y ≤´ x )

foo : UpperBound´ B 0 → ⊥
foo h = notr-<-≤ (s≤s zero zero (z≤n zero)) (h 1 (m<s 1 1 (s≤s zero zero (z≤n zero))))

f4 : (ub : ℕ) → UpperBound´ B ub → 1 ≤´ ub
f4 zero B0 = ⊥-elim (foo B0)
f4 (succ zero) B1 = s≤s 0 0 (z≤n 0)
f4 (succ (succ ub)) Bub = Bub 1 (s≤s 1 1 (s≤s 0 0 (z≤n 0)))

f5 : Lub´ B 1
f5 = f1 , f4
