module Nat where

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

_+ₙ_ : ℕ → ℕ → ℕ
zero +ₙ n     = n
(succ m) +ₙ n = succ (m +ₙ n)

_*ₙ_ : ℕ → ℕ → ℕ
zero *ₙ n     = zero
(succ m) *ₙ n = n +ₙ (m *ₙ n)

