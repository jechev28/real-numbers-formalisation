module TrichotomyPropertiesATP where

open import Axioms
open import Logic

postulate >∨<→≢ : (x y : ℝ) → (x > y) ∨ (x < y) → ¬ (x ≡ y)
{-# ATP prove >∨<→≢ #-}

postulate ≥→≮  : (x y : ℝ) → (x > y) ∨ (x ≡ y) → x ≮ y
{-# ATP prove ≥→≮ #-}

postulate ≡∨<→≯ : (x y : ℝ) → (x ≡ y) ∨ (x < y) → x ≯ y
{-# ATP prove ≡∨<→≯ #-}

postulate ≯∧≢→< : {x y : ℝ} → ¬ (x > y) ∧ ¬ (x ≡ y) → x < y
{-# ATP prove ≯∧≢→< #-}

postulate ≯∧≮→≡ : {x y : ℝ} → ¬ (x > y) ∧ ¬ (x < y) → x ≡ y
{-# ATP prove ≯∧≮→≡ #-}

postulate ≢∧≮→> : {x y : ℝ} → ¬ (x ≡ y) ∧ ¬ (x < y) → x > y
{-# ATP prove ≢∧≮→> #-}

postulate >-asym : {x y : ℝ} → x > y → ¬ (x < y)
{-# ATP prove >-asym #-}

postulate >-irrefl : {x : ℝ} → ¬ (x > x)
{-# ATP prove >-irrefl #-}

postulate >→≢ : {x y : ℝ} → x > y → ¬ (x ≡ y)
{-# ATP prove >→≢ >-irrefl #-}

postulate <-asym : {x y : ℝ} → x < y → ¬ (y < x)
{-# ATP prove <-asym #-}

postulate <-irrefl : {x : ℝ} → ¬ (x < x)
{-# ATP prove <-irrefl #-}

postulate <→≢ : {x y : ℝ} → x < y → ¬ (x ≡ y)
{-# ATP prove <→≢ #-}

postulate ≡→≯ : {x y : ℝ} → x ≡ y → ¬ (x > y)
{-# ATP prove ≡→≯ #-}

postulate ≡→≮ : {x y : ℝ} → x ≡ y → ¬ (x < y)
{-# ATP prove ≡→≮ #-}

postulate >→≮∧≢ : (x y : ℝ) → x > y → x ≮ y ∧ x ≢ y
{-# ATP prove >→≮∧≢ #-}

postulate ≡→≮∧≯ : (x y : ℝ) → x ≡ y → x ≮ y ∧ x ≯ y
{-# ATP prove ≡→≮∧≯ #-}

postulate <→≯∧≢ : (x y : ℝ) → x < y → x ≯ y ∧ x ≢ y
{-# ATP prove <→≯∧≢ #-}
