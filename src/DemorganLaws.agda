module DemorganLaws where

open import ClassicLogic
open import LogicDefinitions

-- De Morgan's laws

demorgan-01 : {p q : Set} → ¬ p ∧ ¬ q → ¬ (p ∨ q)
demorgan-01 (x , x₁) (inj₁ x₂) = x x₂
demorgan-01 (x , x₁) (inj₂ x₂) = x₁ x₂

demorgan-02 : {p q : Set} → ¬ (p ∨ q) → ¬ p ∧ ¬ q
demorgan-02 {p} {q} h = p₁-helper , p₂-helper
  where
    p₁-helper : p → ⊥
    p₁-helper x = h (inj₁ x)

    p₂-helper : q → ⊥
    p₂-helper x = h (inj₂ x)

demorgan-03 : {p q : Set} → ¬ (p ∧ q) → ¬ p ∨ ¬ q
demorgan-03 {p} {q} h = ¬-elim p-helper

  where
   p-helper : ¬ (¬ p ∨ ¬ q) → ⊥
   p-helper h1 = h ((¬¬-elim₁ (∧-proj₁ (demorgan-02 h1))) , (¬¬-elim₁ (∧-proj₂ (demorgan-02 h1))))

demorgan-04 : {p q : Set} → ¬ p ∨ ¬ q → ¬ (p ∧ q)
demorgan-04 {p} {q} h (x , x₁) = p1-helper (demorgan-01 (¬¬-elim₂ x , ¬¬-elim₂ x₁))

  where
   p1-helper : ¬ (¬ p ∨ ¬ q) → ⊥
   p1-helper h1 = h1 h
