module ClassicLogic where

open import Logic

-- The principle of the excluded middle.
postulate pem : ∀ {A} → A ∨ ¬ A

-- The principle of indirect proof (proof by contradiction).
¬-elim : ∀ {A} → (¬ A → ⊥) → A
¬-elim h = case (λ a → a) (λ ¬a → ⊥-elim (h ¬a)) pem

-- Double negation elimination.
¬¬-elim₁ : ∀ {A} → ¬ ¬ A → A
¬¬-elim₁ {A} h = ¬-elim h

¬¬-elim₂ : ∀ {A} → A → ¬ ¬ A
¬¬-elim₂ {A} h h1 = h1 h

-- The reductio ab absurdum rule. (Some authors uses this name for the
-- principle of indirect proof).
raa : ∀ {A} → (¬ A → A) → A
raa h = case (λ a → a) h pem
