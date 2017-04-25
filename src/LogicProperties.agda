-- Logic Properties

module LogicProperties where

open import LogicDefinitions

∨-comm : {A B : Set} → A ∨ B → B ∨ A
∨-comm h = case inj₂ inj₁ h

∧-comm : {A B : Set} → A ∧ B → B ∧ A
∧-comm h = (∧-proj₂ h) , ∧-proj₁ h

∧-assoc₁ : {A B C : Set} → A ∧ (B ∧ C) → (A ∧ B) ∧ C
∧-assoc₁ {A₁} {B₁} {C} (x , x₁ , x₂) = (x , x₁) , x₂

∧-assoc₂ : {A B C : Set} → (A ∧ B) ∧ C → A ∧ (B ∧ C)
∧-assoc₂ {A} {B} {C} h = ∧-proj₁ (∧-proj₁ h) , ∧-proj₁ (∧-comm (∧-proj₁ h)) , ∧-proj₂ h

∨-assoc₁ : {A B C : Set} → A ∨ (B ∨ C) → (A ∨ B) ∨ C
∨-assoc₁ {A} {B} {C} h = case prf₁ prf₂ h

  where
   prf₁ : A → (A ∨ B) ∨ C
   prf₁ A = inj₁ (inj₁ A)

   prf₂ : B ∨ C → (A ∨ B) ∨ C
   prf₂ B∨C = case prf₁₁ prf₂₂ B∨C

    where
     prf₁₁ : B → (A ∨ B) ∨ C
     prf₁₁ B = inj₁ (inj₂ B)

     prf₂₂ : C → (A ∨ B) ∨ C
     prf₂₂ C = inj₂ C

∨-assoc₂ : {A B C : Set} → (A ∨ B) ∨ C → A ∨ (B ∨ C)
∨-assoc₂ {A} {B} {C} (inj₁ h) = case prf₁ prf₂ h

  where
   prf₁ : A → A ∨ B ∨ C
   prf₁ A = inj₁ A

   prf₂ : B → A ∨ B ∨ C
   prf₂ B = inj₂ (inj₁ B)
∨-assoc₂ {A} {B} {C} (inj₂ C₁) = inj₂ (inj₂ C₁)

