module Properties where

open import Axioms
open import DemorganLaws
open import EqProperties
open import EqReasoning
open import Logic
open import Nat

≡-<→< : {x y z : ℝ} → x ≡ y → y < z → x < z
≡-<→< (refl x) y<z = y<z

<-=-→-< : {x y z : ℝ} → x < y → y ≡ z → x < z
<-=-→-< x<y (refl y) = x<y

≡-+-cong-r : {x y z : ℝ} → x ≡ y → x + z ≡ y + z
≡-+-cong-r {x} {y} {z} h =
  x + z ≡⟨ subst (λ w → (x + z) ≡ w + z) h (refl (x + z)) ⟩
  y + z ∎

≡-+-cong-l : {x y z : ℝ} → x ≡ y → z + x ≡ z + y
≡-+-cong-l {x} {y} {z} x=y =
  z + x ≡⟨ subst (λ w → (z + x) ≡ z + w) x=y (refl (z + x)) ⟩
  z + y ∎

≡-*-cong-r : {x y : ℝ} (z : ℝ)→ x ≡ y → x * z ≡ y * z
≡-*-cong-r {x} {y} z h =
  x * z ≡⟨ subst (λ w → (x * z) ≡ w * z) h (refl (x * z)) ⟩
  y * z ∎

≡-*-cong-l : {x y : ℝ} (z : ℝ) → x ≡ y → z * x ≡ z * y
≡-*-cong-l {x} {y} z h =
  z * x ≡⟨ subst (λ w → (z * x) ≡ z * w) h (refl (z * x)) ⟩
  z * y ∎

>-+-right : {x y z : ℝ} → x > y → x + z > y + z
>-+-right {x} {y} {z} x>y = p-helper x>y (>-+-left x>y)

  where
    p-helper : {x y z : ℝ} → x > y → z + x > z + y → x + z > y + z
    p-helper {x} {y} {z} h₁ h₂ = subst₂ (λ t₁ t₂ → t₁ > t₂) (+-comm z x) (+-comm z y) h₂

>-to-< : {x y : ℝ} → x > y → y < x
>-to-< {x} {y} x>y = x>y

<-to-> : {x y : ℝ} → x < y → y > x
<-to-> {x} {y} x<y = x<y

≤-to-≥ : {x y : ℝ} → x ≤ y → y ≥ x
≤-to-≥ {x} {y} x≤y = (case p₁-helper p₂-helper x≤y)

  where
   p₁-helper : x < y → y > x ∨ y ≡ x
   p₁-helper x<y = inj₁ (<-to-> x<y)

   p₂-helper : x ≡ y → y > x ∨ y ≡ x
   p₂-helper x≡y = inj₂ (≡-sym x≡y)

≥-to-≤ : {x y : ℝ} → x ≥ y → y ≤ x
≥-to-≤ {x} {y} x≥y = case p₁-helper p₂-helper x≥y

  where
   p₁-helper : x > y → y < x ∨ y ≡ x
   p₁-helper x>y = inj₁ (>-to-< x>y)

   p₂-helper : x ≡ y → y < x ∨ y ≡ x
   p₂-helper x≡y = inj₂ (≡-sym x≡y)

≡-+-cancel-r : {x y z : ℝ} → x + z ≡ y + z → x ≡ y
≡-+-cancel-r {x} {y} {z} h =
  x               ≡⟨ ≡-sym (+-neut x) ⟩
  x + r₀          ≡⟨ subst (λ w → (x + r₀) ≡ (x + w)) (≡-sym (+-inve z)) (refl (x + r₀)) ⟩
  x + (z + (- z)) ≡⟨ ≡-sym (+-asso x z (- z)) ⟩
  (x + z) + (- z) ≡⟨ subst (λ w → (x + z) + (- z) ≡ w + (- z)) h (refl (x + z + - z)) ⟩
  (y + z) + (- z) ≡⟨ +-asso y z (- z) ⟩
  y + (z + (- z)) ≡⟨ subst (λ w → y + (z + (- z)) ≡ y + w) (+-inve z) (refl (y + (z + - z))) ⟩
  y + r₀          ≡⟨ +-neut y ⟩
  y               ∎

≡-*-cancel-r : {x y z : ℝ} → z ≢ r₀ → x * z ≡ y * z → x ≡ y
≡-*-cancel-r {x} {y} {z} h1 h2 =
  x              ≡⟨ ≡-sym (*-neut x) ⟩
  x * r₁         ≡⟨ subst (λ w → (x * r₁) ≡ (x * w)) (≡-sym (*-inve z h1)) (refl (x * r₁)) ⟩
  x * (z * z ⁻¹) ≡⟨ ≡-sym (*-asso x z (z ⁻¹))  ⟩
  (x * z) * z ⁻¹ ≡⟨ subst (λ w → (x * z) * z ⁻¹ ≡ w * z ⁻¹) h2 (refl (x * z * z ⁻¹)) ⟩
  (y * z) * z ⁻¹ ≡⟨ *-asso y z (z ⁻¹) ⟩
  y * (z * z ⁻¹) ≡⟨ subst (λ w → (y * (z * z ⁻¹)) ≡ (y * w)) (*-inve z h1) (refl (y * (z * z ⁻¹))) ⟩
  y * r₁         ≡⟨ *-neut y ⟩
  y              ∎

>-+-cancel-r : {x y z : ℝ} → x + z > y + z → x > y
>-+-cancel-r h = p₁-helper (p₂-helper (p₃-helper (p₄-helper h)))

  where
    p₁-helper : {x y : ℝ} → x + r₀ > y + r₀ → x > y
    p₁-helper {x} {y} h = subst₂ (λ t₁ t₂ → t₁ > t₂) (+-neut x) (+-neut y) h

    p₂-helper : {x y z : ℝ} → x + (z + (- z)) > y + (z + (- z)) → x + r₀ > y + r₀
    p₂-helper {x} {y} {z} h = subst₂ (λ t₁ t₂ → x + t₁ > y + t₂) (+-inve z) (+-inve z) h

    p₃-helper : {x y z : ℝ} → (x + z) + (- z) > (y + z) + (- z) → x + (z + (- z)) > y + (z + (- z))
    p₃-helper {x} {y} {z} h = p-helper h

     where
       p-helper : {x y x₁ x₂ : ℝ} → (x + x₁) + x₂ > (y + x₁) + x₂ → x + (x₁ + x₂) > y + (x₁ + x₂)
       p-helper {x} {y} {x₁} {x₂} h = subst₂ (λ t₁ t₂ → t₁ > t₂) (+-asso x x₁ x₂) (+-asso y x₁ x₂) h

    p₄-helper : {x y z : ℝ} → x + z > y + z → x + z + (- z) > y + z + (- z)
    p₄-helper {x} {y} {z} h = >-+-right h

─-neut : {x : ℝ} → r₀ - x ≡ - x
─-neut {x} =
   r₀ - x    ≡⟨ +-comm r₀ (- x) ⟩
   - x + r₀  ≡⟨ +-neut (- x) ⟩
   - x       ∎

*-right-zero : {x : ℝ} → x * r₀ ≡ r₀
*-right-zero {x} =
  x * r₀
    ≡⟨ ≡-sym (+-neut (x * r₀)) ⟩
  (x * r₀) + r₀
    ≡⟨ subst (λ w → x * r₀ + r₀ ≡ x * r₀ + w) (≡-sym (+-inve (x * r₀))) (refl (x * r₀ + r₀)) ⟩
  (x * r₀) + ((x * r₀) + (- (x * r₀)))
    ≡⟨ ≡-sym (+-asso (x * r₀) (x * r₀) (- (x * r₀))) ⟩
  ((x * r₀) + (x * r₀)) + (- (x * r₀))
    ≡⟨ subst (λ w → x * r₀ + x * r₀ + - (x * r₀) ≡ w + - (x * r₀)) p-helper (refl (x * r₀ + x * r₀ + - (x * r₀))) ⟩
  ((x * r₀) + r₀) + (- (x * r₀))
    ≡⟨ subst (λ w → x * r₀ + r₀ + - (x * r₀) ≡ w + - (x * r₀)) (+-neut (x * r₀)) (refl (x * r₀ + r₀ + - (x * r₀))) ⟩
  (x * r₀) + (- (x * r₀))
    ≡⟨ +-inve (x * r₀) ⟩
  r₀ ∎

  where
    p-helper : {x : ℝ} → x * r₀ + x * r₀ ≡ x * r₀ + r₀
    p-helper {x} =
      x * r₀ + x * r₀ ≡⟨ ≡-sym (*-dist x r₀ r₀) ⟩
      x * (r₀ + r₀)   ≡⟨ subst (λ w → x * (r₀ + r₀) ≡ x * w) (+-neut r₀) (refl (x * (r₀ + r₀))) ⟩
      x * r₀          ≡⟨ ≡-sym (+-neut (x * r₀)) ⟩
      x * r₀ + r₀     ∎

<-to-minus : {x y : ℝ} → y < x → x - y > r₀
<-to-minus {x} {y} y<x = >-+-cancel-r (p1-helper (>-+-right y<x))

  where
   p1-helper : x + r₀ > y + r₀ → x - y + y > r₀ + y
   p1-helper h1 = subst₂ (λ t₁ t₂ → t₁ > t₂) p11-helper (+-comm y r₀) h1

    where
     p11-helper : x + r₀ ≡ x - y + y
     p11-helper =
       x + r₀ ≡⟨ subst (λ w → x + r₀ ≡ x + w) (≡-sym (+-inve y)) (refl (x + r₀)) ⟩
       x + (y - y) ≡⟨ subst (λ w → x + (y - y) ≡ x + w) (+-comm y (- y)) (refl (x + (y - y))) ⟩
       x + (- y + y) ≡⟨ ≡-sym (+-asso x (- y) y) ⟩
       x - y + y  ∎
minus-to-< : {x y : ℝ} → x - y > r₀ → y < x
minus-to-< {x} {y} h = >-to-< (p1-helper (p2-helper (p3-helper (>-+-right h))))

  where
   p1-helper : x + r₀ > y → x > y
   p1-helper = subst₂ (λ t₁ t₂ → t₁ > t₂) (+-neut x) (refl y)

   p2-helper : x + (y - y) > y → x + r₀ > y
   p2-helper = subst₂ (λ t₁ t₂ → t₁ > t₂) (subst (λ w → x + (y - y) ≡ x + w) (+-inve y) (refl (x + (y - y)))) (refl y)

   p3-helper : x - y + y > r₀ + y → x + (y - y) > y
   p3-helper = subst₂ (λ t₁ t₂ → t₁ > t₂) p31-helper p32-helper

    where
     p31-helper : x - y + y ≡ x + (y - y)
     p31-helper =
      x - y + y   ≡⟨ +-asso x (- y) y ⟩
      x + (- y + y)   ≡⟨ subst (λ w → x + (- y + y) ≡ x + w) (+-comm (- y) y) (refl (x + (- y + y))) ⟩
      x + (y - y) ∎

     p32-helper : r₀ + y ≡ y
     p32-helper =
      r₀ + y   ≡⟨ +-comm r₀ y ⟩
      y + r₀   ≡⟨ +-neut y ⟩
      y ∎

>-to-minus : {x y : ℝ} → y > x → x - y < r₀
>-to-minus {x} {y} y>x = >-+-cancel-r (p1-helper (p2-helper (>-to-< (subst₂ (λ t₁ t₂ → t₁ > t₂) (refl y) (≡-sym (+-neut x)) y>x))))

  where
   p1-helper : x + ((- y) + y) < y + r₀ → (x + (- y)) + y < r₀ + y
   p1-helper = subst₂ (λ t₁ t₂ → t₁ > t₂) (+-comm y r₀) (≡-sym (+-asso x (- y) y))

   p2-helper : x + r₀ < y → x + ((- y) + y) < y + r₀
   p2-helper = subst₂ (λ t₁ t₂ → t₁ < t₂) (≡-sym p22-helper) (≡-sym (+-neut y))

     where
      p22-helper : x + (- y + y) ≡ x + r₀
      p22-helper =
        x + (- y + y) ≡⟨ subst (\w → x + (- y + y) ≡ x + w ) (+-comm (- y) y) (refl (x + (- y + y))) ⟩
        x + (y + (- y)) ≡⟨ subst (\w → x + (y + (- y)) ≡ x + w) (+-inve y) (refl (x + (y + (- y)))) ⟩
        x + r₀ ∎

x-y<0→x<y : {x y : ℝ} → x - y < r₀ → x < y
x-y<0→x<y {x} {y} h = p₁-helper (p₂-helper (>-to-< (>-+-right h)) )

  where
   p₁-helper : x + r₀ < y → x < y
   p₁-helper h₁ = subst₂ (λ t₁ t₂ → t₁ > t₂) (refl y) (+-neut x) h₁

   p₂-helper : x - y + y < r₀ + y → x + r₀ < y
   p₂-helper h₂ = subst₂ (λ t₁ t₂ → t₁ > t₂) p₂₁-helper p₂₂-helper h₂

    where
     p₂₁-helper : r₀ + y ≡ y
     p₂₁-helper =
        r₀ + y ≡⟨ +-comm r₀ y ⟩
        y + r₀ ≡⟨ +-neut y ⟩
        y      ∎

     p₂₂-helper : x - y + y ≡ x + r₀
     p₂₂-helper =
        x - y + y     ≡⟨ +-asso x (- y) y ⟩
        x + (- y + y) ≡⟨ subst (λ w → x + (- y + y) ≡ x + w) (+-comm (- y) y) (refl (x + (- y + y))) ⟩
        x + (y - y)   ≡⟨ subst (λ w → x + (y - y) ≡ x + w) (+-inve y) (refl (x + (y - y))) ⟩
        x + r₀       ∎

x≢0→x>0∨x<0 : {x : ℝ} → x ≢ r₀ → (x > r₀) ∨ (x < r₀)
x≢0→x>0∨x<0 {x} x≢0 = case prf₁ prf₂ (trichotomy x r₀)

  where
  prf₁ : x > r₀ ∧ ¬ x ≡ r₀ ∧ ¬ x < r₀ → x > r₀ ∨ x < r₀
  prf₁ h = inj₁ (∧-proj₁ h)

  prf₂ : (¬ x > r₀ ∧ x ≡ r₀ ∧ ¬ x < r₀) ∨ (¬ x > r₀ ∧ ¬ x ≡ r₀ ∧ x < r₀) → x > r₀ ∨ x < r₀
  prf₂ h = case prf₂₁ prf₂₂ h

    where
     prf₂₁ : ¬ x > r₀ ∧ x ≡ r₀ ∧ ¬ x < r₀ → x > r₀ ∨ x < r₀
     prf₂₁ h = inj₁ (⊥-elim (x≢0 (∧-proj₁ (p-helper h))))

      where
       p-helper : ¬ x > r₀ ∧ (x ≡ r₀ ∧ ¬ x < r₀) → x ≡ r₀ ∧ (¬ x < r₀ ∧ ¬ x > r₀)
       p-helper h = ∧-assoc₂ (∧-comm h)

     prf₂₂ : ¬ x > r₀ ∧ ¬ x ≡ r₀ ∧ x < r₀ → x > r₀ ∨ x < r₀
     prf₂₂ h = inj₂ (∧-proj₂ (∧-assoc₁ h))

x≢0→x⁻¹≢0 : {x : ℝ} → x ≢ r₀ → (x ⁻¹) ≢ r₀
x≢0→x⁻¹≢0 {x} x≢0 x⁻¹≡0 = 1≢0  (p1-helper (≡-*-cong-l x x⁻¹≡0))

  where
   p1-helper : x * x ⁻¹ ≡ x * r₀ → r₁ ≡ r₀
   p1-helper h = subst₂ (λ t₁ t₂ → t₁ ≡ t₂) (*-inve x x≢0) *-right-zero h

x<0→-x>0 : {x : ℝ} → x < r₀ → - x > r₀
x<0→-x>0 {x} h = subst₂ (λ t₁ t₂ → t₁ > t₂) (─-neut) (refl r₀) (<-to-minus h)

x>0→-x<0 : {x : ℝ} → x > r₀ → - x < r₀
x>0→-x<0 {x} x>r₀ = subst₂ (λ t₁ t₂ → t₁ > t₂) (refl r₀) ─-neut (>-to-minus x>r₀)

-x>0→x<0 : {x : ℝ} → - x > r₀ → x < r₀
-x>0→x<0 {x} -x>r₀ = minus-to-< (subst₂ (λ t₁ t₂ → t₁ > t₂) (≡-sym ─-neut) (refl r₀) -x>r₀)

-x<0→x>0 : (x : ℝ) → - x < r₀ → x > r₀
-x<0→x>0 x -x<0 = <-to-> (x-y<0→x<y p₁-helper)

  where
   p₁-helper : r₀ - x < r₀
   p₁-helper = subst₂ (λ t₁ t₂ → t₁ < t₂) p₂-helper (refl r₀) -x<0

    where
     p₂-helper : - x ≡ r₀ - x
     p₂-helper =
        - x      ≡⟨ ≡-sym (+-neut (- x)) ⟩
        - x + r₀ ≡⟨ +-comm (- x) r₀ ⟩
        r₀ - x   ∎

*-negation : {x : ℝ} → - x ≡ (- r₁) * x
*-negation {x} =
  - x
    ≡⟨ ≡-sym (+-neut (- x)) ⟩
  (- x) + r₀
    ≡⟨ subst (λ w → (- x) + r₀ ≡ - x + w) (≡-sym p-helper) (refl (- x + r₀)) ⟩
  (- x) + ((- r₁) * x + x)
    ≡⟨ subst (λ w → (- x) + ((- r₁) * x + x) ≡ - x + w) (+-comm ((- r₁) * x) x) (refl (- x + (- r₁ * x + x))) ⟩
  (- x) + (x + (- r₁) * x)
    ≡⟨ ≡-sym (+-asso (- x) x (- r₁ * x)) ⟩
  ((- x) + x) + (- r₁) * x
    ≡⟨ subst (λ w → - x + x + (- r₁) * x ≡ w + - r₁ * x) (+-comm (- x) x) (refl (- x + x + - r₁ * x)) ⟩
  (x + (- x)) + (- r₁) * x
    ≡⟨ subst (λ w → x + (- x) + (- r₁) * x ≡ w + (- r₁) * x) (+-inve x) (refl (x + - x + - r₁ * x)) ⟩
  r₀ + (- r₁) * x
    ≡⟨ +-comm r₀ ((- r₁) * x) ⟩
  (- r₁) * x + r₀
    ≡⟨ +-neut ((- r₁) * x) ⟩
  (- r₁) * x ∎

  where
    p-helper : {x : ℝ} → (- r₁) * x + x ≡ r₀
    p-helper {x} =
      (- r₁) * x + x
      ≡⟨ subst (λ w → - r₁ * x + x ≡ w + x) (*-comm (- r₁) x) (refl (- r₁ * x + x)) ⟩
      x * (- r₁) + x
      ≡⟨ subst (λ w → x * (- r₁) + x ≡ x * (- r₁) + w) (≡-sym (*-neut x)) (refl (x * - r₁ + x)) ⟩
      x * (- r₁) + x * r₁
      ≡⟨ ≡-sym (*-dist x (- r₁) r₁) ⟩
      x * ((- r₁) + r₁)
      ≡⟨ subst (λ w → x * (- r₁ + r₁) ≡ x * w) (+-comm (- r₁) r₁) (refl (x * (- r₁ + r₁))) ⟩
      x * (r₁ + (- r₁))
      ≡⟨ subst (λ w → x * (r₁ + - r₁) ≡ x * w) (+-inve r₁) (refl (x * (r₁ + - r₁))) ⟩
      x * r₀
      ≡⟨ *-right-zero ⟩
      r₀ ∎

-- Laws of the signs in multiplication.

mul-xy : {x y : ℝ} → (- x) * y ≡ - (x * y)
mul-xy {x} {y} =
  (- x) * y        ≡⟨ subst (λ w → (- x) * y ≡ w * y) *-negation (refl ((- x) * y)) ⟩
  ((- r₁) * x) * y ≡⟨ *-asso (- r₁) x y ⟩
  (- r₁) * (x * y) ≡⟨ ≡-sym *-negation ⟩
  - (x * y)        ∎

mulx-y : {x y : ℝ} → x * (- y) ≡ - (x * y)
mulx-y {x} {y} =
   x * (- y)  ≡⟨ *-comm x (- y) ⟩
   (- y ) * x ≡⟨ mul-xy ⟩
   - (y * x)  ≡⟨ subst (λ w → - (y * x) ≡ - w) (*-comm y x) (refl (- (y * x))) ⟩
   - (x * y)  ∎

mul--x : {x : ℝ} → - (- x) ≡ x
mul--x {x} =
  - (- x)
    ≡⟨ ≡-sym (+-neut (- (- x))) ⟩
  - (- x) + r₀
    ≡⟨ +-comm (- (- x)) r₀ ⟩
  r₀ + (- (- x))
    ≡⟨ subst (λ w → r₀ + (- (- x)) ≡ w + (- (- x))) (≡-sym (+-inve x)) (refl (r₀ + - (- x))) ⟩
  (x + (- x)) + (- (- x))
    ≡⟨ +-asso x (- x) (- (- x)) ⟩
  x + ((- x) + (- (- x)))
    ≡⟨ subst (λ w → x + ((- x) + (- (- x))) ≡ x + w) (+-inve (- x)) (refl (x + (- x + - (- x)))) ⟩
  x + r₀ ≡⟨ +-neut x ⟩
  x ∎

mul-x+y : ∀ {x y} → - (x + y) ≡ - x + (- y)
mul-x+y {x} {y} =
  - (x + y)        ≡⟨ *-negation ⟩
  (- r₁) * (x + y) ≡⟨ *-dist (- r₁) x y ⟩
  (- r₁) * x + (- r₁) * y
    ≡⟨ subst (λ w → ((- r₁) * x + (- r₁) * y) ≡ (w + (- r₁) * y)) ( ≡-sym *-negation ) (refl (- r₁ * x + - r₁ * y)) ⟩
  - x + (- r₁) * y ≡⟨ subst (λ w → (- x + (- r₁) * y) ≡ (- x + w)) (≡-sym *-negation) (refl (- x + - r₁ * y)) ⟩
  - x + (- y)      ∎

mul-x-y : {x y : ℝ} → (- x) * (- y) ≡ x * y
mul-x-y {x} {y} =
  (- x) * (- y) ≡⟨ mul-xy ⟩
  - (x * (- y)) ≡⟨ subst (λ w → - (x * - y) ≡ - w) (*-comm x (- y)) (refl (- (x * - y))) ⟩
  - ((- y) * x) ≡⟨ subst (λ w → - (- y * x) ≡ - w) mul-xy (refl (- (- y * x))) ⟩
  - (- (y * x)) ≡⟨ mul--x ⟩
  y * x         ≡⟨ *-comm y x ⟩
  x * y         ∎

*-dist-minus : (x y z : ℝ) → x * (y - z) ≡ x * y - x * z
*-dist-minus x y z =
      x * (y - z)   ≡⟨ *-dist x y (- z) ⟩
      x * y + x * (- z)   ≡⟨ subst (λ w → x * y + x * (- z) ≡ x * y + x * w) *-negation (refl (x * y + x * (- z))) ⟩
      x * y + x * ((- r₁) * z)   ≡⟨ subst (λ w → x * y + x * ((- r₁) * z) ≡ x * y + w) (≡-sym (*-asso x (- r₁) z))
                                          (refl (x * y + x * ((- r₁) * z))) ⟩
      x * y + (x * (- r₁)) * z   ≡⟨ subst (λ w → x * y + (x * (- r₁)) * z ≡ x * y + w * z) (*-comm x (- r₁))
                                          (refl (x * y + (x * (- r₁)) * z)) ⟩
      x * y + ((- r₁) * x) * z   ≡⟨ subst (λ w → x * y + ((- r₁) * x) * z ≡ x * y + w * z) (≡-sym *-negation)
                                          (refl (x * y + ((- r₁) * x) * z)) ⟩
      x * y + (- x) * z   ≡⟨ subst (λ w → x * y + (- x) * z ≡ x * y + w) mul-xy (refl (x * y + (- x) * z)) ⟩
      x * y - x * z ∎

>-asym : {x y : ℝ} → x > y → x ≮ y
>-asym {x} {y} x>y x<y = case prf₁ prf₂ (trichotomy x y)
  where
  prf₁ : (x > y) ∧ (¬ x ≡ y) ∧ (¬ x < y) → ⊥
  prf₁ (_ , _ , p) = p x<y

  prf₂ : (¬ x > y ∧ x ≡ y ∧ ¬ x < y) ∨ (¬ x > y ∧ ¬ x ≡ y ∧ x < y) → ⊥
  prf₂ (inj₁ (p , _)) = p x>y
  prf₂ (inj₂ (p , _)) = p x>y

>-irrefl : {x : ℝ} → x ≯ x
>-irrefl h = >-asym h h

>→≢ : {x y : ℝ} → x > y → x ≢ y
>→≢ x>y (refl x) = >-irrefl x>y

≥→≮  : {x y : ℝ} → x ≥ y → x ≮ y
≥→≮ {x} {y} x≥y x<y = case prf1 prf2 x≥y

  where
    prf1 : x > y → ⊥
    prf1 x>y = >-asym x>y (<-to-> x<y)

    prf2 : x ≡ y → ⊥
    prf2 x≡y = >→≢ (<-to-> x<y) (≡-sym x≡y)

≢∧≮→> : {x y : ℝ} → (x ≢ y) ∧ (x ≮ y) → x > y
≢∧≮→> {x} {y} (x≢y , x≮y) = case prf₁ prf₂ (trichotomy x y)

  where
   prf₁ : x > y ∧ ¬ x ≡ y ∧ ¬ x < y → x > y
   prf₁ h = ∧-proj₁ h

   prf₂ : (¬ x > y ∧ x ≡ y ∧ ¬ x < y) ∨ (¬ x > y ∧ ¬ x ≡ y ∧ x < y) → x > y
   prf₂ h = case prf₂₁ prf₂₂ h

    where
     prf₂₁ : ¬ x > y ∧ x ≡ y ∧ ¬ x < y → x > y
     prf₂₁ h₁ = ⊥-elim (x≢y (∧-proj₁ (p-helper h₁)))

      where
       p-helper : ¬ x > y ∧ (x ≡ y ∧ ¬ x < y) → x ≡ y ∧ (¬ x < y ∧ ¬ x > y)
       p-helper h₂ = ∧-assoc₂ (∧-comm h₂)

     prf₂₂ : (¬ x > y) ∧ (¬ x ≡ y) ∧ (x < y) → x > y
     prf₂₂ h₃ = ⊥-elim (x≮y (∧-proj₂ (∧-assoc₁ h₃)))

≰→> : {x y : ℝ} → x ≰ y → x > y
≰→> {x} {y} h = ≢∧≮→> (∧-comm (demorgan-02 h))

<-asym : {x y : ℝ} → x < y → y ≮ x
<-asym {x} {y} x<y y<x = >-asym x<y y<x

<-irrefl : {x : ℝ} → x ≮ x
<-irrefl x<x = <-asym x<x x<x

<→≢ : {x y : ℝ} → x < y → x ≢ y
<→≢ x<y (refl x) = <-irrefl x<y

≡→≯ : {x y : ℝ} → x ≡ y → x ≯ y
≡→≯ x≡y x>y = >→≢ x>y x≡y

≡→≮ : {x y : ℝ} → x ≡ y → x ≮ y
≡→≮ x≡y x<y = <→≢ x<y x≡y

>→≮∧≢ : (x y : ℝ) → x > y → x ≮ y ∧ x ≢ y
>→≮∧≢ x y x>y = (λ x<y → >-asym x>y x<y) , (λ x=y → ≡→≯ x=y x>y)

≡→≮∧≯ : (x y : ℝ) → x ≡ y → x ≮ y ∧ x ≯ y
≡→≮∧≯ x y x=y = (λ x<y → <→≢ x<y x=y) , (λ x>y → >→≢ x>y x=y)

<→≯∧≢ : (x y : ℝ) → x < y → x ≯ y ∧ x ≢ y
<→≯∧≢ x y x<y = (λ x>y → <-asym x<y x>y) , (λ x=y → <→≢ x<y x=y)

<→≱ : {x y : ℝ} → x < y → x ≱ y
<→≱ {x} {y} x<y x≥y = case prf1 prf2 x≥y

  where
   prf1 : x > y → ⊥
   prf1 x>y = <-asym x<y (>-to-< x>y)

   prf2 : x ≡ y → ⊥
   prf2 x≡y = >→≢ (<-to-> x<y) (≡-sym x≡y)

≤→≯  : {x y : ℝ} → x ≤ y → x ≯ y
≤→≯ {x} {y} x≤y x>y = case prf1 prf2 x≤y

  where
    prf1 : x < y → ⊥
    prf1 x<y = <-asym x<y (>-to-< x>y)

    prf2 : x ≡ y → ⊥
    prf2 x≡y = >→≢ x>y x≡y

>-∧-*-cong-l : {x y z : ℝ} → (x > y) ∧ (z > r₀) → z * x > z * y
>-∧-*-cong-l {x} {y} {z} h = <-to-> (minus-to-< (subst₂ (λ t₁ t₂ → t₁ > t₂) (*-dist-minus z x y) (refl r₀)
                                               (>-∧-* ((∧-proj₂ h) , (<-to-minus (∧-proj₁ h))))))
>-*-cong-l : {x y z : ℝ} → z > r₀ → x > y → z * x > z * y
>-*-cong-l {x} {y} {z} z>r₀ x>y = >-∧-*-cong-l (x>y , z>r₀)

>-*-cong-r : {x y z : ℝ} → z > r₀ → x > y → x * z > y * z
>-*-cong-r {x} {y} {z} z>r₀ x>y = p-helper x>y (>-*-cong-l z>r₀ x>y)

  where
    p-helper : {x y z : ℝ} → x > y → z * x > z * y → x * z > y * z
    p-helper {x} {y} {z} h₁ h₂ = subst₂ (λ t₁ t₂ → t₁ > t₂) (*-comm z x) (*-comm z y) h₂

>-∧-*-cong-r : {x y z : ℝ} → (x > y) ∧ (z > r₀) → x * z > y * z
>-∧-*-cong-r {x} {y} {z} h = >-*-cong-r (∧-proj₂ h) (∧-proj₁ h)

>->-cong-r : {x y z w : ℝ} → (x > y) ∧ (y > r₀) → (z > w) ∧ (w > r₀) → x * z > y * w
>->-cong-r {x} {y} {z} {w} h₁ h₂ = >-trans (>-∧-*-cong-r (p₁-helper h₁ h₂)) (>-∧-*-cong-l (p₂-helper h₁ h₂))

  where
   p₁-helper : {x y z w : ℝ} → (x > y) ∧ (y > r₀) → (z > w) ∧ (w > r₀) → (x > y) ∧ (z > r₀)
   p₁-helper {x} {y} {z} {w} h₁ h₂ = (∧-proj₁ h₁) , >-trans (∧-proj₁ h₂) (∧-proj₂ h₂)

   p₂-helper : {x y z w : ℝ} → (x > y) ∧ (y > r₀) → (z > w) ∧ (w > r₀) → (z > w) ∧ (y > r₀)
   p₂-helper {x} {y} {z} {w} h₁ h₂ = (∧-proj₁ h₂) , (∧-proj₂ h₁)

<-trans : {x y z : ℝ} → x < y → y < z → x < z
<-trans {x} {y} {z} x<y y<z = >-to-< (>-trans (<-to-> y<z) (<-to-> x<y))

≡->→> : {x y z : ℝ} → x ≡ y → y > z → x > z
≡->→> (refl x) y>z = y>z

>-≡→> : {x y z : ℝ} → x > z → x ≡ y → y > z
>-≡→> x>z (refl x) = x>z

<-≡→< : {x y z : ℝ} → x < y → y ≡ z → x < z
<-≡→< x<y (refl x₁) = x<y

<-+-left : {x y z : ℝ} → x < y → z + x < z + y
<-+-left {x} {y} {z} x<y = >-to-< (>-+-left (<-to-> x<y))

<-+-right : {x y z : ℝ} → x < y → x + z < y + z
<-+-right {x} {y} {z} x<y = >-to-< (>-+-right (<-to-> x<y))

<-<-+ : {x y z w : ℝ} → x < y → z < w → x + z < y + w
<-<-+ {x} {y} {z} {w} x<y z<w = <-trans (<-+-right x<y) (<-+-left z<w)

≤-<-trans : {x y z : ℝ} → x ≤ y → y < z → x < z
≤-<-trans {x} {y} {z} x≤y y<z = case prf1 prf2 x≤y

  where
   prf1 : x < y → x < z
   prf1 x<y = <-trans x<y y<z

   prf2 : x ≡ y → x < z
   prf2 x≡y = ≡-<→< x≡y y<z

≥->-trans : {x y z : ℝ} → x ≥ y → y > z → x > z
≥->-trans {x} {y} {z} x≥y y>z = case prf1 prf2 x≥y

  where
   prf1 : x > y → x > z
   prf1 x>y = >-trans x>y y>z

   prf2 : x ≡ y → x > z
   prf2 x≡y = ≡->→> x≡y y>z

≤-∨ : (x y : ℝ) → x ≤ y ∨ y ≤ x
≤-∨ x y = case prf₁ (case prf₂ prf₃) (trichotomy x y)

  where
   prf₁ : x > y ∧ ¬ x ≡ y ∧ ¬ x < y → x ≤ y ∨ y ≤ x
   prf₁ (x>y , ¬x≡y , ¬x<y) = inj₂ (inj₁ (>-to-< x>y))

   prf₂ : ¬ x > y ∧ x ≡ y ∧ ¬ x < y → x ≤ y ∨ y ≤ x
   prf₂ (¬x>y , x≡y , ¬x<y) = inj₁ (inj₂ x≡y)

   prf₃ : ¬ x > y ∧ ¬ x ≡ y ∧ x < y → x ≤ y ∨ y ≤ x
   prf₃ (¬x>y , ¬x≡y , x<y) = inj₁ (inj₁ x<y)

*-left-zero : {x : ℝ} → r₀ * x ≡ r₀
*-left-zero {x} =
  r₀ * x ≡⟨ *-comm r₀ x ⟩
  x * r₀ ≡⟨ *-right-zero ⟩
  r₀     ∎

*-≢-zero : {x y : ℝ} → x ≢ r₀ → y ≢ r₀ → (x * y) ≢ r₀
*-≢-zero {x} {y} x≢0 y≢0 h = p₁-helper p₂-helper

 where
  p₁-helper : (x ≡ r₀) ∨ (y ≡ r₀) → ⊥
  p₁-helper h₁ = case prf1 prf2 h₁

    where
     prf1 : x ≡ r₀ → ⊥
     prf1 x≡0 = x≢0 x≡0

     prf2 : y ≡ r₀ → ⊥
     prf2 y≡0 = y≢0 y≡0

  p₂-helper : (x ≡ r₀) ∨ (y ≡ r₀)
  p₂-helper = inj₁ p₂₁-helper

    where
     p₂₁-helper : x ≡ r₀
     p₂₁-helper =
       x              ≡⟨ ≡-sym (*-neut x) ⟩
       x * r₁         ≡⟨ subst (λ w → x * r₁ ≡ x * w) (≡-sym (*-inve y y≢0)) (refl (x * r₁)) ⟩
       x * (y * y ⁻¹) ≡⟨ ≡-sym (*-asso x y (y ⁻¹)) ⟩
       (x * y) * y ⁻¹ ≡⟨ subst (λ w → x * y * y ⁻¹ ≡ w * y ⁻¹) h (refl (x * y * y ⁻¹)) ⟩
       r₀ * y ⁻¹      ≡⟨ *-left-zero ⟩
       r₀             ∎

>-r₀-produc : {x : ℝ} → x > r₀ → x * x > r₀
>-r₀-produc {x} x>r₀ = >-∧-* (x>r₀ , x>r₀)

<-∧-* : {x y : ℝ} → (x < r₀) ∧ (y < r₀) → x * y > r₀
<-∧-* {x} {y} h = p-helper (>-∧-* ((x<0→-x>0 (∧-proj₁ h)) , (x<0→-x>0 (∧-proj₂ h))))

  where
   p-helper : (- x) * (- y) > r₀ → x * y > r₀
   p-helper h = subst₂ (λ t₁ t₂ → t₁ > t₂) mul-x-y (refl r₀) h

<-r₀-produc : {x : ℝ} → x < r₀ → x * x > r₀
<-r₀-produc {x} x<0 = <-∧-* (x<0 , x<0)

*-∨-zero : {x y : ℝ} → (x ≡ r₀) ∨ (y ≡ r₀) → x * y ≡ r₀
*-∨-zero {x} {y} h = case prf1 prf2 h

  where
   prf1 : x ≡ r₀ → x * y ≡ r₀
   prf1 h =
     x * y  ≡⟨ subst (λ w → x * y ≡ w * y) h (refl (x * y)) ⟩
     r₀ * y ≡⟨ *-left-zero ⟩
     r₀ ∎

   prf2 : y ≡ r₀ → x * y ≡ r₀
   prf2 h =
     x * y ≡⟨ subst (λ w → x * y ≡ x * w) h (refl (x * y)) ⟩
     x * r₀ ≡⟨ *-right-zero ⟩
     r₀ ∎

mulxx>0 : {x : ℝ} → (x > r₀) ∨ (x < r₀) → x * x > r₀
mulxx>0 {x} h = case >-r₀-produc <-r₀-produc h

<-*-cong-l : {x y z : ℝ} → z > r₀ → x < y → z * x < z * y
<-*-cong-l {x} {y} {z} z>r₀ x<y = >-*-cong-l z>r₀ x<y

r₀-sqr : sqr r₀ ≡ r₀
r₀-sqr = *-right-zero

r₁-sqr : sqr r₁ ≡ r₁
r₁-sqr = *-neut r₁

>-sqr : {x : ℝ} → x ≢ r₀ → sqr x > r₀
>-sqr {x} x≢0 = mulxx>0 (x≢0→x>0∨x<0 x≢0)

2-1=1 : ℕ2ℝ 2 - r₁ ≡ r₁
2-1=1 =
  ℕ2ℝ 2 - r₁
    ≡⟨ subst (λ w → r₁ + (r₁ + r₀) - r₁ ≡ r₁ + w - r₁) (+-neut r₁) (refl (r₁ + (r₁ + r₀) - r₁)) ⟩
  r₁ + r₁ - r₁
    ≡⟨ +-asso r₁ r₁ (- r₁) ⟩
  r₁ + (r₁ - r₁)
    ≡⟨ subst (λ w → r₁ + (r₁ - r₁) ≡ r₁ + w) (+-inve r₁) (refl (r₁ + (r₁ - r₁))) ⟩
  r₁ + r₀
    ≡⟨ +-neut r₁ ⟩
  r₁ ∎

1>0 : r₁ > r₀
1>0 = p₁-helper (>-sqr (1≢0))
  where
    p₁-helper : sqr r₁ > r₀ → r₁ > r₀
    p₁-helper h = subst₂ (λ t₁ t₂ → t₁ > t₂) r₁-sqr (refl r₀) h

1≥0 : r₁ ≥ r₀
1≥0 = inj₁ 1>0

-x=0→x=0 : (x : ℝ) → - x ≡ r₀ → x ≡ r₀
-x=0→x=0 x -x=0 = ≡-*-cancel-r (<→≢(x>0→-x<0 1>0)) p-helper

  where
   p-helper : x * - r₁ ≡ r₀ * - r₁
   p-helper =
     x * - r₁   ≡⟨ *-comm x (- r₁) ⟩
     - r₁ * x   ≡⟨ mul-xy ⟩
     - (r₁ * x) ≡⟨ subst (λ w → - (r₁ * x) ≡ - w) (*-comm r₁ x) (refl (- (r₁ * x))) ⟩
     - (x * r₁) ≡⟨ subst (λ w → - (x * r₁) ≡ - w) (*-neut x) (refl (- (x * r₁))) ⟩
     - x        ≡⟨ -x=0 ⟩
     r₀         ≡⟨ ≡-sym *-right-zero ⟩
     - r₁ * r₀  ≡⟨ *-comm (- r₁) r₀ ⟩
     r₀ * - r₁      ∎

x-y=0→x=y : (x y : ℝ) → x - y ≡ r₀ → x ≡ y
x-y=0→x=y x y h =
     x             ≡⟨ ≡-sym (+-neut x) ⟩
     x + r₀        ≡⟨ subst (λ w → x + r₀ ≡ x + w) (≡-sym (+-inve y)) (refl (x + r₀)) ⟩
     x + (y - y)   ≡⟨ subst (λ w → x + (y - y) ≡ x + w) (+-comm y (- y)) (refl (x + (y - y))) ⟩
     x + (- y + y) ≡⟨ ≡-sym (+-asso x (- y) y) ⟩
     (x - y) + y   ≡⟨ subst (λ w → (x - y) + y ≡ w + y) h (refl ((x - y) + y)) ⟩
     r₀ + y        ≡⟨ +-comm r₀ y ⟩
     y + r₀        ≡⟨ +-neut y ⟩
     y      ∎

2x=x+x : {x : ℝ} → (ℕ2ℝ 2) * x ≡ x + x
2x=x+x {x} =
  (ℕ2ℝ 2) * x     ≡⟨ subst (λ w → ℕ2ℝ 2 * x ≡ (r₁ + w) * x) (+-neut r₁) (refl (ℕ2ℝ 2 * x)) ⟩
  (r₁ + r₁) * x   ≡⟨ subst (λ w → (r₁ + r₁) * x ≡ w) (*-comm (r₁ + r₁) x) (refl ((r₁ + r₁) * x)) ⟩
  x * (r₁ + r₁)   ≡⟨ *-dist x r₁ r₁ ⟩
  x * r₁ + x * r₁ ≡⟨ subst (λ w → x * r₁ + x * r₁ ≡ x * r₁ + w) (*-neut x) (refl (x * r₁ + x * r₁)) ⟩
  x * r₁ + x      ≡⟨ subst (λ w → x * r₁ + x ≡ w + x) (*-neut x) (refl (x * r₁ + x)) ⟩
  x + x ∎

x+1>x : (x : ℝ) → x + r₁ > x
x+1>x x = p₁-helper (>-+-cancel-r (p₂-helper (p₃-helper (p₄-helper 1>0))))

  where
    p₁-helper : r₁ + x > x → x + r₁ > x
    p₁-helper h = subst₂ (λ t₁ t₂ → t₁ > t₂) (+-comm r₁ x) (refl x) h

    p₂-helper : r₁ + (x + (- x)) > r₀ → (r₁ + x) + (- x) > x + (- x)
    p₂-helper h = subst₂ (λ t₁ t₂ → t₁ > t₂) (≡-sym (+-asso r₁ x (- x))) (≡-sym (+-inve x)) h

    p₃-helper : r₁ + r₀ > r₀ → r₁ + (x + (- x)) > r₀
    p₃-helper h = subst₂ (λ t₁ t₂ → t₁ > t₂) (subst (λ w → r₁ + r₀ ≡ r₁ + w) (≡-sym (+-inve x)) (refl (r₁ + r₀))) (refl r₀) h

    p₄-helper : r₁ > r₀ → r₁ + r₀ > r₀
    p₄-helper r₁>r₀ = subst₂ (λ t₁ t₂ → t₁ > t₂) (≡-sym (+-neut r₁)) (refl r₀) r₁>r₀

x<x+1 : (x : ℝ) → x < x + r₁
x<x+1 x = >-to-< (x+1>x x)

2>1 : ℕ2ℝ 2 > r₁
2>1 = p₁-helper (x+1>x r₁)

  where
   p₁-helper : r₁ + r₁ > r₁ → r₁ + (r₁ + r₀) > r₁
   p₁-helper = subst₂ (λ t₁ t₂ → t₁ > t₂) (subst (λ w → r₁ + r₁ ≡ r₁ + w) (≡-sym (+-neut r₁)) (refl (r₁ + r₁))) (refl r₁)

2≢0 : ℕ2ℝ 2 ≢ r₀
2≢0 h = >→≢ (>-trans 2>1 1>0) h

>-inve-r₀ : {x : ℝ} → x > r₀ → x ⁻¹ > r₀
>-inve-r₀ x>r₀ = ≰→> (p₁-helper x>r₀)

  where
   p₁-helper : {x : ℝ} → x > r₀ → ¬ (x ⁻¹ ≤ r₀)
   p₁-helper {x} x>r₀ = p₂-helper x>r₀

    where
      p₂-helper : {x : ℝ} → x > r₀ → x ⁻¹ ≤ r₀ → ⊥
      p₂-helper {x} x>r₀ x⁻¹≤r₀ = case prf1 prf2 x⁻¹≤r₀

       where
         prf1 : x ⁻¹ < r₀ → ⊥
         prf1 x⁻¹<r₀ = p₅-helper (p₄-helper (p₃-helper x⁻¹<r₀))

          where
            p₃-helper : x ⁻¹ < r₀ → x * x ⁻¹ < x * r₀
            p₃-helper = <-*-cong-l x>r₀

            p₄-helper : x * x ⁻¹ < x * r₀ → r₁ < r₀
            p₄-helper h = subst₂ (λ t₁ t₂ → t₁ < t₂) (*-inve x (>→≢ x>r₀)) *-right-zero h

            p₅-helper : r₁ < r₀ → ⊥
            p₅-helper r₁<r₀ = ≥→≮ 1≥0 r₁<r₀

         prf2 : x ⁻¹ ≡ r₀ → ⊥
         prf2 x⁻¹≡r₀ = p₈-helper (p₇-helper (p₆-helper x⁻¹≡r₀))

          where
            p₆-helper : x ⁻¹ ≡ r₀ → x * x ⁻¹ ≡ x * r₀
            p₆-helper = ≡-*-cong-l x

            p₇-helper : x * x ⁻¹ ≡ x * r₀ → r₁ ≡ r₀
            p₇-helper h = subst₂ (λ t₁ t₂ → t₁ ≡ t₂) (*-inve x (>→≢ x>r₀)) *-right-zero h

            p₈-helper : r₁ ≡ r₀ → ⊥
            p₈-helper r₁≡r₀ = 1≢0 r₁≡r₀

>-*-cancel-r : {x y z : ℝ} → z > r₀ → x * z > y * z → x > y
>-*-cancel-r {x} {y} {z} h₁ h₂ = p₁-helper (p₂-helper h₁ (p₃-helper h₁ (p₄-helper h₁ h₂)))

  where
    p₁-helper : {x y : ℝ} → x * r₁ > y * r₁ → x > y
    p₁-helper {x} {y} h = subst₂ (λ t₁ t₂ → t₁ > t₂) (*-neut x) (*-neut y) h

    p₂-helper : {x y z : ℝ} → z > r₀ → x * (z * (z ⁻¹)) > y * (z * (z ⁻¹)) → x * r₁ > y * r₁
    p₂-helper {x} {y} {z} h₁ h₂ = subst₂ (λ t₁ t₂ → x * t₁ > y * t₂) (*-inve z (>→≢ h₁)) (*-inve z (>→≢ h₁)) h₂

    p₃-helper : {x y z : ℝ} → z > r₀ → (x * z) * (z ⁻¹) > (y * z) * (z ⁻¹) → x * (z * (z ⁻¹)) > y * (z * (z ⁻¹))
    p₃-helper {x} {y} {z} h₁ h₂ = p-helper h₂

     where
       p-helper : {x y x₁ x₂ : ℝ} → (x * x₁) * x₂ > (y * x₁) * x₂ → x * (x₁ * x₂) > y * (x₁ * x₂)
       p-helper {x} {y} {x₁} {x₂} h = subst₂ (λ t₁ t₂ → t₁ > t₂) (*-asso x x₁ x₂) (*-asso y x₁ x₂) h

    p₄-helper : {x y z : ℝ} → z > r₀ → x * z > y * z → (x * z) * (z ⁻¹) > (y * z) * (z ⁻¹)
    p₄-helper {x} {y} {z} h₁ h₂ = >-*-cong-r (>-inve-r₀ h₁) h₂

>-*-cancel-l : {x y z : ℝ} → z > r₀ → z * x > z * y → x > y
>-*-cancel-l {x} {y} {z} h₁ h₂ = >-*-cancel-r h₁ (p-helper h₂)

  where
    p-helper : {x y z : ℝ} → z * x > z * y → x * z > y * z
    p-helper {x} {y} {z} h = subst₂ (λ t₁ t₂ → t₁ > t₂) (*-comm z x) (*-comm z y) h

*-dist-r : (x y z : ℝ) → (y + z) * x ≡ y * x + z * x
*-dist-r x y z =
  (y + z) * x       ≡⟨ subst (λ w → ((y + z) * x) ≡ (w)) ( ≡-sym ( *-comm x (y + z) ) ) (refl ((y + z) * x)) ⟩
  x * (y + z)       ≡⟨ *-dist x y z ⟩
  (x * y) + (x * z) ≡⟨ subst (λ w → ((x * y) + (x * z)) ≡ (w + (x * z))) (*-comm x y) (refl (x * y + x * z)) ⟩
  (y * x) + (x * z) ≡⟨ subst (λ w → ((y * x) + (x * z)) ≡ ((y * x) + w)) (*-comm x z) (refl (y * x + x * z)) ⟩
  (y * x) + (z * x) ∎

*-double-dist : (a b c d : ℝ) → (a + b) * (c + d) ≡ (a * c + a * d) + (b * c + b * d)
*-double-dist a b c d =
  (a + b) * (c + d)
   ≡⟨ *-dist (a + b) c d ⟩
  (a + b) * c + (a + b) * d
   ≡⟨ subst (λ w → (a + b) * c + (a + b) * d ≡ w + (a + b) * d) (*-dist-r c a b) (refl ((a + b) * c + (a + b) * d)) ⟩
  (a * c + b * c) + (a + b) * d
   ≡⟨ subst (λ w → a * c + b * c + (a + b) * d ≡ a * c + b * c + w) (*-dist-r d a b) (refl (a * c + b * c + (a + b) * d)) ⟩
  (a * c + b * c) + (a * d + b * d)
   ≡⟨ +-asso (a * c) (b * c) (a * d + b * d) ⟩
  a * c + (b * c + (a * d + b * d))
   ≡⟨ subst (λ w → a * c + (b * c + (a * d + b * d)) ≡ a * c + w) (≡-sym (+-asso (b * c) (a * d) (b * d)))
   (refl (a * c + (b * c + (a * d + b * d)))) ⟩
  a * c + ((b * c + a * d) + b * d)
   ≡⟨ subst (λ w → a * c + (b * c + a * d + b * d) ≡ a * c + (w + b * d)) (+-comm (b * c) (a * d))
   (refl (a * c + (b * c + a * d + b * d))) ⟩
  a * c + ((a * d + b * c) + b * d)
   ≡⟨ subst (λ w → a * c + (a * d + b * c + b * d) ≡ a * c + w) (+-asso (a * d) (b * c) (b * d)) (refl (a * c + (a * d + b * c + b * d))) ⟩
  a * c + (a * d + (b * c + b * d))
   ≡⟨ ≡-sym (+-asso (a * c) (a * d) (b * c + b * d)) ⟩
  (a * c + a * d) + (b * c + b * d) ∎

-- Trinomial Perfect Square.

TPS : (x y : ℝ) → sqr (x + y) ≡ sqr x + ℕ2ℝ 2 * (x * y) + sqr y
TPS x y =
  sqr (x + y)
    ≡⟨ *-double-dist x y x y ⟩
  sqr x + x * y + (y * x + sqr y)
    ≡⟨ +-asso (sqr x) (x * y) (y * x + sqr y) ⟩
  sqr x + (x * y + (y * x + sqr y))
    ≡⟨ subst (λ w → sqr x + (x * y + (y * x + sqr y)) ≡ sqr x + w) (≡-sym (+-asso (x * y) (y * x) (sqr y)))
    (refl (sqr x + (x * y + (y * x + sqr y)))) ⟩
  sqr x + ((x * y + y * x) + sqr y)
    ≡⟨ subst (λ w → sqr x + (x * y + y * x + sqr y) ≡ sqr x + (x * y + w + sqr y)) (*-comm y x)
    (refl (sqr x + (x * y + y * x + sqr y))) ⟩
  sqr x + ((x * y + x * y) + sqr y)
    ≡⟨ subst (λ w → sqr x + (x * y + x * y + sqr y) ≡ sqr x + (w + sqr y)) (≡-sym 2x=x+x)
    (refl (sqr x + (x * y + x * y + sqr y))) ⟩
  sqr x + (ℕ2ℝ 2 * (x * y) + sqr y)
    ≡⟨ ≡-sym (+-asso (sqr x) (ℕ2ℝ 2 * (x * y)) (sqr y)) ⟩
  sqr x + ℕ2ℝ 2 * (x * y) + sqr y   ∎

TPS1 : (x : ℝ) → sqr (x + r₁) ≡ sqr x + ℕ2ℝ 2 * x + r₁
TPS1 x =
  sqr (x + r₁)
   ≡⟨ TPS x r₁ ⟩
  sqr x + ℕ2ℝ 2 * (x * r₁) + sqr r₁
   ≡⟨ subst (λ w → sqr x + ℕ2ℝ 2 * (x * r₁) + sqr r₁ ≡ sqr x + ℕ2ℝ 2 * w + sqr r₁) (*-neut x)
   (refl (sqr x + ℕ2ℝ 2 * (x * r₁) + sqr r₁)) ⟩
  sqr x + ℕ2ℝ 2 * x + sqr r₁
   ≡⟨ subst (λ w → sqr x + ℕ2ℝ 2 * x + sqr r₁ ≡ sqr x + ℕ2ℝ 2 * x + w) (*-neut r₁)
   (refl (sqr x + ℕ2ℝ 2 * x + sqr r₁)) ⟩
  sqr x + ℕ2ℝ 2 * x + r₁ ∎

*-inve-product : {x y : ℝ} → x ≢ r₀ → y ≢ r₀ → (x * y) ≢ r₀ → (x * y) ⁻¹ ≡ x ⁻¹ * y ⁻¹
*-inve-product {x} {y} h1 h2 h3 =
  (x * y) ⁻¹
    ≡⟨ ≡-sym (*-neut ((x * y) ⁻¹)) ⟩
  (x * y) ⁻¹ * r₁
    ≡⟨ *-comm ((x * y) ⁻¹) r₁ ⟩
  r₁ * (x * y) ⁻¹
    ≡⟨ subst (λ w → r₁ * (x * y) ⁻¹ ≡ w * (x * y) ⁻¹) (≡-sym (p-helper h1 h2) ) (refl (r₁ * (x * y) ⁻¹)) ⟩
  ((x ⁻¹ * y ⁻¹) * (x * y)) * (x * y) ⁻¹
    ≡⟨ *-asso (x ⁻¹ * y ⁻¹) (x * y) ((x * y) ⁻¹) ⟩
  (x ⁻¹ * y ⁻¹) * (x * y * (x * y) ⁻¹)
    ≡⟨ subst (λ w → (x ⁻¹ * y ⁻¹) * ((x * y) * (x * y) ⁻¹) ≡ (x ⁻¹ * y ⁻¹) * w) (*-inve (x * y) h3) (refl (x ⁻¹ * y ⁻¹ * (x * y * (x * y) ⁻¹))) ⟩
  (x ⁻¹ * y ⁻¹) * r₁
    ≡⟨ *-neut (x ⁻¹ * y ⁻¹) ⟩
  x ⁻¹ * y ⁻¹ ∎

  where
    p-helper : {x y : ℝ} → x ≢ r₀ → y ≢ r₀ → (x ⁻¹ * y ⁻¹) * (x * y) ≡ r₁
    p-helper {x} {y} h1 h2 =
      (x ⁻¹ * y ⁻¹) * (x * y)
        ≡⟨ subst (λ w → (x ⁻¹ * y ⁻¹) * (x * y) ≡ (x ⁻¹ * y ⁻¹) * w) (*-comm x y) (refl (x ⁻¹ * y ⁻¹ * (x * y))) ⟩
      (x ⁻¹ * y ⁻¹) * (y * x)
        ≡⟨ ≡-sym (*-asso (x ⁻¹ * y ⁻¹) y x) ⟩
      ((x ⁻¹ * y ⁻¹) * y) * x
        ≡⟨ subst (λ w → ((x ⁻¹ * y ⁻¹) * y) * x ≡ w * x) (*-asso (x ⁻¹) (y ⁻¹) y) (refl (x ⁻¹ * y ⁻¹ * y * x)) ⟩
      (x ⁻¹ * (y ⁻¹ * y)) * x
        ≡⟨ subst (λ w → (x ⁻¹ * (y ⁻¹ * y)) * x ≡ (x ⁻¹ * w) * x) (*-comm (y ⁻¹) y) (refl (x ⁻¹ * (y ⁻¹ * y) * x)) ⟩
      (x ⁻¹ * (y * y ⁻¹)) * x
        ≡⟨ subst (λ w → (x ⁻¹ * (y * y ⁻¹)) * x ≡ (x ⁻¹ * w) * x) (*-inve y h2) (refl (x ⁻¹ * (y * y ⁻¹) * x)) ⟩
      (x ⁻¹ * r₁) * x
        ≡⟨ subst (λ w → (x ⁻¹ * r₁) * x ≡ w * x) (*-neut (x ⁻¹)) (refl (x ⁻¹ * r₁ * x)) ⟩
      x ⁻¹ * x
        ≡⟨ *-comm (x ⁻¹) x ⟩
      x * x ⁻¹
        ≡⟨ *-inve x h1 ⟩
      r₁ ∎

-- Adding Heterogeneous Fractions.

+-fractional : {a b c d : ℝ} → b ≢ r₀ → d ≢ r₀ → a * b ⁻¹ + c * d ⁻¹ ≡ (a * d + b * c) * (b * d) ⁻¹
+-fractional {a} {b} {c} {d} b≠0 d≠0 = ≡-sym p-helper

  where
   p-helper : (a * d + b * c) * (b * d) ⁻¹ ≡ a * b ⁻¹ + c * d ⁻¹
   p-helper =
     (a * d + b * c) * (b * d) ⁻¹
      ≡⟨ *-dist-r ((b * d) ⁻¹) (a * d) (b * c) ⟩
     (a * d) * (b * d) ⁻¹ + b * c * (b * d) ⁻¹
      ≡⟨ subst (λ w → (a * d) * (b * d) ⁻¹ + b * c * (b * d) ⁻¹ ≡ w + b * c * (b * d) ⁻¹) (*-asso a d ((b * d) ⁻¹))
      (refl (a * d * (b * d) ⁻¹ + b * c * (b * d) ⁻¹)) ⟩
     a * (d * (b * d) ⁻¹) + b * c * (b * d) ⁻¹
      ≡⟨ subst (λ w → a * (d * (b * d) ⁻¹) + b * c * (b * d) ⁻¹ ≡ a * (d * w ⁻¹) + b * c * (b * d) ⁻¹) (*-comm b d)
      (refl (a * (d * (b * d) ⁻¹) + b * c * (b * d) ⁻¹)) ⟩
     a * (d * (d * b) ⁻¹) + (b * c) * (b * d) ⁻¹
      ≡⟨ subst (λ w → a * (d * (d * b) ⁻¹) + b * c * (b * d) ⁻¹ ≡ a * (d * w) + b * c * (b * d) ⁻¹)
      (*-inve-product d≠0 b≠0 (*-≢-zero d≠0 b≠0)) (refl (a * (d * (d * b) ⁻¹) + b * c * (b * d) ⁻¹)) ⟩
     a * (d * (d ⁻¹ * b ⁻¹)) + (b * c) * (b * d) ⁻¹
      ≡⟨ subst (λ w → a * (d * (d ⁻¹ * b ⁻¹)) + b * c * (b * d) ⁻¹ ≡ a * w + b * c * (b * d) ⁻¹)
      (≡-sym (*-asso d (d ⁻¹) (b ⁻¹))) (refl (a * (d * (d ⁻¹ * b ⁻¹)) + (b * c) * (b * d) ⁻¹)) ⟩
     a * ((d * d ⁻¹) * b ⁻¹) + (b * c) * (b * d) ⁻¹
      ≡⟨ subst (λ w → a * (d * d ⁻¹ * b ⁻¹) + (b * c) * (b * d) ⁻¹ ≡ a * (w * b ⁻¹) + b * c * (b * d) ⁻¹) (*-inve d d≠0)
      (refl (a * (d * d ⁻¹ * b ⁻¹) + b * c * (b * d) ⁻¹)) ⟩
     a * (r₁ * b ⁻¹) + (b * c) * (b * d) ⁻¹
      ≡⟨ subst (λ w → a * (r₁ * b ⁻¹) + b * c * (b * d) ⁻¹ ≡ a * w + b * c * (b * d) ⁻¹) (*-comm r₁ (b ⁻¹))
      (refl (a * (r₁ * b ⁻¹) + b * c * (b * d) ⁻¹)) ⟩
     a * (b ⁻¹ * r₁) + (b * c) * (b * d) ⁻¹
      ≡⟨ subst (λ w → a * (b ⁻¹ * r₁) + b * c * (b * d) ⁻¹ ≡ a * w + b * c * (b * d) ⁻¹) (*-neut (b ⁻¹))
      (refl (a * (b ⁻¹ * r₁) + b * c * (b * d) ⁻¹)) ⟩
     a * b ⁻¹ + (b * c) * (b * d) ⁻¹
      ≡⟨ subst (λ w → a * b ⁻¹ + b * c * (b * d) ⁻¹ ≡ a * b ⁻¹ + w * (b * d) ⁻¹) (*-comm b c)
      (refl (a * b ⁻¹ + b * c * (b * d) ⁻¹)) ⟩
     a * b ⁻¹ + (c * b) * (b * d) ⁻¹
      ≡⟨ subst (λ w → a * b ⁻¹ + c * b * (b * d) ⁻¹ ≡ a * b ⁻¹ + w) (*-asso c b ((b * d) ⁻¹))
      (refl (a * b ⁻¹ + c * b * (b * d) ⁻¹)) ⟩
     a * b ⁻¹ + c * (b * (b * d) ⁻¹)
      ≡⟨ subst (λ w → a * b ⁻¹ + c * (b * (b * d) ⁻¹) ≡ a * b ⁻¹ + c * (b * w)) (*-inve-product b≠0 d≠0 (*-≢-zero b≠0 d≠0))
      (refl (a * b ⁻¹ + c * (b * (b * d) ⁻¹))) ⟩
     a * b ⁻¹ + c * (b * (b ⁻¹ * d ⁻¹))
      ≡⟨ subst (λ w → a * b ⁻¹ + c * (b * (b ⁻¹ * d ⁻¹)) ≡ a * b ⁻¹ + c * w) (≡-sym (*-asso b (b ⁻¹) (d ⁻¹)))
      (refl (a * b ⁻¹ + c * (b * (b ⁻¹ * d ⁻¹)))) ⟩
     a * b ⁻¹ + c * ((b * b ⁻¹) * d ⁻¹)
      ≡⟨ subst (λ w → a * b ⁻¹ + c * (b * b ⁻¹ * d ⁻¹) ≡ a * b ⁻¹ + c * (w * d ⁻¹)) (*-inve b b≠0)
      (refl (a * b ⁻¹ + c * (b * b ⁻¹ * d ⁻¹))) ⟩
     a * b ⁻¹ + c * (r₁ * d ⁻¹)
      ≡⟨ subst (λ w → a * b ⁻¹ + c * (r₁ * d ⁻¹) ≡ a * b ⁻¹ + c * w) (*-comm r₁ (d ⁻¹)) (refl (a * b ⁻¹ + c * (r₁ * d ⁻¹))) ⟩
     a * b ⁻¹ + c * (d ⁻¹ * r₁)
     ≡⟨ subst (λ w → a * b ⁻¹ + c * (d ⁻¹ * r₁) ≡ a * b ⁻¹ + c * w) (*-neut (d ⁻¹)) (refl (a * b ⁻¹ + c * (d ⁻¹ * r₁))) ⟩
     a * b ⁻¹ + c * d ⁻¹   ∎

-- One is equal to its multiplicative inverse.

1≡1⁻¹ : r₁ ≡ r₁ ⁻¹
1≡1⁻¹ =
  r₁         ≡⟨ ≡-sym (*-inve r₁ 1≢0) ⟩
  r₁ * r₁ ⁻¹ ≡⟨ *-comm r₁ (r₁ ⁻¹) ⟩
  r₁ ⁻¹ * r₁ ≡⟨ *-neut (r₁ ⁻¹) ⟩
  r₁ ⁻¹      ∎
