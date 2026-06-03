open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Calf.Computation where

open import Calf.Core.Abstract
open import Calf.Value
open import Calf.Core.Monad
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Univalence using (ua; ua→; ua-gluePath)

record 𝒞 : Type₁ where
  field
    U : 𝒱
  cmp = val U

  field
    charge : val ℂ → cmp → cmp
    charge/0 : ∀ {a} → charge 0ℂ a ≡ a
    charge/+ : ∀ {a c₁ c₂} → charge (c₁ +ℂ c₂) a ≡ charge c₁ (charge c₂ a)
open 𝒞 public

variable
  A B C : 𝒞

infix 1 _⊸_
record _⊸_ (A B : 𝒞) : Type where
  field
    U : cmp A → cmp B
    charge : ∀ c a → U (A .charge c a) ≡ B .charge c (U a)
open _⊸_ public

isEquivᶜ : (A ⊸ B) → Type
isEquivᶜ f = isEquiv (U f)

idᶜ : A ⊸ A
idᶜ .U a = a
idᶜ .charge _ _ = refl

infixl 9 _⨾ᶜ_
_⨾ᶜ_ : (A ⊸ B) → (B ⊸ C) → (A ⊸ C)
(f ⨾ᶜ g) .U = g .U ∘ f .U
(f ⨾ᶜ g) .charge c a = cong (g .U) (f .charge c a) ∙ g .charge c (f .U a)

CHARGE : val ℂ → A ⊸ A
CHARGE {A} c .U = charge A c
CHARGE {A} c .charge c' a =
    A .charge c (A .charge c' a)
  ≡⟨ sym (A .charge/+ {a = a} {c₁ = c} {c₂ = c'}) ⟩
    A .charge (c +ℂ c') a
  ≡⟨ cong (λ d → A .charge d a) (+ℂ-comm c c') ⟩
    A .charge (c' +ℂ c) a
  ≡⟨ A .charge/+ {a = a} {c₁ = c'} {c₂ = c} ⟩
    A .charge c' (A .charge c a)
  ∎

CHARGE-comm : ∀ c₁ c₂ → CHARGE {A} c₁ ⨾ᶜ CHARGE c₂ ≡ CHARGE c₂ ⨾ᶜ CHARGE c₁
CHARGE-comm = {!   !}

isPropCharge/0
  : {U : 𝒱} (charge : val ℂ → val U → val U)
  → isProp (∀ {a} → charge 0ℂ a ≡ a)
isPropCharge/0 {U} charge =
  isPropImplicitΠ λ a → U .is-set (charge 0ℂ a) a

isPropCharge/+
  : {U : 𝒱} (charge : val ℂ → val U → val U)
  → isProp (∀ {a c₁ c₂} → charge (c₁ +ℂ c₂) a ≡ charge c₁ (charge c₂ a))
isPropCharge/+ {U} charge =
  isPropImplicitΠ3 λ a c₁ c₂ →
    U .is-set (charge (c₁ +ℂ c₂) a) (charge c₁ (charge c₂ a))

𝒞-path
  : {A B : 𝒞}
  → (U-path : A .U ≡ B .U)
  → PathP
      (λ i → val ℂ → val (U-path i) → val (U-path i))
      (charge A)
      (charge B)
  → A ≡ B
𝒞-path {A} {B} U-path charge-path i .U = U-path i
𝒞-path {A} {B} U-path charge-path i .charge = charge-path i
𝒞-path {A} {B} U-path charge-path i .charge/0 =
  isProp→PathP
    (λ i → isPropCharge/0 {U = U-path i} (charge-path i))
    (A .charge/0)
    (B .charge/0)
    i
𝒞-path {A} {B} U-path charge-path i .charge/+ =
  isProp→PathP
    (λ i → isPropCharge/+ {U = U-path i} (charge-path i))
    (A .charge/+)
    (B .charge/+)
    i

isProp⊸charge
  : (A B : 𝒞) (f : cmp A → cmp B)
  → isProp ((c : val ℂ) (a : cmp A) → f (A .charge c a) ≡ B .charge c (f a))
isProp⊸charge A B f =
  isPropΠ2 λ c a → B .U .is-set (f (A .charge c a)) (B .charge c (f a))

⊸-path
  : {A₀ A₁ B₀ B₁ : 𝒞}
  → (A-path : A₀ ≡ A₁)
  → (B-path : B₀ ≡ B₁)
  → {f₀ : A₀ ⊸ B₀}
  → {f₁ : A₁ ⊸ B₁}
  → PathP (λ i → cmp (A-path i) → cmp (B-path i)) (f₀ .U) (f₁ .U)
  → PathP (λ i → A-path i ⊸ B-path i) f₀ f₁
⊸-path A-path B-path {f₀ = f₀} {f₁ = f₁} U-path i .U = U-path i
⊸-path A-path B-path {f₀ = f₀} {f₁ = f₁} U-path i .charge =
  isProp→PathP
    (λ i → isProp⊸charge (A-path i) (B-path i) (U-path i))
    (f₀ .charge)
    (f₁ .charge)
    i

idᶜ⨾ᶜf≡f : (f : A ⊸ B) → idᶜ ⨾ᶜ f ≡ f
idᶜ⨾ᶜf≡f f = ⊸-path refl refl refl

charge-path-inv
  : {X Y : Type}
  → (e : X ≃ Y)
  → (chargeX : val ℂ → X → X)
  → (chargeY : val ℂ → Y → Y)
  → ((c : val ℂ) (y : Y) → invEq e (chargeY c y) ≡ chargeX c (invEq e y))
  → PathP
      (λ i → val ℂ → ua (invEquiv e) i → ua (invEquiv e) i)
      chargeY
      chargeX
charge-path-inv e chargeX chargeY h =
  funExt λ c →
    ua→ {e = invEquiv e} λ y →
      ua-gluePath (invEquiv e) (h c y)

charge-path
  : {X Y : Type}
  → (e : X ≃ Y)
  → (chargeX : val ℂ → X → X)
  → (chargeY : val ℂ → Y → Y)
  → ((c : val ℂ) (x : X) → e .fst (chargeX c x) ≡ chargeY c (e .fst x))
  → PathP
      (λ i → val ℂ → ua e i → ua e i)
      chargeX
      chargeY
charge-path e chargeX chargeY h =
  funExt λ c →
    ua→ {e = e} λ x →
      ua-gluePath e (h c x)
