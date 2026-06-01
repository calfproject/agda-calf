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

  field
    seal :
      (a : cmp) (a◦ : ⟨ ABS ⟩ → cmp)
      → ((abs : ⟨ ABS ⟩) → a ⊑[ U ] a◦ abs)
      → cmp
    seal/abs : ∀ {a a◦ a⊑a◦} (abs : ⟨ ABS ⟩) → seal a a◦ a⊑a◦ ≡ a◦ abs
    seal/charge : ∀ {a a◦ a⊑a◦ c} →
      charge c (seal a a◦ a⊑a◦) ≡
      seal (charge c a) (charge c ∘ a◦) (⊑ᵛ-mono {U} {U} (charge c) ∘ a⊑a◦)

  -- field
  --   effect : val (M .fst .F-ob U) → cmp
  --   effect/unit : ∀ {a} → effect (M .snd .η .N-ob _ a) ≡ a
  --   effect/mult : ∀ {a} → effect (M .snd .μ .N-ob _ a) ≡ effect (M .fst .F-hom effect a)

  -- charge : val ℂ → cmp → cmp
  -- charge c a = effect (chargeᴹ c (M .snd .η .N-ob _ a))

  -- charge/0 : ∀ {a} → charge 0ℂ a ≡ a
  -- charge/0 = cong effect chargeᴹ/0 ∙ effect/unit

  -- charge/+ : ∀ {a c₁ c₂} → charge (c₁ +ℂ c₂) a ≡ charge c₁ (charge c₂ a)
  -- charge/+ = cong effect chargeᴹ/+ ∙ {! ?  !}

  -- seal :
  --   (a : cmp) (a◦ : ⟨ ABS ⟩ → cmp)
  --   → ((abs : ⟨ ABS ⟩) → a ⊑[ U ] a◦ abs)
  --   → cmp
  -- seal a a◦ a⊑a◦ = effect $
  --   sealᴹ
  --     (M .snd .η .N-ob _ a)
  --     (λ abs → M .snd .η .N-ob _ (a◦ abs))
  --     (λ abs → ⊑ᵛ-mono {U} {M .fst .F-ob U} (M .snd .η .N-ob _) (a⊑a◦ abs))

  -- seal/abs : ∀ {a a◦ a⊑a◦} (abs : ⟨ ABS ⟩) → seal a a◦ a⊑a◦ ≡ a◦ abs
  -- seal/abs = {!   !}

  -- seal/charge : ∀ {a a◦ a⊑a◦ c} →
  --   charge c (seal a a◦ a⊑a◦) ≡
  --   seal (charge c a) (charge c ∘ a◦) (⊑ᵛ-mono {U} {U} (charge c) ∘ a⊑a◦)
  -- seal/charge = {!   !}

  -- seal/unit : ∀ {a} → seal a (λ _ → a) (λ _ → ⊑ᵛ-refl {U}) ≡ a
  -- seal/unit = {!   !}

  -- seal/mult : ∀ {a a◦ a◦' a⊑a◦} {a◦⊑a◦' : (abs : ⟨ ABS ⟩) → a◦ abs ⊑[ U ] a◦' abs} →
  --   seal (seal a a◦ a⊑a◦) a◦' (λ abs → ⊑ᵛ-trans {U} (≡⇒⊑ᵛ {U} (seal/abs abs)) (a◦⊑a◦' abs)) ≡
  --   seal a a◦' (λ abs → ⊑ᵛ-trans {U} (a⊑a◦ abs) (a◦⊑a◦' abs))
  -- seal/mult = {!   !}
open 𝒞 public

variable
  A B C : 𝒞

record _⊸_ (A B : 𝒞) : Type where
  field
    U : cmp A → cmp B
    charge : ∀ c a → U (A .charge c a) ≡ B .charge c (U a)
    seal : ∀ a a◦ h → U (A .seal a a◦ h) ≡ B .seal (U a) (U ∘ a◦) (⊑ᵛ-mono {𝒞.U A} {𝒞.U B} U ∘ h)
open _⊸_ public

id⊸ : A ⊸ A
id⊸ .U a = a
id⊸ .charge _ _ = refl
id⊸ {A} .seal _ _ _ = refl

_⨾⊸_ : (A ⊸ B) → (B ⊸ C) → (A ⊸ C)
(f ⨾⊸ g) .U = g .U ∘ f .U
(f ⨾⊸ g) .charge c a = cong (g .U) (f .charge c a) ∙ g .charge c (f .U a)
_⨾⊸_ {A} {B} f g .seal a a◦ h =
  cong (g .U) (f .seal a a◦ h)
  ∙ g .seal (f .U a) (f .U ∘ a◦) (⊑ᵛ-mono {U A} {U B} (f .U) ∘ h)

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
CHARGE {A} c .seal a a◦ h = A .seal/charge

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
𝒞-path {A} {B} U-path charge-path i .seal = {!   !}
𝒞-path {A} {B} U-path charge-path i .seal/abs = {!   !}
𝒞-path {A} {B} U-path charge-path i .seal/charge = {!   !}

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
⊸-path A-path B-path {f₀ = f₀} {f₁ = f₁} U-path i .seal = {!   !}

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
