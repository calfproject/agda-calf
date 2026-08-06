module Calf.Computation.Tensor.Base where

open import Calf.Core.Cost
open import Calf.Value
open import Calf.Value.Nat
open import Calf.Computation

open import Cubical.HITs.SetTruncation

⊤ : 𝒞
⊤ .U = ℂ
⊤ .is-set = isSetℂ
⊤ .charge = _+ℂ_
⊤ .charge/0 = +ℂ-identityˡ _
⊤ .charge/+ = +ℂ-assoc _ _ _

trivᶜ : U ⊤
trivᶜ = 0

cmp : 𝒞 → 𝒱
cmp = ⊤ ⊸_

cmp→U : cmp A → U A
cmp→U e = e .U 0ℂ

U→cmp : U A → cmp A
U→cmp {A} e = record { U = flip (A .charge) e ; charge = λ _ _ → A .charge/+ }

module _ where
  data _⊛_ (A B : 𝒞) : 𝒱 where
    inj : (a : U A) (b : U B) → A ⊛ B
    law : ∀ c a b → inj (A .charge c a) b ≡ inj a (B .charge c b)

  charge⊛ : ℂ → A ⊛ B → A ⊛ B
  charge⊛ {A} c (inj a b) = inj (A .charge c a) b
  charge⊛ {A} {B} c (law c' a b i) =
    ( cong (λ z → inj {A} {B} z b) (charge/comm A)
    ∙ law c' (A .charge c a) b ) i

  ∥∥₂-≡
    : isSet Y
    → (f g : ∥ X ∥₂ → Y)
    → (∀ x → f ∣ x ∣₂ ≡ g ∣ x ∣₂)
    → ∀ z → f z ≡ g z
  ∥∥₂-≡ isSetY f g p = elim (λ z → isProp→isSet (isSetY (f z) (g z))) p

  module _ {A B : 𝒞} where
    ⊛-elimProp
      : {P : A ⊛ B → 𝒱}
      → (∀ w → isProp (P w))
      → (∀ a b → P (inj a b))
      → ∀ w → P w
    ⊛-elimProp pP f (inj a b) = f a b
    ⊛-elimProp pP f (law c a b i) =
      isProp→PathP (λ i → pP (law c a b i))
        (f (A .charge c a) b)
        (f a (B .charge c b))
        i

    ⊛-≡
      : isSet Y
      → (f g : ∥ A ⊛ B ∥₂ → Y)
      → (∀ a b → f ∣ inj a b ∣₂ ≡ g ∣ inj a b ∣₂)
      → ∀ z → f z ≡ g z
    ⊛-≡ isSetY f g p = ∥∥₂-≡ isSetY f g (⊛-elimProp (λ _ → isSetY _ _) p)

  opaque
    _⊗_ : 𝒞 → 𝒞 → 𝒞
    (A ⊗ B) .U = ∥ A ⊛ B ∥₂
    (A ⊗ B) .is-set = squash₂
    (A ⊗ B) .charge c = map (charge⊛ c)
    (A ⊗ B) .charge/0 {x} =
      ⊛-≡ squash₂ (map (charge⊛ 0ℂ)) (λ z → z)
        (λ a b → cong (λ z → ∣ inj {A} z b ∣₂) (A .charge/0 {a}))
        x
    (A ⊗ B) .charge/+ {x} {c₁} {c₂} =
      ⊛-≡ squash₂ (map (charge⊛ (c₁ +ℂ c₂))) (λ z → map (charge⊛ c₁) (map (charge⊛ c₂) z))
        (λ a b → cong (λ z → ∣ inj {A} z b ∣₂) (A .charge/+ {a} {c₁} {c₂}))
        x

  opaque
    unfolding _⊗_

    _∥_ : U A → U B → U (A ⊗ B)
    a ∥ b = ∣ inj a b ∣₂

    map₂ : ∀ {A₁ A₂ B₁ B₂}
      → (A₁ ⊸ B₁)
      → (A₂ ⊸ B₂)
      → (A₁ ⊗ A₂ ⊸ B₁ ⊗ B₂)
    map₂ {A₁} {A₂} {B₁} {B₂} f g = mk
      where
        h : A₁ ⊛ A₂ → B₁ ⊛ B₂
        h (inj a₁ a₂) = inj (f .U a₁) (g .U a₂)
        h (law c a₁ a₂ i) =
          ( cong (λ z → inj z (g .U a₂)) (f .charge c a₁)
          ∙ law c (f .U a₁) (g .U a₂)
          ∙ cong (inj (f .U a₁)) (sym (g .charge c a₂)) ) i

        mk : A₁ ⊗ A₂ ⊸ B₁ ⊗ B₂
        mk .U = map h
        mk .charge c =
          ⊛-≡ squash₂
            (λ z → mk .U ((A₁ ⊗ A₂) .charge c z))
            (λ z → (B₁ ⊗ B₂) .charge c (mk .U z))
            (λ a₁ a₂ → cong (λ z → ∣ inj z (g .U a₂) ∣₂) (f .charge c a₁))

⊗ᵏ : ℕ → 𝒞 → 𝒞
⊗ᵏ zero A = ⊤
⊗ᵏ (suc k) A = A ⊗ (⊗ᵏ k A)

⊗ᵏ' : ℕ → 𝒞 → (𝒞 → 𝒞) → 𝒞
⊗ᵏ' zero A₀ Af = ⊤
⊗ᵏ' (suc k) A₀ Af = A₀ ⊗ (⊗ᵏ' k (Af A₀) Af)

opaque
  unfolding _⊗_

  ⊗-identityʳ : A ⊗ ⊤ ≡ A
  ⊗-identityʳ {A = A} = conservativity fwd fwd-equiv
    where
      fwd-U : A ⊛ ⊤ → U A
      fwd-U (inj a c) = A .charge c a
      fwd-U (law c' a c i) =
        ( sym (A .charge/+ {a} {c} {c'})
        ∙ cong (λ d → A .charge d a) (+ℂ-comm c c') ) i

      fwd : A ⊗ ⊤ ⊸ A
      fwd .U = rec (A .is-set) fwd-U
      fwd .charge c₀ =
        ⊛-≡ (A .is-set)
          (λ z → fwd .U ((A ⊗ ⊤) .charge c₀ z))
          (λ z → A .charge c₀ (fwd .U z))
          (λ a c → charge/comm A)

      fwd-equiv : isEquivᶜ fwd
      fwd-equiv = isoToIsEquiv (iso (fwd .U) inv sect retr)
        where
          inv : U A → U (A ⊗ ⊤)
          inv a = ∣ inj a 0ℂ ∣₂

          sect : ∀ a → fwd .U (inv a) ≡ a
          sect a = A .charge/0

          retr : ∀ z → inv (fwd .U z) ≡ z
          retr =
            ⊛-≡ squash₂ (λ z → inv (fwd .U z)) (λ z → z)
              (λ a c →
                  cong ∣_∣₂ (law c a 0ℂ)
                ∙ cong (λ d → ∣ inj a d ∣₂) (+ℂ-identityʳ c))

  ⊗-comm : A ⊗ B ≡ B ⊗ A
  ⊗-comm {A = A} {B = B} = conservativity fwd fwd-equiv
    where
      fwd-U : A ⊛ B → B ⊛ A
      fwd-U (inj a b) = inj b a
      fwd-U (law c a b i) = sym (law c b a) i

      fwd : A ⊗ B ⊸ B ⊗ A
      fwd .U = map fwd-U
      fwd .charge c = {!    !}

      fwd-equiv : isEquivᶜ fwd
      fwd-equiv = {!   !}

  ⊗-identityˡ : ⊤ ⊗ A ≡ A
  ⊗-identityˡ = ⊗-comm ∙ ⊗-identityʳ

  ⊗-assoc : A ⊗ (B ⊗ C) ≡ (A ⊗ B) ⊗ C
  ⊗-assoc = {!   !}
