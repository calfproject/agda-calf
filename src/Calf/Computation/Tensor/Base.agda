module Calf.Computation.Tensor.Base where

open import Calf.Core.Cost
open import Calf.Value
open import Calf.Computation

open import Cubical.HITs.SetTruncation

⊤ : 𝒞
⊤ .U = ℂ
⊤ .is-set = isSetℂ
⊤ .charge = _+ℂ_
⊤ .charge/0 = +ℂ-identityˡ _
⊤ .charge/+ = +ℂ-assoc _ _ _

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

  _∥_ : U A → U B → U (A ⊗ B)
  a ∥ b = ∣ inj a b ∣₂

  ⊗-rec : {A B C : 𝒞}
    → (h : U A → U B → U C)
    → (∀ c a b → h (A .charge c a) b ≡ C .charge c (h a b))
    → (∀ c a b → h a (B .charge c b) ≡ C .charge c (h a b))
    → (A ⊗ B) ⊸ C
  ⊗-rec {A} {B} {C} h hl hr .U = rec (C .is-set) h₀
    where
      h₀ : A ⊛ B → U C
      h₀ (inj a b) = h a b
      h₀ (law c a b i) = (hl c a b ∙ sym (hr c a b)) i
  ⊗-rec {A} {B} {C} h hl hr .charge c =
    ⊛-≡ (C .is-set)
      (λ w → ⊗-rec {A} {B} {C} h hl hr .U ((A ⊗ B) .charge c w))
      (λ w → C .charge c (⊗-rec {A} {B} {C} h hl hr .U w))
      (hl c)

  map₂ : ∀ {A₁ A₂ B₁ B₂}
    → (A₁ ⊸ A₂) → (B₁ ⊸ B₂)
    → (A₁ ⊗ B₁) ⊸ (A₂ ⊗ B₂)
  map₂ {A₁} {A₂} {B₁} {B₂} f g =
    ⊗-rec (λ a b → ∣ inj (f .U a) (g .U b) ∣₂)
      (λ c a b → cong (λ z → ∣ inj z (g .U b) ∣₂) (f .charge c a))
      (λ c a b →
          cong (λ z → ∣ inj (f .U a) z ∣₂) (g .charge c b)
        ∙ sym (cong ∣_∣₂ (law c (f .U a) (g .U b))))

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

map₂-equivᶜ : ∀ {A₁ A₂ B₁ B₂} {f : A₁ ⊸ A₂} {g : B₁ ⊸ B₂}
  → isEquivᶜ f → isEquivᶜ g
  → isEquivᶜ (map₂ f g)
map₂-equivᶜ {f = f} {g = g} fe ge =
  isoToIsEquiv
    (iso (map₂ f g .U) (map₂ (invEquivᶜ f fe) (invEquivᶜ g ge) .U)
      (⊛-≡ squash₂
        (λ z → map₂ f g .U (map₂ (invEquivᶜ f fe) (invEquivᶜ g ge) .U z)) (λ z → z)
        (λ a b i → ∣ inj (secEq (f .U , fe) a i) (secEq (g .U , ge) b i) ∣₂))
      (⊛-≡ squash₂
        (λ z → map₂ (invEquivᶜ f fe) (invEquivᶜ g ge) .U (map₂ f g .U z)) (λ z → z)
        (λ a b i → ∣ inj (retEq (f .U , fe) a i) (retEq (g .U , ge) b i) ∣₂)))

⊗-isContr : isContr (U A) → isContr (U B) → isContr (U (A ⊗ B))
⊗-isContr {A} {B} cA cB .fst = ∣ inj (cA .fst) (cB .fst) ∣₂
⊗-isContr {A} {B} cA cB .snd =
  ⊛-≡ squash₂ (λ _ → ∣ inj (cA .fst) (cB .fst) ∣₂) (λ w → w)
    (λ a b i → ∣ inj (cA .snd a i) (cB .snd b i) ∣₂)
