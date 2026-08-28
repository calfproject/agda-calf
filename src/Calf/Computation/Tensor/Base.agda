module Calf.Computation.Tensor.Base where

open import Calf.Core.Cost
open import Calf.Value
open import Calf.Computation

⊤ : 𝒞
⊤ .U = ℂ
⊤ .is-preorder = isPreorderℂ
⊤ .charge = _+ℂ_
⊤ .charge/0 = +ℂ-identityˡ _
⊤ .charge/+ = +ℂ-assoc _ _ _

⊤-rec : U A → ⊤ ⊸ A
⊤-rec {A} a .U c = A .charge c a
⊤-rec {A} a .charge c c' = A .charge/+

module _ where
  data _⊗₀_ (A B : 𝒞) : 𝒱 where
    inj : (a : U A) (b : U B) → A ⊗₀ B
    law : ∀ c a b → inj (A .charge c a) b ≡ inj a (B .charge c b)

  charge⊛ : ℂ → A ⊗₀ B → A ⊗₀ B
  charge⊛ {A} c (inj a b) = inj (A .charge c a) b
  charge⊛ {A} {B} c (law c' a b i) =
    ( cong (λ z → inj {A} {B} z b) (charge/comm A)
    ∙ law c' (A .charge c a) b ) i

  module _ {A B : 𝒞} where
    ⊗₀-elimProp
      : {P : A ⊗₀ B → 𝒱}
      → (∀ w → isProp (P w))
      → (∀ a b → P (inj a b))
      → ∀ w → P w
    ⊗₀-elimProp pP f (inj a b) = f a b
    ⊗₀-elimProp pP f (law c a b i) =
      isProp→PathP (λ i → pP (law c a b i))
        (f (A .charge c a) b)
        (f a (B .charge c b))
        i

    ⊗₀-≡
      : isPreorder Y
      → (f g : ∥ A ⊗₀ B ∥ᴾ → Y)
      → (∀ a b → f (ηᴾ (inj a b)) ≡ g (ηᴾ (inj a b)))
      → ∀ z → f z ≡ g z
    ⊗₀-≡ isPreorderY f g p =
      rec-unique isPreorderY f g
        (⊗₀-elimProp (λ _ → isPreorder→isSet isPreorderY _ _) p)

  _⊗_ : 𝒞 → 𝒞 → 𝒞
  (A ⊗ B) .U = ∥ A ⊗₀ B ∥ᴾ
  (A ⊗ B) .is-preorder = isPreorderP
  (A ⊗ B) .charge c = mapᴾ (charge⊛ c)
  (A ⊗ B) .charge/0 {x} =
    ⊗₀-≡ isPreorderP (mapᴾ (charge⊛ 0ℂ)) (λ z → z)
      (λ a b → cong (λ z → ηᴾ (inj {A} z b)) (A .charge/0 {a}))
      x
  (A ⊗ B) .charge/+ {x} {c₁} {c₂} =
    ⊗₀-≡ isPreorderP
      (mapᴾ (charge⊛ (c₁ +ℂ c₂)))
      (λ z → mapᴾ (charge⊛ c₁) (mapᴾ (charge⊛ c₂) z))
      (λ a b → cong (λ z → ηᴾ (inj {A} z b)) (A .charge/+ {a} {c₁} {c₂}))
      x

  _∥_ : U A → U B → U (A ⊗ B)
  a ∥ b = ηᴾ (inj a b)

  ∥-law : ∀ c (a : U A) (b : U B)
    → _∥_ {A} {B} (A .charge c a) b ≡ a ∥ B .charge c b
  ∥-law c a b = cong ηᴾ (law c a b)

  ⊗-rec : {A B C : 𝒞}
    → (h : U A → U B → U C)
    → (∀ c a b → h (A .charge c a) b ≡ C .charge c (h a b))
    → (∀ c a b → h a (B .charge c b) ≡ C .charge c (h a b))
    → (A ⊗ B) ⊸ C
  ⊗-rec {A} {B} {C} h hl hr .U =
    rec (C .is-preorder) λ
      { (inj a b) → h a b
      ; (law c a b i) → (hl c a b ∙ sym (hr c a b)) i
      }
  ⊗-rec {A} {B} {C} h hl hr .charge c =
    ⊗₀-≡ (C .is-preorder)
      (λ w → ⊗-rec {A} {B} {C} h hl hr .U ((A ⊗ B) .charge c w))
      (λ w → C .charge c (⊗-rec {A} {B} {C} h hl hr .U w))
      (hl c)

  map₂ : ∀ {A₁ A₂ B₁ B₂}
    → (A₁ ⊸ A₂) → (B₁ ⊸ B₂)
    → (A₁ ⊗ B₁) ⊸ (A₂ ⊗ B₂)
  map₂ {A₁} {A₂} {B₁} {B₂} f g =
    ⊗-rec (λ a b → ηᴾ (inj (f .U a) (g .U b)))
      (λ c a b → cong (λ z → ηᴾ (inj z (g .U b))) (f .charge c a))
      (λ c a b →
          cong (λ z → ηᴾ (inj (f .U a) z)) (g .charge c b)
        ∙ sym (cong ηᴾ (law c (f .U a) (g .U b))))

⊗-identityʳ : A ⊗ ⊤ ≡ A
⊗-identityʳ {A = A} = conservativity fwd fwd-equiv
  where
    fwd : A ⊗ ⊤ ⊸ A
    fwd = ⊗-rec (λ a c → A .charge c a) (λ _ _ _ → charge/comm A) (λ _ _ _ → A .charge/+)

    fwd-equiv : isEquivᶜ fwd
    fwd-equiv = isoToIsEquiv (iso (fwd .U) inv sect retr)
      where
        inv : U A → U (A ⊗ ⊤)
        inv a = ηᴾ (inj a 0ℂ)

        sect : ∀ a → fwd .U (inv a) ≡ a
        sect a = A .charge/0

        retr : ∀ z → inv (fwd .U z) ≡ z
        retr =
          ⊗₀-≡ isPreorderP (λ z → inv (fwd .U z)) (λ z → z)
            (λ a c →
                cong ηᴾ (law c a 0ℂ)
              ∙ cong (λ d → ηᴾ (inj a d)) (+ℂ-identityʳ c))

opaque
  map₂-equivᶜ : ∀ {A₁ A₂ B₁ B₂} {f : A₁ ⊸ A₂} {g : B₁ ⊸ B₂}
    → isEquivᶜ f → isEquivᶜ g
    → isEquivᶜ (map₂ f g)
  map₂-equivᶜ {f = f} {g = g} fe ge =
    isoToIsEquiv
      (iso (map₂ f g .U) (map₂ (invEquivᶜ f fe) (invEquivᶜ g ge) .U)
        (⊗₀-≡ isPreorderP
          (λ z → map₂ f g .U (map₂ (invEquivᶜ f fe) (invEquivᶜ g ge) .U z)) (λ z → z)
          (λ a b i → ηᴾ (inj (secEq (f .U , fe) a i) (secEq (g .U , ge) b i))))
        (⊗₀-≡ isPreorderP
          (λ z → map₂ (invEquivᶜ f fe) (invEquivᶜ g ge) .U (map₂ f g .U z)) (λ z → z)
          (λ a b i → ηᴾ (inj (retEq (f .U , fe) a i) (retEq (g .U , ge) b i)))))

⊗-isContr : isContr (U A) → isContr (U B) → isContr (U (A ⊗ B))
⊗-isContr {A} {B} cA cB .fst = ηᴾ (inj (cA .fst) (cB .fst))
⊗-isContr {A} {B} cA cB .snd =
  ⊗₀-≡ isPreorderP (λ _ → ηᴾ (inj (cA .fst) (cB .fst))) (λ w → w)
    (λ a b i → ηᴾ (inj (cA .snd a i) (cB .snd b i)))
