module Calf.Computation.Tensor.Base where

open import Calf.Core.Cost
open import Calf.Value
open import Calf.Value.Nat
open import Calf.Value.Product
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
  ⊗ᵏ : (X → 𝒞) → (X → X) → X → ℕ → 𝒞
  ⊗ᵏ Af xf x₀ zero = ⊤
  ⊗ᵏ Af xf x₀ (suc k) = Af x₀ ⊗ (⊗ᵏ Af xf (xf x₀) k)

  Vecᶜ : 𝒞 → ℕ → 𝒞
  Vecᶜ A = ⊗ᵏ (λ _ → A) (λ _ → tt) tt

opaque
  unfolding _⊗_

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


  ⊗-comm-fun : A ⊗ B ⊸ B ⊗ A
  ⊗-comm-fun {A} {B} = fwd
    where
      flip-⊛ : ∀ {C D : 𝒞} → (C ⊛ D) → (D ⊛ C)
      flip-⊛ (inj c d) = inj d c
      flip-⊛ (law c₀ c d i) = sym (law c₀ d c) i

      fwd : A ⊗ B ⊸ B ⊗ A
      fwd .U = map (flip-⊛ {C = A} {D = B})
      fwd .charge c =
        ⊛-≡ squash₂
          (λ z → fwd .U ((A ⊗ B) .charge c z))
          (λ z → (B ⊗ A) .charge c (fwd .U z))
          (λ a b → cong ∣_∣₂ (sym (law c b a)))

  ⊗-comm : A ⊗ B ≡ B ⊗ A
  ⊗-comm {A} {B} = conservativity fwd fwd-equiv
    where
      fwd : A ⊗ B ⊸ B ⊗ A
      fwd = ⊗-comm-fun {A} {B}

      fwd-equiv : isEquivᶜ fwd
      fwd-equiv = isoToIsEquiv (iso (fwd .U) inv sect retr)
        where
          inv : U (B ⊗ A) → U (A ⊗ B)
          inv = ⊗-comm-fun {B} {A} .U

          sect : ∀ a → fwd .U (inv a) ≡ a
          sect = ⊛-≡ squash₂ (λ z → fwd .U (inv z)) (λ z → z) (λ b a → refl)

          retr : ∀ z → inv (fwd .U z) ≡ z
          retr = ⊛-≡ squash₂ (λ z → inv (fwd .U z)) (λ z → z) (λ a b → refl)

  ⊗-identityˡ : ⊤ ⊗ A ≡ A
  ⊗-identityˡ = ⊗-comm ∙ ⊗-identityʳ

  ⊗-assoc-fwd : A ⊗ (B ⊗ C) ⊸ (A ⊗ B) ⊗ C
  ⊗-assoc-fwd {A} {B} {C} = fwd
    where
      inner : U A → B ⊛ C → (A ⊗ B) ⊛ C
      inner a (inj b c) = inj ∣ inj a b ∣₂ c
      inner a (law d b c i) = law-≡ i
        where
          law-≡ : inj {A = A ⊗ B} {B = C} ∣ inj a (B .charge d b) ∣₂ c ≡ inj ∣ inj a b ∣₂ (C .charge d c)
          law-≡ =
              inj ∣ inj a (B .charge d b) ∣₂ c
            ≡⟨ cong (λ z → inj {A = A ⊗ B} {B = C} ∣ z ∣₂ c) (sym (law d a b)) ⟩
              inj ∣ inj (A .charge d a) b ∣₂ c
            ≡⟨ law d ∣ inj a b ∣₂ c ⟩
              inj ∣ inj a b ∣₂ (C .charge d c)
            ∎

      fwd-U : A ⊛ (B ⊗ C) → U ((A ⊗ B) ⊗ C)
      fwd-U (inj a bc) = map (inner a) bc
      fwd-U (law d a bc i) =
        ⊛-≡ squash₂
        (map (inner (A .charge d a)))
        (λ z → map (inner a) (map (charge⊛ d) z))
        (λ b c → cong (λ z → ∣ inj {A = A ⊗ B} {B = C} ∣ z ∣₂ c ∣₂) (law d a b))
        bc i

      fwd : A ⊗ (B ⊗ C) ⊸ (A ⊗ B) ⊗ C
      fwd .U = rec squash₂ fwd-U
      fwd .charge d =
        ⊛-≡ squash₂
        (λ z → fwd .U ((A ⊗ (B ⊗ C)) .charge d z))
        (λ z → ((A ⊗ B) ⊗ C) .charge d (fwd .U z))
        (λ a →
          ⊛-≡ squash₂
          (map (inner (A .charge d a)))
          (λ z → map (charge⊛ d) (map (inner a) z))
          (λ b c → refl)
        )

  ⊗-assoc-bwd : (A ⊗ B) ⊗ C ⊸ A ⊗ (B ⊗ C)
  ⊗-assoc-bwd {A} {B} {C} =
    ⊗-comm-fun ⨾ᶜ
    map₂ idᶜ ⊗-comm-fun ⨾ᶜ
    ⊗-assoc-fwd {C} {B} {A} ⨾ᶜ
    map₂ ⊗-comm-fun idᶜ ⨾ᶜ
    ⊗-comm-fun

  ⊗-assoc : A ⊗ (B ⊗ C) ≡ (A ⊗ B) ⊗ C
  ⊗-assoc {A} {B} {C} = conservativity fwd fwd-equiv
    where
      fwd : A ⊗ (B ⊗ C) ⊸ (A ⊗ B) ⊗ C
      fwd = ⊗-assoc-fwd {A} {B} {C}

      fwd-equiv : isEquivᶜ fwd
      fwd-equiv = isoToIsEquiv (iso (fwd .U) inv sect retr)
        where
          inv : U ((A ⊗ B) ⊗ C) → U (A ⊗ (B ⊗ C))
          inv = ⊗-assoc-bwd {A} {B} {C} .U

          sect : ∀ a → fwd .U (inv a) ≡ a
          sect =
            ⊛-≡ squash₂ (λ z → fwd .U (inv z)) (λ z → z)
            (flip $ λ c →
              ⊛-≡ squash₂ (λ z → fwd .U (inv ∣ inj z c ∣₂)) (λ z → ∣ inj z c ∣₂)
              (λ a b → refl)
            )

          retr : ∀ z → inv (fwd .U z) ≡ z
          retr =
            ⊛-≡ squash₂ (λ z → inv (fwd .U z)) (λ z → z)
            (λ a →
              ⊛-≡ squash₂ (λ z → inv (fwd .U ∣ inj a z ∣₂)) (λ z → ∣ inj a z ∣₂)
              (λ b c → refl)
            )

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

opaque
  unfolding _⊗_

  ⊗-isContr : isContr (U A) → isContr (U B) → isContr (U (A ⊗ B))
  ⊗-isContr {A} {B} cA cB .fst = ∣ inj (cA .fst) (cB .fst) ∣₂
  ⊗-isContr {A} {B} cA cB .snd =
    ⊛-≡ squash₂ (λ _ → ∣ inj (cA .fst) (cB .fst) ∣₂) (λ w → w)
      (λ a b i → ∣ inj (cA .snd a i) (cB .snd b i) ∣₂)
