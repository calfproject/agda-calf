open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism using (Iso; iso; isoToIsEquiv)
open import Cubical.HITs.SetTruncation

module Calf.Computation.Tensor where

open import Calf.Value
open import Calf.Value.Product
open import Calf.Computation
open import Calf.Core.Cost

∥∥₂-≡
  : {V C : Type} → isSet C
  → (f g : ∥ V ∥₂ → C)
  → (∀ v → f ∣ v ∣₂ ≡ g ∣ v ∣₂)
  → ∀ z → f z ≡ g z
∥∥₂-≡ Cset f g p = elim (λ z → isProp→isSet (Cset (f z) (g z))) p

data _⊛_ (A B : 𝒞) : Type where
  inj : (a : U A) (b : U B) → A ⊛ B
  law : ∀ c a b → inj (A .charge c a) b ≡ inj a (B .charge c b)

module _ {A B : 𝒞} where
  ⊛-elimProp
    : {P : A ⊛ B → Type}
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
    : {C : Type} → isSet C
    → (f g : ∥ A ⊛ B ∥₂ → C)
    → (∀ a b → f ∣ inj a b ∣₂ ≡ g ∣ inj a b ∣₂)
    → ∀ z → f z ≡ g z
  ⊛-≡ Cset f g p = ∥∥₂-≡ Cset f g (⊛-elimProp (λ _ → Cset _ _) p)

  -- charge acts on the left factor; the `law` case uses commutativity of charge
  charge⊛ : ℂ → A ⊛ B → A ⊛ B
  charge⊛ c (inj a b) = inj (A .charge c a) b
  charge⊛ c (law c' a b i) =
    ( cong (λ z → inj {A} {B} z b) (charge/comm A)
    ∙ law c' (A .charge c a) b ) i

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

module _ where
  open import Calf.Computation.Free

  opaque
    unfolding F

    F-monoidal : (F X ⊗ F Y) ≡ F (X × Y)
    F-monoidal {X} {Y} = conservativity f f-equiv
      where
        prod₂ : ∥ X ∥₂ → ∥ Y ∥₂ → ∥ X × Y ∥₂
        prod₂ = rec2 squash₂ (λ x y → ∣ x , y ∣₂)

        h : (F X) ⊛ (F Y) → U (F (X × Y))
        h (inj (c₁ , x) (c₂ , y)) = (c₁ +ℂ c₂) , prod₂ x y
        h (law c (c₁ , x) (c₂ , y) i) =
          cong (_, prod₂ x y)
            ( cong (_+ℂ c₂) (+ℂ-comm c c₁) ∙ +ℂ-assoc c₁ c c₂ ) i

        f : (F X ⊗ F Y) ⊸ F (X × Y)
        f .U = rec (F (X × Y) .is-set) h
        f .charge c =
          ⊛-≡ (F (X × Y) .is-set)
            (λ z → f .U ((F X ⊗ F Y) .charge c z))
            (λ z → F (X × Y) .charge c (f .U z))
            (λ (c₁ , x) (c₂ , y) → cong (_, prod₂ x y) (+ℂ-assoc c c₁ c₂))

        g : U (F (X × Y)) → U (F X ⊗ F Y)
        g (c , w) =
          rec squash₂ (λ (x , y) → ∣ inj (c , ∣ x ∣₂) (0ℂ , ∣ y ∣₂) ∣₂) w

        f-equiv : isEquivᶜ f
        f-equiv = isoToIsEquiv (iso (f .U) g sect retr)
          where
            sect : ∀ m → f .U (g m) ≡ m
            sect (c , w) =
              ∥∥₂-≡ (F (X × Y) .is-set)
                (λ w → f .U (g (c , w)))
                (λ w → c , w)
                (λ (x , y) → cong (_, ∣ x , y ∣₂) (+ℂ-identityʳ c))
                w

            retr : ∀ z → g (f .U z) ≡ z
            retr =
              ⊛-≡ squash₂ (λ z → g (f .U z)) (λ z → z)
                (λ (c₁ , x) (c₂ , y) →
                  elim2
                    {C = λ x y →
                      g (f .U ∣ inj (c₁ , x) (c₂ , y) ∣₂) ≡ ∣ inj (c₁ , x) (c₂ , y) ∣₂}
                    (λ _ _ → isProp→isSet (squash₂ _ _))
                    (λ x y →
                        cong (λ d → ∣ inj (d , ∣ x ∣₂) (0ℂ , ∣ y ∣₂) ∣₂) (+ℂ-comm c₁ c₂)
                      ∙ cong ∣_∣₂ (law c₂ (c₁ , ∣ x ∣₂) (0ℂ , ∣ y ∣₂))
                      ∙ cong (λ d → ∣ inj (c₁ , ∣ x ∣₂) (d , ∣ y ∣₂) ∣₂) (+ℂ-identityʳ c₂))
                    x y)

  par : U (F X) → U (F Y) → U (F (X × Y))
  par ex ey = transport (cong U F-monoidal) (ex ∥ ey)


⊤ : 𝒞
⊤ .U = ℂ
⊤ .is-set = isSetℂ
⊤ .charge = _+ℂ_
⊤ .charge/0 = +ℂ-identityˡ _
⊤ .charge/+ = +ℂ-assoc _ _ _

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

module _ where
  open import Calf.Computation.Closed using (●ᶜ; ●ᶜ-charge-map)
  import Calf.Value.Closed as ●

  combine● : ●.● (U A) → ●.● (U B) → ●.● ∥ A ⊛ B ∥₂
  combine● {A} {B} a• b• = ●.bind a• (λ a → ●.map (λ b → ∣ inj {A} {B} a b ∣₂) b•)

  ●ᶜ-⊗ : ●ᶜ (A ⊗ B) ≡ (●ᶜ A ⊗ ●ᶜ B)
  ●ᶜ-⊗ {A} {B} = conservativity Φ Φ-equiv
    where
      ε⊛ : A ⊛ B → ●ᶜ A ⊛ ●ᶜ B
      ε⊛ (inj a b) = inj (●.η• a) (●.η• b)
      ε⊛ (law c a b i) = law c (●.η• a) (●.η• b) i

      ε : ∥ A ⊛ B ∥₂ → ∥ ●ᶜ A ⊛ ●ᶜ B ∥₂
      ε = map ε⊛

      Φ-U : U (●ᶜ (A ⊗ B)) → U (●ᶜ A ⊗ ●ᶜ B)
      Φ-U =
        ●.ind (λ _ → ∥ ●ᶜ A ⊛ ●ᶜ B ∥₂)
          ε
          (λ abs → ∣ inj (●.∗ abs) (●.∗ abs) ∣₂)
          (λ w abs →
            ⊛-≡ squash₂ ε (λ _ → ∣ inj (●.∗ abs) (●.∗ abs) ∣₂)
              (λ a b →
                  cong (λ z → ∣ inj {●ᶜ A} {●ᶜ B} z (●.η• b) ∣₂) (●.law a abs)
                ∙ cong (λ z → ∣ inj {●ᶜ A} {●ᶜ B} (●.∗ abs) z ∣₂) (●.law b abs))
              w)

      Φ : ●ᶜ (A ⊗ B) ⊸ (●ᶜ A ⊗ ●ᶜ B)
      Φ .U = Φ-U
      Φ .charge c =
        ●.ind (λ a• → Φ-U (●ᶜ (A ⊗ B) .charge c a•) ≡ (●ᶜ A ⊗ ●ᶜ B) .charge c (Φ-U a•))
          (λ w →
            ⊛-≡ squash₂
              (λ w → ε (map (charge⊛ c) w))
              (λ w → map (charge⊛ c) (ε w))
              (λ a b → refl)
              w)
          (λ abs → refl)
          (λ w abs →
            isProp→PathP (λ _ → squash₂ _ _)
              (⊛-≡ squash₂ (λ w → ε (map (charge⊛ c) w)) (λ w → map (charge⊛ c) (ε w)) (λ a b → refl) w)
              refl)

      comb : ●.● (U A) → ●.● (U B) → ●.● ∥ A ⊛ B ∥₂
      comb = combine●

      comb-law : ∀ c a• b•
        → comb (●ᶜ A .charge c a•) b• ≡ comb a• (●ᶜ B .charge c b•)
      comb-law c a• b• =
        ●.ind (λ a• → comb (●ᶜ A .charge c a•) b• ≡ comb a• (●ᶜ B .charge c b•))
          (λ a →
              cong (λ f → ●.map f b•) (funExt λ b → cong ∣_∣₂ (law c a b))
            ∙ sym (●.map-∘ (B .charge c) (λ b → ∣ inj a b ∣₂) b•)
            ∙ cong (●.map (λ b → ∣ inj a b ∣₂)) (sym (●ᶜ-charge-map c b•)))
          (λ abs → refl)
          (λ a abs → isProp→PathP (λ _ → ●.●-preserves-isSet squash₂ _ _) _ refl)
          a•

      Ψ⊛ : ●ᶜ A ⊛ ●ᶜ B → ●.● ∥ A ⊛ B ∥₂
      Ψ⊛ (inj a• b•) = comb a• b•
      Ψ⊛ (law c a• b• i) = comb-law c a• b• i

      Ψ : U (●ᶜ A ⊗ ●ᶜ B) → U (●ᶜ (A ⊗ B))
      Ψ = rec (●.●-preserves-isSet squash₂) Ψ⊛

      sect-pt : ∀ a• b• → Φ-U (comb a• b•) ≡ ∣ inj a• b• ∣₂
      sect-pt a• b• =
        ●.ind (λ a• → Φ-U (comb a• b•) ≡ ∣ inj a• b• ∣₂)
          (λ a →
            ●.ind (λ b• → Φ-U (comb (●.η• a) b•) ≡ ∣ inj (●.η• a) b• ∣₂)
              (λ b → refl)
              (λ abs → cong (λ z → ∣ inj {●ᶜ A} {●ᶜ B} z (●.∗ abs) ∣₂) (sym (●.law a abs)))
              (λ b abs → isProp→PathP (λ _ → squash₂ _ _) _ _)
              b•)
          (λ abs → cong (λ z → ∣ inj (●.∗ abs) z ∣₂) (sym (●.●-path-to-star abs b•)))
          (λ a abs → isProp→PathP (λ _ → squash₂ _ _) _ _)
          a•

      Φ-equiv : isEquivᶜ Φ
      Φ-equiv = isoToIsEquiv (iso Φ-U Ψ sect retr)
        where
          sect : ∀ y → Φ-U (Ψ y) ≡ y
          sect = ⊛-≡ squash₂ (λ y → Φ-U (Ψ y)) (λ y → y) (λ a• b• → sect-pt a• b•)

          retr : ∀ x → Ψ (Φ-U x) ≡ x
          retr =
            ●.ind (λ x → Ψ (Φ-U x) ≡ x)
              (⊛-≡ (●.●-preserves-isSet squash₂) (λ w → Ψ (ε w)) ●.η• (λ a b → refl))
              (λ abs → refl)
              (λ w abs → isProp→PathP (λ _ → ●.●-preserves-isSet squash₂ _ _) _ refl)

module _ where
  open import Calf.Computation.Open as ◯ᶜ
  open import Calf.Computation.Closed as ●ᶜ
  open import Calf.Computation.Glue
  open import Calf.Computation.Abstraction
  open import Calf.Computation.Credit

  opaque
    unfolding Abstractionᶜ

    Abstractionᶜ-⊗ : ∀ {A-⊤ A-abs α B-⊤ B-abs β} →
      Abstractionᶜ A-⊤ A-abs α ⊗ Abstractionᶜ B-⊤ B-abs β ≡
      Abstractionᶜ (A-⊤ ⊗ B-⊤) (A-abs ⊗ B-abs) (map₂ α β)
    Abstractionᶜ-⊗ = {!   !}

  A⊗▷B≡▷[A⊗B] : ∀ c → (A ⊗ (▷[ c ] B)) ≡ (▷[ c ] (A ⊗ B))
  A⊗▷B≡▷[A⊗B] {A} {B} c =
      (A ⊗ (▷[ c ] B))
    ≡⟨ cong (_⊗ (▷[ c ] B)) (sym Abstractionᶜ-id) ⟩
      (Abstractionᶜ A A idᶜ ⊗ (▷[ c ] B))
    ≡⟨ Abstractionᶜ-⊗ {A} {A} {idᶜ} {B} {B} {CHARGE c} ⟩
      Abstractionᶜ (A ⊗ B) (A ⊗ B) (map₂ idᶜ (CHARGE c))
    ≡⟨
      cong (Abstractionᶜ _ _)
        (⊸-path refl refl
            (funExt
              (⊛-≡ squash₂
                (map₂ idᶜ (CHARGE c) .U)
                (CHARGE {A ⊗ B} c .U)
                (λ a b → sym (cong ∣_∣₂ (law c a b))))))
    ⟩
      Abstractionᶜ (A ⊗ B) (A ⊗ B) (CHARGE c)
    ≡⟨ refl ⟩
      (▷[ c ] (A ⊗ B))
    ∎
