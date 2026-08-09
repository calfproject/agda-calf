module Calf.Computation.Tensor.Free where

open import Calf.Core.Cost
open import Calf.Value
open import Calf.Value.Product
open import Calf.Computation
open import Calf.Computation.Free

open import Cubical.HITs.SetTruncation
open import Cubical.Foundations.Univalence using (ua→; ua-gluePath)

open import Calf.Computation.Tensor.Base

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

module _ where
  open import Calf.Computation.Copower

  opaque
    unfolding F

    Σᶜ-F-fwd : ∀ {X} → ([ x ∈ X ] ⋊ ⊤) ⊸ F ⟨ X ⟩
    Σᶜ-F-fwd .U (x , c) = c , ∣ x ∣₂
    Σᶜ-F-fwd .charge _ _ = refl

    F-Σᶜ-fwd : ∀ {X} → F ⟨ X ⟩ ⊸ ([ x ∈ X ] ⋊ ⊤)
    F-Σᶜ-fwd {X} .U (c , x) =
      rec (Σᶜ X (const ⊤) .is-set) (λ x → x , c) x
    F-Σᶜ-fwd {X} .charge c (c' , x) =
      elim
        (λ x → isProp→isSet
          (Σᶜ X (const ⊤) .is-set
            (F-Σᶜ-fwd .U (c +ℂ c' , x))
            (Σᶜ X (const ⊤) .charge c (F-Σᶜ-fwd .U (c' , x)))))
        (λ _ → refl)
        x

    F-Σᶜ-fwd-equiv : ∀ {X} → isEquivᶜ (F-Σᶜ-fwd {X})
    F-Σᶜ-fwd-equiv {X} =
      isoToIsEquiv (iso (F-Σᶜ-fwd .U) (Σᶜ-F-fwd .U) sec retr)
      where
        sec : ∀ e → F-Σᶜ-fwd .U (Σᶜ-F-fwd .U e) ≡ e
        sec _ = refl

        retr : ∀ e → Σᶜ-F-fwd .U (F-Σᶜ-fwd .U e) ≡ e
        retr (c , x) = ∥∥₂-≡ (F ⟨ X ⟩ .is-set)
          (λ x → Σᶜ-F-fwd .U (F-Σᶜ-fwd .U (c , x)))
          (c ,_) (λ _ → refl) x

    F-Σᶜ : ∀ {X} → F ⟨ X ⟩ ≡ ([ x ∈ X ] ⋊ ⊤)
    F-Σᶜ = conservativity F-Σᶜ-fwd F-Σᶜ-fwd-equiv

    F-Σᶜ-potential : ∀ {X} (Φ : ⟨ X ⟩ → ℂ) 
      → PathP (λ i → F-Σᶜ {X} i ⊸ F-Σᶜ {X} i)
          (bind' λ x → F _ .charge (Φ x) (ret x))
          (Σᶜ-map {X} {const ⊤} (λ x → CHARGE (Φ x)))
    F-Σᶜ-potential {X} Φ =
      ⊸-path F-Σᶜ F-Σᶜ
        (ua→
          {e = F-Σᶜ-fwd .U , F-Σᶜ-fwd-equiv}
          (λ e → ua-gluePath _ (naturality e)))
      where
        naturality : (e : U (F ⟨ X ⟩)) →
          F-Σᶜ-fwd .U (bind' (λ x → F _ .charge (Φ x) (ret x)) .U e)
          ≡ Σᶜ-map {X} {const ⊤} (λ x → CHARGE (Φ x)) .U (F-Σᶜ-fwd .U e)
        naturality (c , x) =
          ∥∥₂-≡ (Σᶜ X (const ⊤) .is-set)
            (λ x →
              F-Σᶜ-fwd .U
                (bind' (λ x → F _ .charge (Φ x) (ret x)) .U (c , x)))
            (λ x →
              Σᶜ-map {X} {const ⊤} (λ x → CHARGE (Φ x)) .U
                (F-Σᶜ-fwd .U (c , x)))
            (λ x → cong (x ,_) (+ℂ-comm c (Φ x)))
            x
