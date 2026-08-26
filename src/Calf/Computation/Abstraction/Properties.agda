module Calf.Computation.Abstraction.Properties where

open import Cubical.Foundations.Univalence using (ua; ua→; ua-gluePath)
open import Cubical.Foundations.Equiv using (composesToId→Equiv)

open import Calf.Core.Abstract
open import Calf.Core.Cost using (ℂ)
open import Calf.Value
import Calf.Value.Open as ◯
import Calf.Value.Closed as ●
open import Calf.Computation
open import Calf.Computation.Open as ◯ᶜ
open import Calf.Computation.Closed as ●ᶜ
open import Calf.Computation.Glue as Glueᶜ hiding (squareᶜ)
open 𝒞-FRACTURE

open import Calf.Computation.Abstraction.Base

opaque
  unfolding Abstractionᶜ

  ●ᶜ-Abstractionᶜ : ∀ {A-⊤ A-abs} (α : A-⊤ ⊸ A-abs) → ●ᶜ (Abstractionᶜ A-⊤ A-abs α) ≡ ●ᶜ A-⊤
  ●ᶜ-Abstractionᶜ {A-⊤} {A-abs} α =
    cong ⟨_⟩ᶜ (𝒞-glue•-path (Abstractionᶜ-FRAC A-⊤ A-abs α))

  ◯ᶜ-Abstractionᶜ : ∀ {A-⊤ A-abs} (α : A-⊤ ⊸ A-abs) → ◯ᶜ (Abstractionᶜ A-⊤ A-abs α) ≡ ◯ᶜ A-abs
  ◯ᶜ-Abstractionᶜ {A-⊤} {A-abs} α =
    cong ⟨_⟩ᶜ (𝒞-glue◦-path (Abstractionᶜ-FRAC A-⊤ A-abs α))

opaque
  unfolding Abstractionᶜ triangle-Uᶜ

  ●ᶜ-triangle-Uᶜ-equiv : ∀ {A-⊤ A-abs} (α : A-⊤ ⊸ A-abs)
    → isEquiv (●ᶜ.map (triangle-Uᶜ α) .U)
  ●ᶜ-triangle-Uᶜ-equiv {A-⊤} {A-abs} α =
    composesToId→Equiv (equivFun ge) (●ᶜ.map (triangle-Uᶜ α) .U) (funExt proj-unit) (ge .snd)
    where
      ge : U (●ᶜ (Abstractionᶜ A-⊤ A-abs α)) ≃ U (●ᶜ A-⊤)
      ge = glue•-equiv (U-FRACTURE (Abstractionᶜ-FRAC A-⊤ A-abs α))

      proj-unit : ∀ w → equivFun ge (●ᶜ.map (triangle-Uᶜ α) .U w) ≡ w
      proj-unit = ●.elim (λ _ → ●.●-≡-isModal _ _) (λ _ → refl)

●ᶜ-Abstractionᶜ-≃ᶜ : ∀ {A-⊤ A-abs} (α : A-⊤ ⊸ A-abs) → ●ᶜ A-⊤ ≃ᶜ ●ᶜ (Abstractionᶜ A-⊤ A-abs α)
●ᶜ-Abstractionᶜ-≃ᶜ α = ●ᶜ.map (triangle-Uᶜ α) , ●ᶜ-triangle-Uᶜ-equiv α

opaque
  unfolding Abstractionᶜ squareᶜ' triangle-Uᶜ

  triangle-Uᶜ-natural : ∀ {A-⊤ A-abs α B-⊤ B-abs β}
    (f-⊤ : A-⊤ ⊸ B-⊤) (f-abs : A-abs ⊸ B-abs)
    (coh : (a : U A-⊤) → β .U (f-⊤ .U a) ≡ f-abs .U (α .U a))
    → triangle-Uᶜ α ⨾ᶜ squareᶜ' α β f-⊤ f-abs coh
      ≡ f-⊤ ⨾ᶜ triangle-Uᶜ β
  triangle-Uᶜ-natural {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} f-⊤ f-abs coh =
    ⊸-path refl refl
      (funExt λ a →
        Glue-path (is-set (◯ᶜ B-abs))
          refl
          (funExt λ _ → sym (coh a)))

opaque
  unfolding Abstractionᶜ ●ᶜ-Abstractionᶜ

  Abstractionᶜ-coherence : ∀ {A-⊤ A-abs} (α : A-⊤ ⊸ A-abs) →
    PathP
      (λ i →
        sym (●ᶜ-Abstractionᶜ α) i ⊸
        ●ᶜ (sym (◯ᶜ-Abstractionᶜ α) i))
      (●ᶜ.map (α ⨾ᶜ η◦ᶜ {A = A-abs}))
      (●ᶜ.map (η◦ᶜ {A = Abstractionᶜ A-⊤ A-abs α}))
  Abstractionᶜ-coherence {A-⊤} {A-abs} α =
    𝒞-glue-fracture-section-α•
      (Abstractionᶜ-FRAC A-⊤ A-abs α)

opaque
  unfolding Abstractionᶜ

  ◯[Abstractionᶜ≃A-abs]
    : ∀ {A-⊤ A-abs} (α : A-⊤ ⊸ A-abs)
    → ⟨ ABS ⟩
    → Abstractionᶜ A-⊤ A-abs α ≃ᶜ A-abs
  ◯[Abstractionᶜ≃A-abs] {A-⊤} {A-abs} α abs =
    ◯[Glueᶜ≃A◦] (Abstractionᶜ-FRAC A-⊤ A-abs α) abs ∙ₑᶜ ABS-◯ᶜA≃A abs

opaque
  unfolding Abstractionᶜ squareᶜ' triangleᶜ' ◯[Abstractionᶜ≃A-abs]

  ◯[Abstractionᶜ≡A-abs]
    : ∀ {A-⊤ A-abs} (α : A-⊤ ⊸ A-abs)
    → ⟨ ABS ⟩
    → Abstractionᶜ A-⊤ A-abs α ≡ A-abs
  ◯[Abstractionᶜ≡A-abs] α abs = uaᶜ (◯[Abstractionᶜ≃A-abs] α abs)

  ◯[squareᶜ'≡f-abs]
    : ∀ {A-⊤ A-abs B-⊤ B-abs}
    → (α : A-⊤ ⊸ A-abs) (β : B-⊤ ⊸ B-abs)
    → (f-⊤ : A-⊤ ⊸ B-⊤) (f-abs : A-abs ⊸ B-abs)
    → (f-coh : (a-⊤ : U A-⊤) → U β (U f-⊤ a-⊤) ≡ U f-abs (U α a-⊤))
    → (abs : ⟨ ABS ⟩)
    → PathP
      (λ i →
        ◯[Abstractionᶜ≡A-abs] α abs i
          ⊸ ◯[Abstractionᶜ≡A-abs] β abs i)
      (squareᶜ' α β f-⊤ f-abs f-coh)
      f-abs
  ◯[squareᶜ'≡f-abs] α β f-⊤ f-abs f-coh abs =
    ⊸-path
      (◯[Abstractionᶜ≡A-abs] α abs)
      (◯[Abstractionᶜ≡A-abs] β abs)
      (ua→
        {e = ◯[Abstractionᶜ≃A-abs] α abs .fst .U
           , ◯[Abstractionᶜ≃A-abs] α abs .snd}
        {B = λ i → U (◯[Abstractionᶜ≡A-abs] β abs i)}
        (λ _ →
          ua-gluePath
            ( ◯[Abstractionᶜ≃A-abs] β abs .fst .U
            , ◯[Abstractionᶜ≃A-abs] β abs .snd)
            refl))

  ◯[triangleᶜ'≡b-abs] : ∀ {B-⊤ B-abs} (β : B-⊤ ⊸ B-abs)
      (b-⊤ : U B-⊤) (b-abs : U B-abs) (b-coh : β .U b-⊤ ≡ b-abs) (abs : ⟨ ABS ⟩) →
    PathP (λ i → U (◯[Abstractionᶜ≡A-abs] β abs i))
      (triangleᶜ' β b-⊤ b-abs b-coh)
      b-abs
  ◯[triangleᶜ'≡b-abs] β b-⊤ b-abs b-coh abs =
    ua-gluePath
      ( ◯[Abstractionᶜ≃A-abs] β abs .fst .U
      , ◯[Abstractionᶜ≃A-abs] β abs .snd)
      refl


opaque
  unfolding Abstractionᶜ squareᶜ'

  squareᶜ'-charge
    : ∀ {A-⊤ A-abs} (α : A-⊤ ⊸ A-abs) (c : ℂ)
    → (α-charge : (a : U A-⊤) → α .U (A-⊤ .charge c a) ≡ A-abs .charge c (α .U a))
    → squareᶜ' α α
        (CHARGE {A-⊤} c) (CHARGE {A-abs} c)
        α-charge
      ≡ CHARGE {Abstractionᶜ A-⊤ A-abs α} c
  squareᶜ'-charge {A-⊤} {A-abs} α c α-charge =
    ⊸-path
      refl
      refl
      (funExt λ _ → Glue-path (is-set (◯ᶜ A-abs)) refl refl)

  squareᶜ'-⨾ᶜ : ∀ {A-⊤ A-abs α B-⊤ B-abs β C-⊤ C-abs γ}
    (f-⊤ : A-⊤ ⊸ B-⊤) (f-abs : A-abs ⊸ B-abs)
    (fc : (a : U A-⊤) → β .U (f-⊤ .U a) ≡ f-abs .U (α .U a))
    (g-⊤ : B-⊤ ⊸ C-⊤) (g-abs : B-abs ⊸ C-abs)
    (gc : (b : U B-⊤) → γ .U (g-⊤ .U b) ≡ g-abs .U (β .U b))
    → squareᶜ' α β f-⊤ f-abs fc ⨾ᶜ squareᶜ' β γ g-⊤ g-abs gc
      ≡ squareᶜ' α γ (f-⊤ ⨾ᶜ g-⊤) (f-abs ⨾ᶜ g-abs)
          (λ a → gc (f-⊤ .U a) ∙ cong (g-abs .U) (fc a))
  squareᶜ'-⨾ᶜ {C-⊤ = C-⊤} {C-abs} {γ} f-⊤ f-abs fc g-⊤ g-abs gc =
    ⊸-path refl refl $ funExt λ a →
      Glue-path (is-set (◯ᶜ C-abs))
        (●.map-∘ (f-⊤ .U) (g-⊤ .U) (• a))
        (◯.map-∘ (f-abs .U) (g-abs .U) (◦ a))

  squareᶜ'-≡ : ∀ {A-⊤ A-abs α B-⊤ B-abs β}
    {f-⊤ f-⊤' : A-⊤ ⊸ B-⊤} {f-abs f-abs' : A-abs ⊸ B-abs}
    {fc : (a : U A-⊤) → β .U (f-⊤ .U a) ≡ f-abs .U (α .U a)}
    {fc' : (a : U A-⊤) → β .U (f-⊤' .U a) ≡ f-abs' .U (α .U a)}
    → f-⊤ ≡ f-⊤' → f-abs ≡ f-abs'
    → squareᶜ' α β f-⊤ f-abs fc ≡ squareᶜ' α β f-⊤' f-abs' fc'
  squareᶜ'-≡ {B-⊤ = B-⊤} {B-abs} {β} {fc = fc} {fc' = fc'} p q =
    ⊸-path refl refl $ funExt λ a →
      Glue-path (is-set (◯ᶜ B-abs))
        (cong (λ f → ●.map (f .U) (• a)) p)
        (cong (λ f → ◯.map (f .U) (◦ a)) q)

  Abstractionᶜ-Abstractionᶜ : ∀ {A-⊤ A-abs B-⊤ B-abs}
      (α : A-⊤ ⊸ A-abs) (β : B-⊤ ⊸ B-abs)
      (f-⊤ : A-⊤ ⊸ B-⊤) (f-abs : A-abs ⊸ B-abs)
      (f-coherence : (a-⊤ : U A-⊤) → U β (U f-⊤ a-⊤) ≡ U f-abs (U α a-⊤)) →
    Abstractionᶜ
      (Abstractionᶜ A-⊤ A-abs α)
      (Abstractionᶜ B-⊤ B-abs β)
      (squareᶜ' α β f-⊤ f-abs f-coherence)
    ≡ Abstractionᶜ A-⊤ B-abs (α ⨾ᶜ f-abs)
  Abstractionᶜ-Abstractionᶜ {A-⊤} {A-abs} {B-⊤} {B-abs} α β f-⊤ f-abs f-coherence =
    cong 𝒞-Glue $
    𝒞-FRACTURE-path
      (𝒞-glue•-path (Abstractionᶜ-FRAC A-⊤ A-abs α))
      (𝒞-glue◦-path (Abstractionᶜ-FRAC B-⊤ B-abs β)) $
    ⊸-path
      (λ i → ⟨ 𝒞-glue•-path (Abstractionᶜ-FRAC A-⊤ A-abs α) i ⟩ᶜ)
      (λ i → ●ᶜ ⟨ 𝒞-glue◦-path (Abstractionᶜ-FRAC B-⊤ B-abs β) i ⟩ᶜ)
      (square-χ•-path
        (squareᶜ' α β f-⊤ f-abs f-coherence .U)
        (●ᶜ.map ((α ⨾ᶜ f-abs) ⨾ᶜ η◦ᶜ) .U)
        (λ g →
            cong (●.map (◯.map (f-abs .U))) (sym (•→◦ g))
          ∙ ●.map-∘ ((α ⨾ᶜ η◦ᶜ) .U) (◯.map (f-abs .U)) (• g)))
