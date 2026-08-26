module Calf.Computation.Abstraction.Copower where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence using (ua→; ua-gluePath)
open import Cubical.Data.Sigma using (ΣPathP)

open import Calf.Core.Abstract using (ABS)
open import Calf.Core.Cost
open import Calf.Value
open import Calf.Value.Open as ◯
open import Calf.Value.Closed as ●
open import Calf.Value.Glue hiding (square)
open import Calf.Value.Abstraction using (square)
open import Calf.Computation
open import Calf.Computation.Copower
open import Calf.Computation.Open as ◯ᶜ
open import Calf.Computation.Closed as ●ᶜ hiding (law)
open import Calf.Computation.Abstraction.Base
open import Calf.Computation.Abstraction.Properties

module _ {X : 𝒱ₚ} where
  ⋊-map : (A ⊸ B) → (X ⋊ A ⊸ X ⋊ B)
  ⋊-map f .U (x , a) = x , f .U a
  ⋊-map f .charge c (x , a) = cong (x ,_) (f .charge c a)

  ⋊-proj₂ : X ⋊ A ⊸ A
  ⋊-proj₂ .U = snd
  ⋊-proj₂ .charge c _ = refl

  module _ {A-⊤ A-abs : 𝒞} {α : A-⊤ ⊸ A-abs} where
    private
      opaque
        ⋊-proj₂ᵃ : Abstractionᶜ (X ⋊ A-⊤) (X ⋊ A-abs) (⋊-map α) ⊸ Abstractionᶜ A-⊤ A-abs α
        ⋊-proj₂ᵃ = squareᶜ' {α = ⋊-map α} {β = α} ⋊-proj₂ ⋊-proj₂ (λ _ → refl)

      opaque
        unfolding Abstractionᶜ

        ⋊-proj₁-glue : U (Abstractionᶜ (X ⋊ A-⊤) (X ⋊ A-abs) (⋊-map α)) → FractureGlue ⟨ X ⟩
        ⋊-proj₁-glue = square {χ = ⋊-map α .U} {ψ = λ x → x} fst fst (λ _ → refl)

        ⋊-proj₁-●-charge : (c : ℂ) (q• : U (●ᶜ (X ⋊ A-⊤)))
          → ●.map fst (●ᶜ (X ⋊ A-⊤) .charge c q•) ≡ ●.map fst q•
        ⋊-proj₁-●-charge c = ●.elim (λ _ → ●-≡-isModal _ _) (λ _ → refl)

        ⋊-proj₁-glue-charge : (c : ℂ) (g : U (Abstractionᶜ (X ⋊ A-⊤) (X ⋊ A-abs) (⋊-map α)))
          → ⋊-proj₁-glue (Abstractionᶜ (X ⋊ A-⊤) (X ⋊ A-abs) (⋊-map α) .charge c g) ≡ ⋊-proj₁-glue g
        ⋊-proj₁-glue-charge c g =
          Glue-path (isSet◯ (isPreorder→isSet (str X))) (⋊-proj₁-●-charge c (• g)) refl

    opaque
      ⋊-Abstractionᶜ : Abstractionᶜ (X ⋊ A-⊤) (X ⋊ A-abs) (⋊-map α) ⊸ X ⋊ Abstractionᶜ A-⊤ A-abs α
      ⋊-Abstractionᶜ .U g = invIsEq fracture-isEquiv (⋊-proj₁-glue g) , ⋊-proj₂ᵃ .U g
      ⋊-Abstractionᶜ .charge c g =
        ΣPathP (cong (invIsEq fracture-isEquiv) (⋊-proj₁-glue-charge c g) , ⋊-proj₂ᵃ .charge c g)

    private opaque
      unfolding ⋊-proj₂ᵃ

      ⋊-proj₂ᵃ-abs : (abs : ⟨ ABS ⟩)
        → PathP
            (λ i →
              ◯[Abstractionᶜ≡A-abs] {X ⋊ A-⊤} {X ⋊ A-abs} {⋊-map α} abs i
                ⊸ ◯[Abstractionᶜ≡A-abs] {A-⊤} {A-abs} {α} abs i)
            ⋊-proj₂ᵃ
            ⋊-proj₂
      ⋊-proj₂ᵃ-abs abs = ◯[squareᶜ'≡f-abs] {f-⊤ = ⋊-proj₂} {⋊-proj₂} {λ _ → refl} abs

    opaque
      unfolding ⋊-proj₁-glue ⋊-Abstractionᶜ ◯[Abstractionᶜ≡A-abs]

      ◯[⋊-Abstractionᶜ≡idᶜ] : (abs : ⟨ ABS ⟩)
        → PathP
            (λ i →
              ◯[Abstractionᶜ≡A-abs] {X ⋊ A-⊤} {X ⋊ A-abs} {⋊-map α} abs i
                ⊸ X ⋊ ◯[Abstractionᶜ≡A-abs] {A-⊤} {A-abs} {α} abs i)
            ⋊-Abstractionᶜ
            idᶜ
      ◯[⋊-Abstractionᶜ≡idᶜ] abs =
        ⊸-path _ (λ i → X ⋊ ◯[Abstractionᶜ≡A-abs] {A-⊤} {A-abs} {α} abs i)
          (ua→ {e = ◯[Abstractionᶜ≃A-abs] {X ⋊ A-⊤} {X ⋊ A-abs} {⋊-map α} abs .fst .U , ◯[Abstractionᶜ≃A-abs] {X ⋊ A-⊤} {X ⋊ A-abs} {⋊-map α} abs .snd} λ g →
            ΣPathP
              {A = λ _ → ⟨ X ⟩}
              {B = λ i _ → U (◯[Abstractionᶜ≡A-abs] {A-⊤} {A-abs} {α} abs i)}
              ( cong (λ h → ◦ h abs) (secIsEq fracture-isEquiv (⋊-proj₁-glue g))
              , λ i →
                  ⋊-proj₂ᵃ-abs abs i .U
                    (ua-gluePath (◯[Abstractionᶜ≃A-abs] {X ⋊ A-⊤} {X ⋊ A-abs} {⋊-map α} abs .fst .U , ◯[Abstractionᶜ≃A-abs] {X ⋊ A-⊤} {X ⋊ A-abs} {⋊-map α} abs .snd)
                      {x = g} {y = ◯[Abstractionᶜ≃A-abs] {X ⋊ A-⊤} {X ⋊ A-abs} {⋊-map α} abs .fst .U g} refl i) ))
