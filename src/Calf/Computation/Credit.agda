module Calf.Computation.Credit where

open import Cubical.Foundations.Path using (fromPathP⁻)
open import Cubical.Foundations.Transport using (transport⁻-fillerExt⁻)
open import Cubical.Foundations.Univalence using (ua)

open import Calf.Core.Abstract
open import Calf.Core.Cost
open import Calf.Value
open import Calf.Value.Closed as ●
open import Calf.Computation
open import Calf.Computation.Abstraction
open import Calf.Computation.Closed as ●ᶜ
open import Calf.Computation.Glue hiding (squareᶜ)
open import Calf.Computation.Open as ◯ᶜ
open import Calf.Computation.Seal

open Fractureᶜ

opaque
  infixr 5 ▷[_]_

  ▷[_]_ : ℂ → 𝒞 → 𝒞
  ▷[ c ] A = Abstractionᶜ (chargeᶜ {A} c)

  ▷-map : (A ⊸ B) → (▷[ c ] A ⊸ ▷[ c ] B)
  ▷-map {A} {B} {c} f =
    squareᶜ (chargeᶜ c) (chargeᶜ c)
      f
      f
      (sym ∘ f .charge c)

  ▷-0 : ▷[ 0ℂ ] A ≃ᶜ A
  ▷-0 {A} =
    subst (λ f → Abstractionᶜ f ≃ᶜ A)
      (sym chargeᶜ-0)
      (invEquivᶜ (Abstractionᶜ-id A))

  ▷-+ : ▷[ c₁ +ℂ c₂ ] A ≃ᶜ ▷[ c₁ ] ▷[ c₂ ] A
  ▷-+ {c₁} {c₂} {A} =
      ▷[ c₁ +ℂ c₂ ] A
    ≃ᶜ⟨⟩
      Abstractionᶜ (chargeᶜ (c₁ +ℂ c₂))
    ≃ᶜ⟨ Abstractionᶜ-≃ (idEquivᶜ A) (idEquivᶜ A) (λ _ → sym (A .charge-+)) ⟩
      Abstractionᶜ (chargeᶜ {A} c₂ ⨾ᶜ chargeᶜ c₁)
    ≃ᶜ⟨
      invEquivᶜ
        (Abstractionᶜ-fuse
          (chargeᶜ c₂) (chargeᶜ c₂)
          (chargeᶜ c₁) (chargeᶜ c₁)
          (funExtᶜ⁻ (chargeᶜ-comm {A} c₁ c₂)))
    ⟩
      Abstractionᶜ (squareᶜ (chargeᶜ c₂) (chargeᶜ c₂) (chargeᶜ c₁) (chargeᶜ c₁) _)
    ≃ᶜ⟨ Abstractionᶜ-≃ (idEquivᶜ _) (idEquivᶜ _) (λ _ → Glue-path (is-set (◯ᶜ A)) refl refl) ⟩
      Abstractionᶜ (chargeᶜ c₁)
    ≃ᶜ⟨⟩
      ▷[ c₁ ] ▷[ c₂ ] A
    ■ᶜ

  ▷-open : ⟨ ABS ⟩ → (c : ℂ) (A : 𝒞) → ▷[ c ] A ≃ᶜ A
  ▷-open abs c A = Abstractionᶜ-open (chargeᶜ c) abs

  ▷-●ᶜ : (c : ℂ) (A : 𝒞) → ●ᶜ (▷[ c ] A) ≃ᶜ ●ᶜ A
  ▷-●ᶜ c A = ●ᶜ-Abstractionᶜ (chargeᶜ c)

  ▷-◯ᶜ : (c : ℂ) (A : 𝒞) → ◯ᶜ (▷[ c ] A) ≃ᶜ ◯ᶜ A
  ▷-◯ᶜ c A = ◯ᶜ-Abstractionᶜ (chargeᶜ c)

  waste : (A : 𝒞) → c ⊑ c' → ▷[ c' ] A ⊸ᵈ ▷[ c ] A
  waste {c} {c'} A c⊑c' =
    squareᵈᶜ (chargeᶜ c') (chargeᶜ c) idᶜ idᶜ λ a →
    mono (flip (A .charge) a) c⊑c'

  save : (A : 𝒞) (c : ℂ) → A ⊸ ▷[ c ] A
  save A c = injᶜ-⊤ (chargeᶜ c)

  spend : (A : 𝒞) (c : ℂ) → ▷[ c ] A ⊸ A
  spend A c = projᶜ-abs (chargeᶜ c)

  save⨾spend≡chargeᶜ : (c : ℂ) → save A c ⨾ᶜ spend A c ≡ chargeᶜ c
  save⨾spend≡chargeᶜ = injᶜ-projᶜ ∘ chargeᶜ
