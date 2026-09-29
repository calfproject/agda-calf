module Calf.Computation.Glue.Fracture where

open import Cubical.Foundations.Equiv.Properties using (congEquiv)
open import Cubical.Foundations.Path
  using (compPathlEquiv; compPathrEquiv; symIso)
open import Cubical.Foundations.Univalence using (ua)

open import Calf.Core.Abstract
open import Calf.Value
import Calf.Value.Closed as ●
import Calf.Value.Open as ◯
open import Calf.Value.Product
open import Calf.Value.Sigma
open import Calf.Computation
open import Calf.Computation.Closed as ●ᶜ
open import Calf.Computation.Open as ◯ᶜ

open import Calf.Computation.Glue.Base

open import Calf.Value.Glue public

module _ where
  open Fractureᶜ

  FractureGlueᶜ : 𝒞 → 𝒞
  FractureGlueᶜ = fromFractureᶜ ∘ toFractureᶜ

  fractureᶜ : A ⊸ FractureGlueᶜ A
  fractureᶜ .U = fracture
  fractureᶜ {A} .charge c a = Glue-path (is-set (◯ᶜ A)) refl refl

  glue-fracture-retractᶜ : retract toFractureᶜ fromFractureᶜ
  glue-fracture-retractᶜ A = sym (conservativity fractureᶜ fracture-isEquiv)

  glue•ᶜ : (F : Fractureᶜ) → ●ᶜ (fromFractureᶜ F) ≃ᶜ ⟨ F .A• ⟩ᶜ
  glue•ᶜ F =
    ●ᶜ-rec (F .A•) (proj•ᶜ {α• = F .α•}) ,
    equivIsEquiv (glue• (U-Fracture F))

  glue◦ᶜ : (F : Fractureᶜ) → ◯ᶜ (fromFractureᶜ F) ≃ᶜ ⟨ F .A◦ ⟩ᶜ
  glue◦ᶜ F =
    ◯ᶜ-rec (F .A◦) (proj◦ᶜ {α• = F .α•}) ,
    ◯.rec-isEquiv (strᶜ (F .A◦)) (glue◦ (U-Fracture F)) (glue◦-β (U-Fracture F))

  glue◦ᶜ-β : (F : Fractureᶜ) (a : U (fromFractureᶜ F))
    → equivFunᶜ (glue◦ᶜ F) .U (η◦ a) ≡ proj◦ a
  glue◦ᶜ-β = glue◦-β ∘ U-Fracture

  opaque
    glue-fracture-sectionᶜ : section toFractureᶜ fromFractureᶜ
    glue-fracture-sectionᶜ F =
      Fractureᶜ-ua (glue•ᶜ F) (glue◦ᶜ F) $
      ●.η-ext (λ _ → ●.isModal●) $ funExt λ a →
        proj•→◦ a ∙ cong η• (sym (glue◦ᶜ-β F a))

  fracture-and-gluingᶜ : 𝒞 ≃ Fractureᶜ
  fracture-and-gluingᶜ =
    isoToEquiv
      (iso
        toFractureᶜ
        fromFractureᶜ
        glue-fracture-sectionᶜ
        glue-fracture-retractᶜ)

  Glueᶜ-open : (F : Fractureᶜ) → ⟨ ABS ⟩ → fromFractureᶜ F ≃ᶜ ⟨ F .A◦ ⟩ᶜ
  Glueᶜ-open F abs =
    proj◦ᶜ {⟨ F .A• ⟩ᶜ} {⟨ F .A◦ ⟩ᶜ} {F .α•} ,
    equivIsEquiv (Glue-open (U-Fracture F) abs)

module _ where
  fracture-and-gluing-squareᶜ : (A ⊸ B) ≃ Fractureᶜ-Square (toFractureᶜ A) (toFractureᶜ B)
  fracture-and-gluing-squareᶜ {A} {B} =
      (A ⊸ B)
    ≃⟨ equiv⊸Cod (fractureᶜ , fracture-isEquiv) ⟩
      A ⊸ FractureGlueᶜ B
    ≃⟨ ⊸-Glueᶜ-≃ ⟩
      (Σ[ (f• , f◦) ∈ (A ⊸ ●ᶜ B) × (A ⊸ ◯ᶜ B) ] f• ⨾ᶜ ●ᶜ.map η◦ᶜ ≡ f◦ ⨾ᶜ η•ᶜ)
    ≃⟨
      invEquiv
        (Σ-cong-equiv
          (≃-× (⊸-precomp-η•ᶜ-≃ (●ᶜ• B)) (⊸-precomp-η◦ᶜ-≃ (◯ᶜ◦ B)))
          (λ (f• , f◦) →
            congEquiv (⊸-precomp-η•ᶜ-≃ (●ᶜ• (◯ᶜ B)))
            ∙ₑ compPathlEquiv (⨾ᶜ-assoc η•ᶜ f• (●ᶜ.map η◦ᶜ))
            ∙ₑ compPathrEquiv (funExtᶜ λ _ → refl)))
    ⟩
      Fractureᶜ-Square (toFractureᶜ A) (toFractureᶜ B)
    ■

  toSquareᶜ : (A ⊸ B) → Fractureᶜ-Square (toFractureᶜ A) (toFractureᶜ B)
  toSquareᶜ = equivFun fracture-and-gluing-squareᶜ
