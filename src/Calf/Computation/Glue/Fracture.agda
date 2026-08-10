module Calf.Computation.Glue.Fracture where

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties using (congEquiv)
open import Cubical.Foundations.Path using (compPathlEquiv; compPathrEquiv)
open import Cubical.Foundations.Univalence using (ua)

open import Calf.Core.Cost
open import Calf.Value
import Calf.Value.Open as ◯
import Calf.Value.Closed as ●
open import Calf.Value.Glue public
open import Calf.Value.Product
open import Calf.Value.Sigma
open import Calf.Computation
open import Calf.Computation.Open as ◯ᶜ
open import Calf.Computation.Closed as ●ᶜ

open import Calf.Computation.Glue.Base
open 𝒞-FRACTURE

glue•-charge
  : (F : 𝒞-FRACTURE) (c : ℂ) (g• : U (●ᶜ (𝒞-Glue F)))
  → equivFun (glue•-equiv (U-FRACTURE F)) (●ᶜ (𝒞-Glue F) .charge c g•)
  ≡ ⟨ F .A• ⟩ᶜ .charge c (equivFun (glue•-equiv (U-FRACTURE F)) g•)
glue•-charge F c =
  ●.elim (λ g• → ●.isModal≡ (F .A• .snd)) λ g →
      glue•-β (U-FRACTURE F) (𝒞-Glue F .charge c g)
    ∙ sym (cong (⟨ F .A• ⟩ᶜ .charge c) (glue•-β (U-FRACTURE F) g))

glue◦-charge
  : (F : 𝒞-FRACTURE) (c : ℂ) (g◦ : U (◯ᶜ (𝒞-Glue F)))
  → equivFun (glue◦-equiv (U-FRACTURE F)) (◯ᶜ (𝒞-Glue F) .charge c g◦)
  ≡ ⟨ F .A◦ ⟩ᶜ .charge c (equivFun (glue◦-equiv (U-FRACTURE F)) g◦)
glue◦-charge F c =
  ◯.elim (λ g◦ → ◯.isModal≡ (F .A◦ .snd)) λ g →
      glue◦-β (U-FRACTURE F) (𝒞-Glue F .charge c g)
    ∙ sym (cong (⟨ F .A◦ ⟩ᶜ .charge c) (glue◦-β (U-FRACTURE F) g))

𝒞-glue•-path : (F : 𝒞-FRACTURE) → ●ᶜ• (𝒞-Glue F) ≡ F .A•
𝒞-glue•-path F =
  𝒞•-path
    (𝒞-path
      (ua (glue•-equiv (U-FRACTURE F)))
      (charge-path
        (glue•-equiv (U-FRACTURE F))
        (●ᶜ (𝒞-Glue F) .charge)
        (⟨ F .A• ⟩ᶜ .charge)
        (glue•-charge F)))

𝒞-glue◦-path : (F : 𝒞-FRACTURE) → ◯ᶜ◦ (𝒞-Glue F) ≡ F .A◦
𝒞-glue◦-path F =
  𝒞◦-path
    (𝒞-path
      (ua (glue◦-equiv (U-FRACTURE F)))
      (charge-path
        (glue◦-equiv (U-FRACTURE F))
        (◯ᶜ (𝒞-Glue F) .charge)
        (⟨ F .A◦ ⟩ᶜ .charge)
        (glue◦-charge F)))

opaque
  𝒞-glue-fracture-section : section 𝒞-Fracture 𝒞-Glue
  𝒞-glue-fracture-section F =
    𝒞-FRACTURE-path
      (𝒞-glue•-path F)
      (𝒞-glue◦-path F)
      (⊸-path
        (λ i → ⟨ 𝒞-glue•-path F i ⟩ᶜ)
        (λ i → ●ᶜ ⟨ 𝒞-glue◦-path F i ⟩ᶜ)
        (λ i → 𝒱-FRACTURE.χ• (glue-fracture-section (U-FRACTURE F) i))) 

  𝒞-glue-fracture-section-α• : (F : 𝒞-FRACTURE) →
    PathP
      (λ i →
        ⟨ 𝒞-glue•-path F (~ i) ⟩ᶜ ⊸
        ●ᶜ ⟨ 𝒞-glue◦-path F (~ i) ⟩ᶜ)
      (F .α•)
      (𝒞-Fracture (𝒞-Glue F) .α•)
  𝒞-glue-fracture-section-α• F i =
    𝒞-glue-fracture-section F (~ i) .α•

𝒞-fracture : A ⊸ 𝒞-Glue (𝒞-Fracture A)
𝒞-fracture .U = fracture
𝒞-fracture {A} .charge c a = Glue-path (isSet◯ (A .is-set)) refl refl

opaque
  𝒞-glue-fracture-retract : retract 𝒞-Fracture 𝒞-Glue
  𝒞-glue-fracture-retract A =
    sym (conservativity (𝒞-fracture {A}) fracture-isEquiv)

𝒞-fracture-and-gluing : 𝒞 ≃ 𝒞-FRACTURE
𝒞-fracture-and-gluing =
  isoToEquiv
    (iso
      𝒞-Fracture
      𝒞-Glue
      𝒞-glue-fracture-section
      𝒞-glue-fracture-retract)

to𝒞Square : (A ⊸ B) → 𝒞-Square (𝒞-Fracture A) (𝒞-Fracture B)
to𝒞Square f .𝒞-Square.f• = ●ᶜ.map f
to𝒞Square f .𝒞-Square.f◦ = ◯ᶜ.map f
to𝒞Square f .𝒞-Square.f-coh = toSquare (U f) .𝒱-Square.f-coh

𝒞-fracture-and-gluing-square : (A ⊸ B) ≃ 𝒞-Square (𝒞-Fracture A) (𝒞-Fracture B)
𝒞-fracture-and-gluing-square {A} {B} =
    (A ⊸ B)
  ≃⟨ ⊸-postcomp-≃ 𝒞-fracture fracture-isEquiv ⟩
    (A ⊸ 𝒞-Glue (𝒞-Fracture B))
  ≃⟨ ⊸-Glueᶜ-≃ {A} {𝒞-Fracture B} ⟩
    (Σ[ (h◦ , h•) ∈ (A ⊸ ◯ᶜ B) × (A ⊸ ●ᶜ B) ]
      (h◦ ⨾ᶜ η•ᶜ ≡ h• ⨾ᶜ ●ᶜ.map η◦ᶜ))
  ≃⟨ invEquiv (Σ-cong-equiv
       (≃-× (⊸-precomp-η◦ᶜ-≃ (◯ᶜ◦ B)) (⊸-precomp-η•ᶜ-≃ (●ᶜ• B)))
       (λ (f◦ , f•) →
           congEquiv (⊸-precomp-η•ᶜ-≃ (●ᶜ• (◯ᶜ B)))
         ∙ₑ compPathrEquiv (assoc-η f•)
         ∙ₑ compPathlEquiv (sym (natural-η f◦)))) ⟩
    (Σ[ (f◦ , f•) ∈ (◯ᶜ A ⊸ ◯ᶜ B) × (●ᶜ A ⊸ ●ᶜ B) ]
      (●ᶜ.map η◦ᶜ ⨾ᶜ ●ᶜ.map f◦ ≡ f• ⨾ᶜ ●ᶜ.map η◦ᶜ))
  ≃⟨ invEquiv Squareᶜ-pullback-≃ ⟩
    𝒞-Square (𝒞-Fracture A) (𝒞-Fracture B)
  ■
  where
    opaque
      natural-η : (f◦ : ◯ᶜ A ⊸ ◯ᶜ B)
        → η•ᶜ {A} ⨾ᶜ (●ᶜ.map η◦ᶜ ⨾ᶜ ●ᶜ.map f◦) ≡ (η◦ᶜ ⨾ᶜ f◦) ⨾ᶜ η•ᶜ
      natural-η f◦ = ⊸-path refl refl refl

    opaque
      assoc-η : (f• : ●ᶜ A ⊸ ●ᶜ B)
        → η•ᶜ ⨾ᶜ (f• ⨾ᶜ ●ᶜ.map η◦ᶜ) ≡ (η•ᶜ ⨾ᶜ f•) ⨾ᶜ ●ᶜ.map η◦ᶜ
      assoc-η f• = ⊸-path refl refl refl
