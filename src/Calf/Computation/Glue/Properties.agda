open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence using (ua→; ua-gluePath)
open import Cubical.Data.Sigma using (ΣPathP; Σ≡Prop)

module Calf.Computation.Glue.Properties (φ : hProp _) where

open import Calf.Core.Cost
open import Calf.Value
import Calf.Value.Open φ as ◯
import Calf.Value.Closed φ as ●
open import Calf.Computation
open import Calf.Computation.Open φ as ◯ᶜ
open import Calf.Computation.Closed φ as ●ᶜ

open import Calf.Computation.Glue.Base φ
open import Calf.Computation.Glue.Fracture φ
open Fractureᶜ

fracture-map
  : (f : A ⊸ B)
  → FractureGlueᶜ A ⊸ FractureGlueᶜ B
fracture-map f = squareᶜ (●ᶜ.map f) (◯ᶜ.map f) (toSquareᶜ f .snd)

fracture-map-coh
  : (f : A ⊸ B)
  → (q• : U (●ᶜ A))
  → (q◦ : U (◯ᶜ A))
  → (qcoh : ●ᶜ.map (η◦ᶜ {A = A}) .U q• ≡ η• q◦)
  → ●.map (η◦ᶜ {A = B} .U) (●ᶜ.map f .U q•)
    ≡ η• (◯.map (f .U) q◦)
fracture-map-coh f q• q◦ qcoh =
  •→◦ (fracture-map f .U ((q• , q◦) , qcoh))

fracture-map-fracture
  : (f : A ⊸ B) (a : U A)
  → fracture-map f .U (fracture {X = U A} a) ≡ fracture {X = U B} (f .U a)
fracture-map-fracture {A} {B} f a =
  Σ≡Prop (λ _ → is-set (●ᶜ (◯ᶜ B)) _ _) refl

Glueᶜ-open-≃ : (F : Fractureᶜ) → ⟨ φ ⟩ → fromFractureᶜ F ≃ᶜ ⟨ F .A◦ ⟩ᶜ
Glueᶜ-open-≃ F p =
  proj◦ᶜ F , Glue-open-≃ (U-Fracture F) p .snd

Glueᶜ-open : (F : Fractureᶜ) → ⟨ φ ⟩ → fromFractureᶜ F ≡ ⟨ F .A◦ ⟩ᶜ
Glueᶜ-open F p = uaᶜ (Glueᶜ-open-≃ F p)

squareᶜ-openP : {F G : Fractureᶜ}
  → (f• : ⟨ F .A• ⟩ᶜ ⊸ ⟨ G .A• ⟩ᶜ) (f◦ : ⟨ F .A◦ ⟩ᶜ ⊸ ⟨ G .A◦ ⟩ᶜ)
  → (coh : f• ⨾ᶜ G .α• ≡ F .α• ⨾ᶜ ●ᶜ.map f◦) (p : ⟨ φ ⟩)
  → PathP (λ i → Glueᶜ-open F p i ⊸ Glueᶜ-open G p i)
      (squareᶜ f• f◦ coh)
      f◦
squareᶜ-openP {F} {G} f• f◦ coh p =
  uaᶜ-⊸ (Glueᶜ-open-≃ F p) (Glueᶜ-open-≃ G p) (⊸-path refl refl refl)
