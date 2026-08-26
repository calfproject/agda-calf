module Calf.Computation.Glue.Properties where

open import Calf.Core.Abstract
open import Calf.Core.Cost
open import Calf.Value
import Calf.Value.Open as ◯
import Calf.Value.Closed as ●
open import Calf.Value.Glue public
open import Calf.Computation
open import Calf.Computation.Open as ◯ᶜ
open import Calf.Computation.Closed as ●ᶜ
open import Cubical.Foundations.Univalence using (ua→; ua-gluePath)
open import Cubical.Data.Sigma using (ΣPathP; Σ≡Prop)

open import Calf.Computation.Glue.Base
open import Calf.Computation.Glue.Fracture
open 𝒞-FRACTURE

fracture-map
  : (f : A ⊸ B)
  → 𝒞-FractureGlue A ⊸ 𝒞-FractureGlue B
fracture-map f = squareᶜ (●ᶜ.map f) (◯ᶜ.map f) (to𝒞Square f .snd)

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

◯[Glueᶜ≃A◦] : (F : 𝒞-FRACTURE) → ⟨ ABS ⟩ → 𝒞-Glue F ≃ᶜ ⟨ F .A◦ ⟩ᶜ
◯[Glueᶜ≃A◦] F abs =
  proj◦ᶜ F , ◯[Glue≃X◦] (U-FRACTURE F) abs .snd

◯[Glueᶜ≡A◦] : (F : 𝒞-FRACTURE) → ⟨ ABS ⟩ → 𝒞-Glue F ≡ ⟨ F .A◦ ⟩ᶜ
◯[Glueᶜ≡A◦] F abs = uaᶜ (◯[Glueᶜ≃A◦] F abs)

◯[squareᶜ≡f◦] : {F G : 𝒞-FRACTURE}
  → (f• : ⟨ F .A• ⟩ᶜ ⊸ ⟨ G .A• ⟩ᶜ) (f◦ : ⟨ F .A◦ ⟩ᶜ ⊸ ⟨ G .A◦ ⟩ᶜ)
  → (coh : f• ⨾ᶜ G .α• ≡ F .α• ⨾ᶜ ●ᶜ.map f◦) (abs : ⟨ ABS ⟩)
  → PathP (λ i → ◯[Glueᶜ≡A◦] F abs i ⊸ ◯[Glueᶜ≡A◦] G abs i)
      (squareᶜ f• f◦ coh)
      f◦
◯[squareᶜ≡f◦] {F} {G} f• f◦ coh abs =
  uaᶜ-⊸ (◯[Glueᶜ≃A◦] F abs) (◯[Glueᶜ≃A◦] G abs) (⊸-path refl refl refl)
