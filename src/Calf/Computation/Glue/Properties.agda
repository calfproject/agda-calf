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
fracture-map {A} {B} f .U ((q• , q◦) , qcoh) =
  (●ᶜ.map f .U q• , ◯.map (f .U) q◦) ,
  ( ●.map (η◦ᶜ {A = B} .U) (●ᶜ.map f .U q•)
  ≡⟨ ●.map-∘ (f .U) (η◦ᶜ {A = B} .U) q• ⟩
    ●.map (λ a → η◦ᶜ {A = B} .U (f .U a)) q•
  ≡⟨ sym (●.map-∘ (η◦ᶜ {A = A} .U) (◯.map (f .U)) q•) ⟩
    ●.map (◯.map (f .U)) (●.map (η◦ᶜ {A = A} .U) q•)
  ≡⟨ cong (●.map (◯.map (f .U))) qcoh ⟩
    η• (◯.map (f .U) q◦)
  ∎ )
fracture-map {A} {B} f .charge c q =
  Σ≡Prop (λ _ → is-set (●ᶜ (◯ᶜ B)) _ _)
    (ΣPathP (●ᶜ.map f .charge c (• q) , λ i p → f .charge c (◦ q p) i))

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

𝒞-fracture-≡
  : {A B : 𝒞}
  → (p• : ●ᶜ A ≡ ●ᶜ B)
  → (p◦ : ◯ᶜ A ≡ ◯ᶜ B)
  → PathP (λ i → p• i ⊸ ●ᶜ (p◦ i)) (●ᶜ.map (η◦ᶜ {A = A})) (●ᶜ.map (η◦ᶜ {A = B}))
  → A ≡ B
𝒞-fracture-≡ {A} {B} p• p◦ pα =
    sym (𝒞-glue-fracture-retract A)
  ∙ cong 𝒞-Glue F-path
  ∙ 𝒞-glue-fracture-retract B
  where
    F-path : 𝒞-Fracture A ≡ 𝒞-Fracture B
    F-path = 𝒞-FRACTURE-path (●ᶜ.𝒞•-path p•) (◯ᶜ.𝒞◦-path p◦) pα

◯[Glueᶜ≃A◦] : (F : 𝒞-FRACTURE) → ⟨ ABS ⟩ → 𝒞-Glue F ≃ᶜ ⟨ F .A◦ ⟩ᶜ
◯[Glueᶜ≃A◦] F abs =
  proj◦ᶜ F , ◯[Glue≃X◦] (U-FRACTURE F) abs .snd

◯[Glueᶜ≡A◦] : (F : 𝒞-FRACTURE) → ⟨ ABS ⟩ → 𝒞-Glue F ≡ ⟨ F .A◦ ⟩ᶜ
◯[Glueᶜ≡A◦] F abs = uaᶜ (◯[Glueᶜ≃A◦] F abs)

◯[squareᶜ≡f◦] : {F G : 𝒞-FRACTURE}
    {f• : ⟨ F .A• ⟩ᶜ ⊸ ⟨ G .A• ⟩ᶜ} {f◦ : ⟨ F .A◦ ⟩ᶜ ⊸ ⟨ G .A◦ ⟩ᶜ}
    {coh : f• ⨾ᶜ G .α• ≡ F .α• ⨾ᶜ ●ᶜ.map f◦} (abs : ⟨ ABS ⟩)
  → PathP (λ i → ◯[Glueᶜ≡A◦] F abs i ⊸ ◯[Glueᶜ≡A◦] G abs i)
      (squareᶜ f• f◦ coh)
      f◦
◯[squareᶜ≡f◦] {F} {G} {f•} {f◦} {coh} abs =
  ⊸-path
    (◯[Glueᶜ≡A◦] F abs)
    (◯[Glueᶜ≡A◦] G abs)
    (ua→
      {e = ◯[Glueᶜ≃A◦] F abs .fst .U , ◯[Glueᶜ≃A◦] F abs .snd}
      {B = λ i → U (◯[Glueᶜ≡A◦] G abs i)}
      (λ _ →
        ua-gluePath
          (◯[Glueᶜ≃A◦] G abs .fst .U , ◯[Glueᶜ≃A◦] G abs .snd)
          refl))
