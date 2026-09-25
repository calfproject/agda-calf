module Calf.Value.Glue.Base where

open import Cubical.Foundations.Univalence using (ua; ua→)
open import Cubical.Data.Sigma using (ΣPathP; Σ≡Prop)

open import Calf.Value
open import Calf.Value.Closed as ●
open import Calf.Value.Open as ◯
open import Calf.Value.Product

Glue : (X• X◦ : 𝒱) (χ• : X• → ● X◦) → 𝒱
Glue X• X◦ χ• = Σ[ (x• , x◦) ∈ X• × X◦ ] χ• x• ≡ η• x◦

module _ {X• X◦ : 𝒱} {χ• : X• → ● X◦} where
  • : Glue X• X◦ χ• → X•
  • g = g .fst .fst

  ◦ : Glue X• X◦ χ• → X◦
  ◦ g = g .fst .snd

  •→◦ : (g : Glue X• X◦ χ•) → χ• (• g) ≡ η• (◦ g)
  •→◦ g = g .snd

  opaque
    Glue-path : ∀ {g g' : Glue X• X◦ χ•}
      → isSet X◦
      → • g ≡ • g'
      → ◦ g ≡ ◦ g'
      → g ≡ g'
    Glue-path isSetX◦ p• p◦ =
      Σ≡Prop (λ _ → isSet● isSetX◦ _ _) (ΣPathP (p• , p◦))

  opaque
    isSetGlue : isSet X• → isSet X◦ → isSet (Glue X• X◦ χ•)
    isSetGlue isSetX• isSetX◦ =
      isSetΣ
        (isSet× isSetX• isSetX◦)
        λ _ → isProp→isSet (isSet● isSetX◦ _ _)

  opaque
    isPreorderGlue : isPreorder X• → isPreorder X◦ → isPreorder (Glue X• X◦ χ•)
    isPreorderGlue isPreorderX• isPreorderX◦ =
      isLocalPullback isPreorderX• isPreorderX◦ (isPreorder● isPreorderX◦) χ• η•

record Fracture : 𝒱₁ where
  field
    X• : 𝒱•
    X◦ : 𝒱◦
    χ• : ⟨ X• ⟩ → ● ⟨ X◦ ⟩
open Fracture

Fracture-path
  : {F F' : Fracture}
  → (X•-path : F .X• ≡ F' .X•)
  → (X◦-path : F .X◦ ≡ F' .X◦)
  → PathP
      (λ i → X•-path i .fst → ● (X◦-path i .fst))
      (F .χ•)
      (F' .χ•)
  → F ≡ F'
Fracture-path X•-path X◦-path χ•-path i .X• = X•-path i
Fracture-path X•-path X◦-path χ•-path i .X◦ = X◦-path i
Fracture-path X•-path X◦-path χ•-path i .χ• = χ•-path i

Fracture-ua
  : {F F' : Fracture}
  → (e• : ⟨ F .X• ⟩ ≃ ⟨ F' .X• ⟩)
  → (e◦ : ⟨ F .X◦ ⟩ ≃ ⟨ F' .X◦ ⟩)
  → F' .χ• ∘ equivFun e• ≡ ●.map (equivFun e◦) ∘ F .χ•
  → F ≡ F'
Fracture-ua {F} e• e◦ e•→◦ =
  Fracture-path
    (𝒱•-path (ua e•))
    (𝒱◦-path (ua e◦))
    (ua→ λ x• → ●-ua-gluePath e◦ (sym (funExt⁻ e•→◦ x•)))

fromFracture : Fracture → 𝒱
fromFracture F = Glue ⟨ F .X• ⟩ ⟨ F .X◦ ⟩ (F .χ•)

toFracture : 𝒱 → Fracture
toFracture X .X• = ●• X
toFracture X .X◦ = ◯◦ X
toFracture X .χ• = ●.map η◦

Fracture-Square : Fracture → Fracture → 𝒱
Fracture-Square F₁ F₂ =
  Σ[ (f• , f◦) ∈ (⟨ F₁ .X• ⟩ → ⟨ F₂ .X• ⟩) × (⟨ F₁ .X◦ ⟩ → ⟨ F₂ .X◦ ⟩) ]
    F₂ .χ• ∘ f• ≡ ●.map f◦ ∘ F₁ .χ•

square
  : ∀ {X• X◦ χ Y• Y◦ ψ}
  → (f• : X• → Y•)
  → (f◦ : X◦ → Y◦)
  → ((x• : X•) → ψ (f• x•) ≡ ●.map f◦ (χ x•))
  → Glue X• X◦ χ → Glue Y• Y◦ ψ
square f• f◦ f-coh ((x• , x◦) , h) =
  (f• x• , f◦ x◦) , f-coh x• ∙ cong (●.map f◦) h
