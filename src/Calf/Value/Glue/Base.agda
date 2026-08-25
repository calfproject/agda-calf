module Calf.Value.Glue.Base where

open import Calf.Value
open import Calf.Value.Closed as ●
open import Calf.Value.Open as ◯
open import Calf.Value.Product

open import Cubical.Data.Sigma using (ΣPathP; Σ≡Prop)

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
    isPreorderGlue pre• pre◦ =
      isLocalPullback pre• pre◦ (isPreorder● pre◦) χ• η•

record 𝒱-FRACTURE : 𝒱₁ where
  field
    X• : 𝒱•
    X◦ : 𝒱◦
    χ• : ⟨ X• ⟩ → ● ⟨ X◦ ⟩
open 𝒱-FRACTURE

𝒱-FRACTURE-path
  : {F G : 𝒱-FRACTURE}
  → (X•-path : F .X• ≡ G .X•)
  → (X◦-path : F .X◦ ≡ G .X◦)
  → PathP
      (λ i → X•-path i .fst → ● (X◦-path i .fst))
      (F .χ•)
      (G .χ•)
  → F ≡ G
𝒱-FRACTURE-path X•-path X◦-path χ•-path i .X• = X•-path i
𝒱-FRACTURE-path X•-path X◦-path χ•-path i .X◦ = X◦-path i
𝒱-FRACTURE-path X•-path X◦-path χ•-path i .χ• = χ•-path i

𝒱-Glue : 𝒱-FRACTURE → 𝒱
𝒱-Glue F = Glue ⟨ F .X• ⟩ ⟨ F .X◦ ⟩ (F .χ•)

𝒱-Fracture : 𝒱 → 𝒱-FRACTURE
𝒱-Fracture X .X• = ●• X
𝒱-Fracture X .X◦ = ◯◦ X
𝒱-Fracture X .χ• = ●.map η◦

𝒱-Square : 𝒱-FRACTURE → 𝒱-FRACTURE → 𝒱
𝒱-Square F G =
  Σ[ (f• , f◦) ∈ (⟨ F .X• ⟩ → ⟨ G .X• ⟩) × (⟨ F .X◦ ⟩ → ⟨ G .X◦ ⟩) ]
    G .χ• ∘ f• ≡ ●.map f◦ ∘ F .χ•

square
  : ∀ {X• X◦ χ Y• Y◦ ψ}
  → (f• : X• → Y•)
  → (f◦ : X◦ → Y◦)
  → ((x• : X•) → ψ (f• x•) ≡ ●.map f◦ (χ x•))
  → Glue X• X◦ χ → Glue Y• Y◦ ψ
square f• f◦ f-coh ((x• , x◦) , h) =
  (f• x• , f◦ x◦) , f-coh x• ∙ cong (●.map f◦) h
