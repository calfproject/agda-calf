open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Calf.Value.Seal (φ : hProp _) where

open import Calf.Core.Cost
open import Calf.Core.Directed
open import Calf.Computation
open import Calf.Value
open import Calf.Value.Product
open import Calf.Value.Closed φ
open import Calf.Value.Open φ
open import Calf.Value.Glue φ using (Fracture; toFracture)

Glueᵈ : (X• X◦ : 𝒱) (χ• : X• → ● X◦) → 𝒱
Glueᵈ X• X◦ χ• = Σ[ (x• , x◦) ∈ X• × X◦ ] χ• x• ⊑ η• x◦

module _ {X• X◦ : 𝒱} {χ• : X• → ● X◦} where
  • : Glueᵈ X• X◦ χ• → X•
  • g = g .fst .fst

  ◦ : Glueᵈ X• X◦ χ• → X◦
  ◦ g = g .fst .snd

  •→◦ : (g : Glueᵈ X• X◦ χ•) → χ• (• g) ⊑ η• (◦ g)
  •→◦ g = g .snd

open Fracture

opaque
  isPreorderGlueᵈ : (X• X◦ : 𝒱) {χ• : X• → ● X◦}
    → isPreorder X•
    → isPreorder X◦
    → isPreorder (Glueᵈ X• X◦ χ•)
  isPreorderGlueᵈ X• X◦ isPreorderX• isPreorderX◦ =
    isLocalComma isPreorderX• isPreorderX◦ (isPreorder● isPreorderX◦)

fromFractureᵈ : Fracture → 𝒱
fromFractureᵈ F = Glueᵈ ⟨ F .X• ⟩ ⟨ F .X◦ ⟩ (F .χ•)

Seal : 𝒱 → 𝒱
Seal = fromFractureᵈ ∘ toFracture

opaque
  isPreorderSeal : isPreorder X → isPreorder (Seal X)
  isPreorderSeal {X} isPreorderX =
    isPreorderGlueᵈ (● X) (◯ X) (isPreorder● isPreorderX) (isPreorder◯ isPreorderX)
