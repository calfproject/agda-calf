module Calf.Value.Seal where

open import Cubical.Data.Sigma

open import Calf.Core.Abstract
open import Calf.Value
open import Calf.Value.Closed as ●
open import Calf.Value.Glue using (Fracture; toFracture)
open import Calf.Value.Open
open import Calf.Value.Product

Glueᵈ : {X• X◦ : 𝒱} (χ• : X• → ● X◦) → 𝒱
Glueᵈ {X•} {X◦} χ• = Σ[ (x• , x◦) ∈ X• × X◦ ] χ• x• ⊑ η• x◦

module _ {X• X◦ : 𝒱} {χ• : X• → ● X◦} where
  proj•ᵈ : Glueᵈ χ• → X•
  proj•ᵈ ((x• , _) , _) = x•

  proj◦ᵈ : Glueᵈ χ• → X◦
  proj◦ᵈ ((_ , x◦) , _) = x◦

  proj•→◦ᵈ : (x : Glueᵈ χ•) → χ• (proj•ᵈ x) ⊑ η• (proj◦ᵈ x)
  proj•→◦ᵈ = proj₂

  opaque
    Glueᵈ-path : ∀ {x x' : Glueᵈ χ•}
      → isPreorder X◦
      → proj•ᵈ x ≡ proj•ᵈ x'
      → proj◦ᵈ x ≡ proj◦ᵈ x'
      → x ≡ x'
    Glueᵈ-path isPreorderX◦ p• p◦ =
      Σ≡Prop (λ _ → isPreorder→isThin (isPreorder● isPreorderX◦) _ _) (ΣPathP (p• , p◦))

  opaque
    isPreorderGlueᵈ : isPreorder X• → isPreorder X◦ → isPreorder (Glueᵈ χ•)
    isPreorderGlueᵈ isPreorderX• isPreorderX◦ =
      isLocalComma isPreorderX• isPreorderX◦ (isPreorder● isPreorderX◦)

open Fracture

fromFractureᵈ : Fracture → 𝒱
fromFractureᵈ F = Glueᵈ (F .χ•)

Seal : 𝒱 → 𝒱
Seal = fromFractureᵈ ∘ toFracture

opaque
  isPreorderSeal : isPreorder X → isPreorder (Seal X)
  isPreorderSeal {X} isPreorderX =
    isPreorderGlueᵈ (isPreorder● isPreorderX) (isPreorder◯ isPreorderX)

Seal-open : ⟨ ABS ⟩ → Seal X ≃ X
Seal-open {X} abs =
    Σ[ (x• , x◦) ∈ ● X × ◯ X ] ●.map η◦ x• ⊑ η• x◦
  ≃⟨ Σ-contractSnd (λ _ → isContr⊑ (◯-isConnected abs)) ⟩
    ● X × ◯ X
  ≃⟨ Σ-contractFst (◯-isConnected abs) ⟩
    ◯ X
  ≃⟨ invEquiv (η◦ , ◯isModal abs) ⟩
    X
  ■
