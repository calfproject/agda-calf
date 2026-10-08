module Calf.Value.Seal where

open import Cubical.Data.Sigma

open import Calf.Core.Abstract
open import Calf.Value
open import Calf.Value.Closed as ●
open import Calf.Value.Glue using (Glue; Fracture; toFracture)
open import Calf.Value.Open as ◯
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

fractureᵈ : X → Seal X
fractureᵈ x = (η• x , η◦ x) , ⊑-refl

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

squareᵈ
  : ∀ {X• X◦ χ• Y• Y◦ ψ•}
  → (f• : X• → Y•)
  → (f◦ : X◦ → Y◦)
  → ((x• : X•) → ψ• (f• x•) ⊑ ●.map f◦ (χ• x•))
  → Glue χ• → Glueᵈ ψ•
squareᵈ f• f◦ f-coh ((x• , x◦) , h) =
  (f• x• , f◦ x◦) , ⊑∙≡ (f-coh x•) (cong (●.map f◦) h)

Fracture-Squareᵈ : Fracture → Fracture → 𝒱
Fracture-Squareᵈ F₁ F₂ =
  Σ[ (f• , f◦) ∈ (⟨ F₁ .X• ⟩ → ⟨ F₂ .X• ⟩) × (⟨ F₁ .X◦ ⟩ → ⟨ F₂ .X◦ ⟩) ]
    ((x : ⟨ F₁ .X• ⟩) → F₂ .χ• (f• x) ⊑ ●.map f◦ (F₁ .χ• x))

fracture-and-gluing-squareᵈ : (X → Seal Y) ≃ Fracture-Squareᵈ (toFracture X) (toFracture Y)
fracture-and-gluing-squareᵈ {X} {Y} =
    (X → Seal Y)
  ≃⟨ Σ-Π-≃ ⟩
    (Σ[ f ∈ (X → ● Y × ◯ Y) ] ((x : X) → ●.map η◦ (f x .fst) ⊑ η• (f x .snd)))
  ≃⟨ Σ-cong-equiv-fst Σ-Π-≃ ⟩
    (Σ[ (f• , f◦) ∈ (X → ● Y) × (X → ◯ Y) ] ((x : X) → ●.map η◦ (f• x) ⊑ η• (f◦ x)))
  ≃⟨
    invEquiv
      (Σ-cong-equiv
        (≃-× (●.∘η-≃ (const ●.isModal●)) (◯.∘η-≃ (const ◯.isModal◯)))
        (λ _ → ●.∘η-≃ λ _ → ●.isModal⊑ ●.isModal●))
  ⟩
    Fracture-Squareᵈ (toFracture X) (toFracture Y)
  ■
