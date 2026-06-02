open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism

module Calf.Value.Glue where

open import Calf.Core.Abstract
open import Calf.Value
open import Calf.Value.Open as ◯
open import Calf.Value.Closed as ●
open import Calf.Phase.Glue (ABS .fst) (ABS .snd) public

Glueᵛ : (X• : 𝒱•) (X◦ : 𝒱◦) (χ : val (X• .fst) → val (●ᵛ (X◦ .fst))) → 𝒱
Glueᵛ X• X◦ χ .val = Glue (𝒱•→Type• X•) (𝒱◦→Type◦ X◦) χ
Glueᵛ X• X◦ χ .is-set = isSetGlue (X• .fst .is-set) (X◦ .fst .is-set)

record 𝒱-FRAC : Type₁ where
  field
    X• : 𝒱•
    X◦ : 𝒱◦
    χ : val (X• .fst) → val (●ᵛ (X◦ .fst))
open 𝒱-FRAC

𝒱-FRAC→FRAC : 𝒱-FRAC → FRAC
𝒱-FRAC→FRAC F =
  record
    { X• = 𝒱•→Type• (F .X•)
    ; X◦ = 𝒱◦→Type◦ (F .X◦)
    ; χ = F .χ
    }

𝒱-fromFRAC : 𝒱-FRAC → 𝒱
𝒱-fromFRAC F = Glueᵛ (F .X•) (F .X◦) (F .χ)

𝒱-toFRAC : 𝒱 → 𝒱-FRAC
𝒱-toFRAC X .X• = ●ᵛ X , ●ᵛ-η•ᵛ-isEquiv {X}
𝒱-toFRAC X .X◦ = ◯ᵛ X , ◯ᵛ-ηᵛ-isEquiv
𝒱-toFRAC X .χ = ●.map (η◦ᵛ {X})

squareᵛ
  : ∀ {X• X◦ α Y• Y◦ β}
  → (f• : val (X• .fst) → val (Y• .fst))
  → (f◦ : val (X◦ .fst) → val (Y◦ .fst))
  → ((x• : val (X• .fst)) → β (f• x•) ≡ ●.map f◦ (α x•))
  → val (Glueᵛ X• X◦ α) → val (Glueᵛ Y• Y◦ β)
squareᵛ f• f◦ f-coherence q .• = f• (q .•)
squareᵛ f• f◦ f-coherence q .◦ = f◦ (q .◦)
squareᵛ f• f◦ f-coherence q .•→◦ =
  f-coherence (q .•) ∙ cong (●.map f◦) (q .•→◦)

Glueᵛ' : (X-⊤ X-abs : 𝒱) → (val X-⊤ → val X-abs) → 𝒱
Glueᵛ' X-⊤ X-abs α =
  Glueᵛ
    (●ᵛ X-⊤ , ●ᵛ-η•ᵛ-isEquiv {X-⊤})
    (◯ᵛ X-abs , ◯ᵛ-ηᵛ-isEquiv)
    (●.map (η◦ᵛ {X-abs} ∘ α))

squareᵛ'
  : ∀ {X-⊤ X-abs α Y-⊤ Y-abs β}
  → (f-⊤ : val X-⊤ → val Y-⊤)
  → (f-abs : val X-abs → val Y-abs)
  → ((x-⊤ : val X-⊤) → β (f-⊤ x-⊤) ≡ f-abs (α x-⊤))
  → val (Glueᵛ' X-⊤ X-abs α) → val (Glueᵛ' Y-⊤ Y-abs β)
squareᵛ' {X-abs = X-abs} {α = α} {Y-abs = Y-abs} {β = β} f-⊤ f-abs f-coherence =
  squareᵛ
    (●.map f-⊤)
    (◯.map f-abs)
    (λ x• →
        ●.map (η◦ᵛ {Y-abs} ∘ β) (●.map f-⊤ x•)
      ≡⟨ ●.●-map-∘ f-⊤ (η◦ᵛ {Y-abs} ∘ β) x• ⟩
        ●.map (λ x → η◦ᵛ {Y-abs} (β (f-⊤ x))) x•
      ≡⟨ cong (λ f → ●.map f x•) (funExt λ x → cong (η◦ᵛ {Y-abs}) (f-coherence x)) ⟩
        ●.map (λ x → η◦ᵛ {Y-abs} (f-abs (α x))) x•
      ≡⟨ sym (●.●-map-∘ (η◦ᵛ {X-abs} ∘ α) (◯.map f-abs) x•) ⟩
        ●.map (◯.map f-abs) (●.map (η◦ᵛ {X-abs} ∘ α) x•)
      ∎)

𝒱-glue•-path : (F : 𝒱-FRAC) →
  (●ᵛ (𝒱-fromFRAC F) , ●ᵛ-η•ᵛ-isEquiv {𝒱-fromFRAC F}) ≡ F .X•
𝒱-glue•-path F =
  Σ≡Prop
    (λ X → isPropIsEquiv (η•ᵛ {X}))
    (𝒱-path (cong fst (glue•-path (𝒱-FRAC→FRAC F))))

𝒱-glue◦-path : (F : 𝒱-FRAC) →
  (◯ᵛ (𝒱-fromFRAC F) , ◯ᵛ-ηᵛ-isEquiv) ≡ F .X◦
𝒱-glue◦-path F =
  Σ≡Prop
    (λ X → isPropIsEquiv (η◦ᵛ {X}))
    (𝒱-path (cong fst (glue◦-path (𝒱-FRAC→FRAC F))))

𝒱-glue-fracture-section : section 𝒱-toFRAC 𝒱-fromFRAC
𝒱-glue-fracture-section F i .X• = 𝒱-glue•-path F i
𝒱-glue-fracture-section F i .X◦ = 𝒱-glue◦-path F i
𝒱-glue-fracture-section F i .χ =
  FRAC.χ (glue-fracture-section (𝒱-FRAC→FRAC F) i)

𝒱-glue-fracture-retract : retract 𝒱-toFRAC 𝒱-fromFRAC
𝒱-glue-fracture-retract X = 𝒱-path (glue-fracture-retract (val X))

𝒱-fracture-and-gluing : 𝒱 ≃ 𝒱-FRAC
𝒱-fracture-and-gluing .fst = 𝒱-toFRAC
𝒱-fracture-and-gluing .snd =
  isoToIsEquiv
    (iso
      𝒱-toFRAC
      𝒱-fromFRAC
      𝒱-glue-fracture-section
      𝒱-glue-fracture-retract)
