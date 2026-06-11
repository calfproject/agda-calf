open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism

module Calf.Value.Glue where

open import Calf.Core.Abstract
open import Calf.Core.Directed
open import Calf.Value
open import Calf.Value.Open as ◯ᵛ
open import Calf.Value.Closed as ●ᵛ
open import Calf.Phase.Glue (ABS .fst) (ABS .snd) public

Glueᵛ : (X• : 𝒱•) (X◦ : 𝒱◦) (χ• : val (X• .fst) → val (●ᵛ (X◦ .fst))) → 𝒱
Glueᵛ X• X◦ χ• .val = Glue (𝒱•→Type• X•) (𝒱◦→Type◦ X◦) χ•
Glueᵛ X• X◦ χ• .is-set = isSetGlue (X• .fst .is-set) (X◦ .fst .is-set)

record 𝒱-FRAC : Type₁ where
  field
    X• : 𝒱•
    X◦ : 𝒱◦
    χ• : val (X• .fst) → val (●ᵛ (X◦ .fst))
open 𝒱-FRAC

𝒱-FRAC→FRAC : 𝒱-FRAC → FRAC
𝒱-FRAC→FRAC F =
  record
    { X• = 𝒱•→Type• (F .X•)
    ; X◦ = 𝒱◦→Type◦ (F .X◦)
    ; χ• = F .χ•
    }

𝒱-fromFRAC : 𝒱-FRAC → 𝒱
𝒱-fromFRAC F = Glueᵛ (F .X•) (F .X◦) (F .χ•)

𝒱-toFRAC : 𝒱 → 𝒱-FRAC
𝒱-toFRAC X .X• = ●ᵛ X , ●ᵛ.η-isEquiv
𝒱-toFRAC X .X◦ = ◯ᵛ X , ◯ᵛ.η-isEquiv
𝒱-toFRAC X .χ• = ●ᵛ.map (η◦ᵛ {X})

𝒱-glue•-path : (F : 𝒱-FRAC) →
  (●ᵛ (𝒱-fromFRAC F) , ●ᵛ.η-isEquiv) ≡ F .X•
𝒱-glue•-path F =
  Σ≡Prop
    (λ X → isPropIsEquiv (η•ᵛ {X}))
    (𝒱-path (cong fst (glue•-path (𝒱-FRAC→FRAC F))))

𝒱-glue◦-path : (F : 𝒱-FRAC) →
  (◯ᵛ (𝒱-fromFRAC F) , ◯ᵛ.η-isEquiv) ≡ F .X◦
𝒱-glue◦-path F =
  Σ≡Prop
    (λ X → isPropIsEquiv (η◦ᵛ {X}))
    (𝒱-path (cong fst (glue◦-path (𝒱-FRAC→FRAC F))))

𝒱-glue-fracture-section : section 𝒱-toFRAC 𝒱-fromFRAC
𝒱-glue-fracture-section F i .X• = 𝒱-glue•-path F i
𝒱-glue-fracture-section F i .X◦ = 𝒱-glue◦-path F i
𝒱-glue-fracture-section F i .χ• =
  FRAC.χ• (glue-fracture-section (𝒱-FRAC→FRAC F) i)

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


squareᵛ
  : ∀ {X• X◦ χ Y• Y◦ ψ}
  → (f• : val (X• .fst) → val (Y• .fst))
  → (f◦ : val (X◦ .fst) → val (Y◦ .fst))
  → ((x• : val (X• .fst)) → ψ (f• x•) ≡ ●ᵛ.map f◦ (χ x•))
  → val (Glueᵛ X• X◦ χ) → val (Glueᵛ Y• Y◦ ψ)
squareᵛ f• f◦ f-coherence q .• = f• (q .•)
squareᵛ f• f◦ f-coherence q .◦ = f◦ (q .◦)
squareᵛ f• f◦ f-coherence q .•→◦ =
  f-coherence (q .•) ∙ cong (●ᵛ.map f◦) (q .•→◦)

Glueᵛ' : (X-⊤ X-abs : 𝒱) → (val X-⊤ → val X-abs) → 𝒱
Glueᵛ' X-⊤ X-abs χ =
  Glueᵛ
    (●ᵛ X-⊤ , ●ᵛ.η-isEquiv)
    (◯ᵛ X-abs , ◯ᵛ.η-isEquiv)
    (●ᵛ.map (η◦ᵛ {X-abs} ∘ χ))

squareᵛ'
  : ∀ {X-⊤ X-abs χ Y-⊤ Y-abs ψ}
  → (f-⊤ : val X-⊤ → val Y-⊤)
  → (f-abs : val X-abs → val Y-abs)
  → ((x-⊤ : val X-⊤) → ψ (f-⊤ x-⊤) ≡ f-abs (χ x-⊤))
  → val (Glueᵛ' X-⊤ X-abs χ) → val (Glueᵛ' Y-⊤ Y-abs ψ)
squareᵛ' {X-⊤ = X-⊤} {X-abs = X-abs} {χ = χ} {Y-⊤ = Y-⊤} {Y-abs = Y-abs} {ψ = ψ} f-⊤ f-abs f-coherence =
  squareᵛ
    {X• = ●ᵛ X-⊤ , ●ᵛ.η-isEquiv}
    {X◦ = ◯ᵛ X-abs , ◯ᵛ.η-isEquiv}
    {χ = ●ᵛ.map (η◦ᵛ {X-abs} ∘ χ)}
    {Y• = ●ᵛ Y-⊤ , ●ᵛ.η-isEquiv}
    {Y◦ = ◯ᵛ Y-abs , ◯ᵛ.η-isEquiv}
    {ψ = ●ᵛ.map (η◦ᵛ {Y-abs} ∘ ψ)}
    (●ᵛ.map f-⊤)
    (◯ᵛ.map f-abs)
    (λ x• →
        ●ᵛ.map (η◦ᵛ {Y-abs} ∘ ψ) (●ᵛ.map f-⊤ x•)
      ≡⟨ ●ᵛ.map-∘ f-⊤ (η◦ᵛ {Y-abs} ∘ ψ) x• ⟩
        ●ᵛ.map (λ x → η◦ᵛ {Y-abs} (ψ (f-⊤ x))) x•
      ≡⟨ cong (λ f → ●ᵛ.map f x•) (funExt λ x → cong (η◦ᵛ {Y-abs}) (f-coherence x)) ⟩
        ●ᵛ.map (λ x → η◦ᵛ {Y-abs} (f-abs (χ x))) x•
      ≡⟨ sym (●ᵛ.map-∘ (η◦ᵛ {X-abs} ∘ χ) (◯ᵛ.map f-abs) x•) ⟩
        ●ᵛ.map (◯ᵛ.map f-abs) (●ᵛ.map (η◦ᵛ {X-abs} ∘ χ) x•)
      ∎)
