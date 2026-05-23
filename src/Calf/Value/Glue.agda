open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

module Calf.Value.Glue (φ : Type) (φ-isProp : isProp φ) where

open import Calf.Value
open import Calf.Value.Open φ φ-isProp as ◯
open import Calf.Value.Closed φ φ-isProp as ●
open import Calf.Phase.Glue φ φ-isProp public

Glueᵛ : (X• : 𝒱•) (X∘ : 𝒱∘) (χ : val (X• .fst) → val (●ᵛ (X∘ .fst))) → 𝒱
Glueᵛ X• X∘ χ .val = Glue (𝒱•→Type• X•) (𝒱∘→Type∘ X∘) χ
Glueᵛ X• X∘ χ .isPreorder = {!   !}

record 𝒱-FRAC : Type₁ where
  field
    X• : 𝒱•
    X∘ : 𝒱∘
    χ : val (X• .fst) → val (●ᵛ (X∘ .fst))
open 𝒱-FRAC

𝒱-FRAC→FRAC : 𝒱-FRAC → FRAC
𝒱-FRAC→FRAC F =
  record
    { X• = 𝒱•→Type• (F .X•)
    ; X∘ = 𝒱∘→Type∘ (F .X∘)
    ; χ = F .χ
    }

𝒱-fromFRAC : 𝒱-FRAC → 𝒱
𝒱-fromFRAC F = Glueᵛ (F .X•) (F .X∘) (F .χ)

𝒱-toFRAC : 𝒱 → 𝒱-FRAC
𝒱-toFRAC X .X• = ●ᵛ X , ●-η-isEquiv
𝒱-toFRAC X .X∘ = ◯ᵛ X , ◯-η-isEquiv
𝒱-toFRAC X .χ = ●.map η∘

𝒱-glue•-path : (F : 𝒱-FRAC) →
  (●ᵛ (𝒱-fromFRAC F) , ●-η-isEquiv) ≡ F .X•
𝒱-glue•-path F =
  Σ≡Prop
    (λ X → isPropIsEquiv (η• {val X}))
    (𝒱-path (cong fst (glue•-path (𝒱-FRAC→FRAC F))))

𝒱-glue∘-path : (F : 𝒱-FRAC) →
  (◯ᵛ (𝒱-fromFRAC F) , ◯-η-isEquiv) ≡ F .X∘
𝒱-glue∘-path F =
  Σ≡Prop
    (λ X → isPropIsEquiv (η∘ {val X}))
    (𝒱-path (cong fst (glue∘-path (𝒱-FRAC→FRAC F))))

𝒱-glue-fracture-section : section 𝒱-toFRAC 𝒱-fromFRAC
𝒱-glue-fracture-section F i .X• = 𝒱-glue•-path F i
𝒱-glue-fracture-section F i .X∘ = 𝒱-glue∘-path F i
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
