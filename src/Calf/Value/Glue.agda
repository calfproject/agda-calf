open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Calf.Value.Glue (φ : Type) (φ-isProp : isProp φ) where

open import Calf.Value
open import Calf.Value.Open φ φ-isProp as ◯
open import Calf.Value.Closed φ φ-isProp as ●
open import Calf.Phase.Glue φ φ-isProp public
open import Cubical.Foundations.Equiv

Glueᵛ : (X• : 𝒱•) (X∘ : 𝒱∘) (χ : val (X• .fst) → val (●ᵛ (X∘ .fst))) → 𝒱
Glueᵛ X• X∘ χ .val = Glue (𝒱•→Type• X•) (𝒱∘→Type∘ X∘) χ
Glueᵛ X• X∘ χ .isPreorder = {!   !}

record 𝒱-FRAC : Type₁ where
  field
    X• : 𝒱•
    X∘ : 𝒱∘
    χ : val (X• .fst) → val (●ᵛ (X∘ .fst))
open 𝒱-FRAC

𝒱-fracture-and-gluing : 𝒱 ≃ 𝒱-FRAC
𝒱-fracture-and-gluing .fst X = {!   !}
𝒱-fracture-and-gluing .snd = {!   !}
