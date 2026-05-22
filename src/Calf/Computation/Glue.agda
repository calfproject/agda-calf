open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Calf.Computation.Glue (φ : Type) (φ-isProp : isProp φ) where

open import Calf.Computation
open import Calf.Computation.Open φ φ-isProp as ◯
open import Calf.Computation.Closed φ φ-isProp as ●
open import Calf.Value.Glue φ φ-isProp public
open import Cubical.Foundations.Equiv

Glueᶜ : (A• : 𝒞•) (A∘ : 𝒞∘) (α : A• .fst ⊸ ●ᶜ (A∘ .fst)) → 𝒞
Glueᶜ A• A∘ α .U = Glueᵛ (U• A•) (U∘ A∘) (α .U)
Glueᶜ A• A∘ α .charge c a .• = A• .fst .charge c (a .•)
Glueᶜ A• A∘ α .charge c a .∘ = A∘ .fst .charge c (a .∘)
Glueᶜ A• A∘ α .charge c a .•→∘ = α .charge c (a .•) ∙ cong (●ᶜ (A∘ .fst) .charge c) (a .•→∘)
Glueᶜ A• A∘ α .charge/0 {a} i .• = A• .fst .charge/0 {a .•} i
Glueᶜ A• A∘ α .charge/0 {a} i .∘ = A∘ .fst .charge/0 {a .∘} i
Glueᶜ A• A∘ α .charge/0 {a} i .•→∘ = {!   !}
Glueᶜ A• A∘ α .charge/+ = {!   !}

record 𝒞-FRAC : Type₁ where
  field
    A• : 𝒞•
    A∘ : 𝒞∘
    α : A• .fst ⊸ ●ᶜ (A∘ .fst)
open 𝒞-FRAC

𝒞-fracture-and-gluing : 𝒞 ≃ 𝒞-FRAC
𝒞-fracture-and-gluing .fst A .A• = {!   !}
𝒞-fracture-and-gluing .fst A .A∘ = {!   !}
𝒞-fracture-and-gluing .fst A .α = {!   !}
𝒞-fracture-and-gluing .snd .equiv-proof A = {!   !}
