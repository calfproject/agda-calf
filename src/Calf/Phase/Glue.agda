open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Calf.Phase.Glue (φ : Type) (φ-isProp : isProp φ) where

open import Calf.Phase.Open φ φ-isProp as ◯
open import Calf.Phase.Closed φ φ-isProp as ●
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure

record Glue (X• : Type•) (X∘ : Type∘) (χ : ⟨ X• ⟩ → ● ⟨ X∘ ⟩) : Type where
  field
    • : ⟨ X• ⟩
    ∘ : ⟨ X∘ ⟩
    •→∘ : χ • ≡ η• ∘
open Glue public

record FRAC : Type₁ where
  field
    X• : Type•
    X∘ : Type∘
    χ : ⟨ X• ⟩ → ● ⟨ X∘ ⟩
open FRAC

fracture-and-gluing : Type ≃ FRAC
fracture-and-gluing .fst X = {!   !}
fracture-and-gluing .snd = {!   !}
