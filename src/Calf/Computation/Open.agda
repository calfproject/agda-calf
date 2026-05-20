open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Calf.Computation.Open (φ : Type) (φ-isProp : isProp φ) where

open import Calf.Value
open import Calf.Value.Open φ φ-isProp
open import Calf.Computation
open import Calf.Computation.Power
open import Cubical.Foundations.Equiv

◯ᶜ : 𝒞 → 𝒞
◯ᶜ = fromProp φ-isProp ⇀_

η∘ᶜ : A ⊸ ◯ᶜ A
η∘ᶜ {A} .U = η∘ᵛ {A .U}
η∘ᶜ .charge _ _ = refl

𝒞∘ : Type₁
𝒞∘ = Σ[ A ∈ 𝒞 ] isEquiv (η∘ᶜ {A} .U)

U∘ : 𝒞∘ → 𝒱∘
U∘ A∘ .fst = A∘ .fst .U
U∘ A∘ .snd = A∘ .snd
