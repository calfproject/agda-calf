open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Foundations.Equiv

module Calf.Computation.Open (φ : Type) (φ-isProp : isProp φ) where

open import Calf.Value
open import Calf.Value.Open φ φ-isProp using (η∘ᵛ)
open import Calf.Value.Open φ φ-isProp hiding (◯ᵛ; η∘ᵛ) renaming (◯ᵛ-ηᵛ-isEquiv to ◯ᶜ-ηᶜ-isEquiv) public
open import Calf.Computation
open import Calf.Computation.Power

◯ᶜ : 𝒞 → 𝒞
◯ᶜ = fromProp φ-isProp ⇀_

η∘ᶜ : A ⊸ ◯ᶜ A
η∘ᶜ {A} .U = η∘ᵛ {A .U}
η∘ᶜ .charge _ _ = refl

𝒞∘ : Type₁
𝒞∘ = Σ[ A ∈ 𝒞 ] isEquiv (η∘ᶜ {A} .U)

𝒞∘-path : {A∘ B∘ : 𝒞∘} → A∘ .fst ≡ B∘ .fst → A∘ ≡ B∘
𝒞∘-path p = Σ≡Prop (λ A → isPropIsEquiv (η∘ᶜ {A} .U)) p

U∘ : 𝒞∘ → 𝒱∘
U∘ A∘ .fst = A∘ .fst .U
U∘ A∘ .snd = A∘ .snd
