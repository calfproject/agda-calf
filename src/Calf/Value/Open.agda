open import Cubical.Foundations.Prelude

module Calf.Value.Open (φ : Type) (φ-isProp : isProp φ) where

open import Calf.Value
open import Calf.Value.Function
open import Calf.Phase.Open φ φ-isProp renaming (◯-η-isEquiv to ◯ᵛ-ηᵛ-isEquiv) public
open import Cubical.Foundations.Equiv

◯ᵛ : 𝒱 → 𝒱
◯ᵛ = fromProp φ-isProp →ᵛ_

η◦ᵛ : val X → val (◯ᵛ X)
η◦ᵛ = η◦

𝒱◦ : Type₁
𝒱◦ = Σ[ X ∈ 𝒱 ] isEquiv (η◦ {val X})

𝒱◦→Type◦ : 𝒱◦ → Type◦
𝒱◦→Type◦ X◦ .fst = val (X◦ .fst)
𝒱◦→Type◦ X◦ .snd = X◦ .snd
