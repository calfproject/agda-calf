open import Cubical.Foundations.Prelude

module Calf.Value.Open where

open import Calf.Core.Abstract
open import Calf.Phase.Open (ABS .fst) (ABS .snd) as ◯ public
open import Calf.Value
open import Calf.Value.Function
open import Cubical.Foundations.Equiv

◯ᵛ : 𝒱 → 𝒱
◯ᵛ = fromProp ABS →ᵛ_

η◦ᵛ : val X → val (◯ᵛ X)
η◦ᵛ = η◦

𝒱◦ : Type₁
𝒱◦ = Σ[ X ∈ 𝒱 ] isEquiv (η◦ {val X})

𝒱◦→Type◦ : 𝒱◦ → Type◦
𝒱◦→Type◦ X◦ .fst = val (X◦ .fst)
𝒱◦→Type◦ X◦ .snd = X◦ .snd
