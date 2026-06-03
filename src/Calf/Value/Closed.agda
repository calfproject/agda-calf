open import Cubical.Foundations.Prelude

module Calf.Value.Closed where

open import Calf.Core.Abstract
open import Calf.Phase.Closed (ABS .fst) (ABS .snd) public
open import Calf.Value
open import Cubical.Data.Sigma
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function


●ᵛ : 𝒱 → 𝒱
●ᵛ X .val = ● (X .val)
●ᵛ X .is-set = ●-preserves-isSet (X .is-set)

η•ᵛ : val X → val (●ᵛ X)
η•ᵛ = η•

𝒱• : Type₁
𝒱• = Σ[ X ∈ 𝒱 ] isEquiv (η•ᵛ {X})

𝒱•→Type• : 𝒱• → Type•
𝒱•→Type• X• .fst = val (X• .fst)
𝒱•→Type• X• .snd = X• .snd
