open import Cubical.Foundations.Prelude

module Calf.Value.Closed where

open import Calf.Core.Abstract
open import Calf.Value
open import Calf.Phase.Closed (ABS .fst) (ABS .snd) as ● hiding (●-η-isEquiv) public
open import Cubical.Data.Sigma
open import Cubical.Foundations.Equiv


●ᵛ : 𝒱 → 𝒱
●ᵛ X .val = ● (X .val)
●ᵛ X .is-set = isSet● (X .is-set)

η•ᵛ : val X → val (●ᵛ X)
η•ᵛ = η•

𝒱• : Type₁
𝒱• = Σ[ X ∈ 𝒱 ] isEquiv (η•ᵛ {X})

𝒱•→Type• : 𝒱• → Type•
𝒱•→Type• X• .fst = val (X• .fst)
𝒱•→Type• X• .snd = X• .snd

●ᵛ-η•ᵛ-isEquiv : isEquiv (η•ᵛ {●ᵛ X})
●ᵛ-η•ᵛ-isEquiv = ●.●-η-isEquiv
