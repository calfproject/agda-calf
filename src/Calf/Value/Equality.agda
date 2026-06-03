module Calf.Value.Equality where

open import Calf.Value
open import Cubical.Foundations.Prelude

_≡ᵛ_ : val X → val X → 𝒱
(x ≡ᵛ x') .val = x ≡ x'
_≡ᵛ_ {X} x x' .is-set = isProp→isSet (X .is-set x x')

≡ᵛ-syntax : val X → val X → 𝒱
≡ᵛ-syntax {X} = _≡ᵛ_ {X}

syntax ≡ᵛ-syntax {X} x x' = x ≡ᵛ[ X ] x'
