module Calf.Value.Sum where

open import Calf.Value
open import Cubical.Data.Sum renaming (inl to inj₁; inr to inj₂) public

_+ᵛ_ : 𝒱 → 𝒱 → 𝒱
(X +ᵛ Y) .val = val X ⊎ val Y
(X +ᵛ Y) .is-set = isSet⊎ (X .is-set) (Y .is-set)
