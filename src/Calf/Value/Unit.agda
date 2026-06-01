module Calf.Value.Unit where

open import Calf.Value
open import Cubical.Data.Unit public

1ᵛ : 𝒱
1ᵛ .val = Unit
1ᵛ .is-set = isSetUnit
