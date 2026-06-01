module Calf.Value.Bool where

open import Calf.Value
open import Cubical.Data.Bool public

Boolᵛ : 𝒱
Boolᵛ .val = Bool
Boolᵛ .is-set = isSetBool
