module Calf.Value.Sum where

open import Calf.Value
open import Data.Sum public

_+ᵛ_ : 𝒱 → 𝒱 → 𝒱
(X +ᵛ Y) .val = val X ⊎ val Y
(X +ᵛ Y) .isPreorder = {!   !}
