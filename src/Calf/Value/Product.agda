module Calf.Value.Product where

open import Calf.Value
open import Data.Product public

infixr 2 _×ᵛ_
_×ᵛ_ : 𝒱 → 𝒱 → 𝒱
(X ×ᵛ Y) .val = val X × val Y
(X ×ᵛ Y) .isPreorder = {!   !}
