module Calf.Value.Empty where

open import Calf.Value
open import Data.Empty public

0ᵛ : 𝒱
0ᵛ .val = ⊥
0ᵛ .isPreorder = {!   !}
