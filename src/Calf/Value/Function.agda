module Calf.Value.Function where

open import Calf.Value
open import Calf.Value.Pi
open import Function

_→ᵛ_ : 𝒱 → 𝒱 → 𝒱
X →ᵛ Y = Πᵛ X (const Y)
