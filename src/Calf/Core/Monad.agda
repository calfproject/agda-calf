module Calf.Core.Monad where

open import Calf.Value
open import Calf.Core.Cost public
open import Calf.Value.Product public

opaque
  M : 𝒱 → 𝒱
  M X = ℂ ×ᵛ X

  M-ret : val X → val (M X)
  M-ret x = (0ℂ , x)
