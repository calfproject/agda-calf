open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Calf.Core.Monad where

open import Calf.Value
open import Calf.Core.Cost public
open import Calf.Value.Product

opaque
  M : 𝒱 → 𝒱
  M X = ℂ ×ᵛ X

  retᴹ : X → M X
  retᴹ x = 0ℂ , x
