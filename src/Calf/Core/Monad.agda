open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma

module Calf.Core.Monad where

open import Calf.Value
open import Calf.Core.Cost public

opaque
  M : 𝒱 → 𝒱
  M X = ℂ × X

  retᴹ : X → M X
  retᴹ x = 0ℂ , x
