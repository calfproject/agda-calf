module Calf.Value.Bool where

open import Calf.Value
open import Cubical.Data.Bool public
open import Cubical.Foundations.Prelude

Boolᵛ : 𝒱
Boolᵛ .val = Bool
Boolᵛ .isPreorder = IsDiscrete'⊆IsPreorder
