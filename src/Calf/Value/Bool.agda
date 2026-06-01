module Calf.Value.Bool where

open import Calf.Core.Directed
open import Calf.Value
open import Cubical.Data.Bool public
open import Cubical.Foundations.Prelude

Boolᵛ : 𝒱
Boolᵛ .val = Bool
Boolᵛ .is-set = isSetBool
Boolᵛ .is-preorder = IsDiscrete⊆IsPreorder
