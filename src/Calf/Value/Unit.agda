module Calf.Value.Unit where

open import Calf.Core.Directed
open import Calf.Value
open import Cubical.Data.Unit public
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv.PathSplit

1ᵛ : 𝒱
1ᵛ .fst = Unit
1ᵛ .snd = isSetUnit

instance
  open isDiscrete
  open isPathSplitEquiv

  1ᵛ-isDiscrete : isDiscrete (val 1ᵛ)
  1ᵛ-isDiscrete .is-discrete _ .sec = {!   !}
  1ᵛ-isDiscrete .is-discrete _ .secCong = {!   !}
