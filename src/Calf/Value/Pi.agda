module Calf.Value.Pi where

open import Cubical.Foundations.HLevels using (isSetΠ) public
open import Calf.Value

opaque
  isDiscreteΠ : {Y : X → 𝒱} → ((x : X) → isDiscrete (Y x)) → isDiscrete ((x : X) → Y x)
  isDiscreteΠ = isLocalΠ

  isPreorderΠ : {Y : X → 𝒱} → ((x : X) → isPreorder (Y x)) → isPreorder ((x : X) → Y x)
  isPreorderΠ = isLocalΠ
