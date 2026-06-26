module Calf.Value.Pi where

open import Cubical.Foundations.HLevels using (isSetΠ) public
open import Calf.Value

isPreorderΠ : {Y : X → 𝒱} → ((x : X) → isPreorder (Y x)) → isPreorder ((x : X) → Y x)
isPreorderΠ = {!   !}
