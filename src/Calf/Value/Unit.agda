module Calf.Value.Unit where

open import Calf.Value

open import Cubical.Data.Unit public
  renaming (Unit to ⊤; isSetUnit to isSet⊤)

opaque
  isDiscrete⊤ : isDiscrete ⊤
  isDiscrete⊤ = isLocalUnit

  isPreorder⊤ : isPreorder ⊤
  isPreorder⊤ = isLocalUnit {F = Fᴾ}
