module Calf.Value.Unit where

open import Calf.Value
open import Cubical.Data.Unit public
open import Cubical.Foundations.Prelude

open import Cubical.Data.Unit
  renaming (Unit to ⊤; isSetUnit to isSet⊤)
  public

opaque
  isDiscrete⊤ : isDiscrete ⊤
  isDiscrete⊤ = isLocalUnit

  isPreorder⊤ : isPreorder ⊤
  isPreorder⊤ = isLocalUnit {F = Fᴾ}
