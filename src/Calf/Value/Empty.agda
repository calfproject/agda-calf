module Calf.Value.Empty where

open import Calf.Value

open import Cubical.Data.Empty public
  hiding (rec)

isSet⊥ : isSet ⊥
isSet⊥ = isProp→isSet isProp⊥
