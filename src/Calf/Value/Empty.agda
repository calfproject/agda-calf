module Calf.Value.Empty where

open import Calf.Value
open import Cubical.Data.Empty hiding (rec) public

isSet⊥ : isSet ⊥
isSet⊥ = isProp→isSet isProp⊥
