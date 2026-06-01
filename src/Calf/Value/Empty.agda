module Calf.Value.Empty where

open import Calf.Value
open import Cubical.Data.Empty
open import Cubical.Foundations.Prelude

0ᵛ : 𝒱
0ᵛ .val = ⊥
0ᵛ .is-set = isProp→isSet isProp⊥
