module Calf.Value.Empty where

open import Calf.Core.Directed
open import Calf.Value
open import Cubical.Data.Empty
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma

0ᵛ : 𝒱
0ᵛ .val = ⊥
0ᵛ .is-set = isProp→isSet isProp⊥
0ᵛ .is-preorder = {!   !}
