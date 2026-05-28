module Calf.Value.Empty where

open import Calf.Value
open import Cubical.Data.Empty
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma

0ᵛ : 𝒱
0ᵛ .fst = ⊥
0ᵛ .snd = isProp→isSet isProp⊥
