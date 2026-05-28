module Calf.Value.Product where

open import Calf.Value
open import Cubical.Data.Sigma public
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

infixr 2 _×ᵛ_
_×ᵛ_ : 𝒱 → 𝒱 → 𝒱
(X ×ᵛ Y) .fst = val X × val Y
(X ×ᵛ Y) .snd = isSet× (X .snd) (Y .snd)
