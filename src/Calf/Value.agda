module Calf.Value where

open import Cubical.Foundations.Prelude renaming (Type to 𝒱) public
open import Cubical.Foundations.Equiv public
open import Cubical.Foundations.Function public hiding (idfun)
open import Cubical.Foundations.HLevels public
open import Cubical.Foundations.Isomorphism public
open import Cubical.Foundations.Structure public

variable
  X Y Z : 𝒱

id : X → X
id x = x

𝒱ₛ : 𝒱₁
𝒱ₛ = hSet _
