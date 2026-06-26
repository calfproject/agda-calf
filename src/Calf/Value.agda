module Calf.Value where

open import Cubical.Foundations.Prelude renaming (Type to 𝒱) public
open import Cubical.Foundations.Function public
open import Cubical.Foundations.HLevels

open import Calf.Core.Directed public

variable
  X Y Z : 𝒱

record hPreorder : 𝒱₁ where
  field
    val : 𝒱
    is-set : isSet val
    is-preorder : isPreorder val
open hPreorder public

𝒱ₛ : 𝒱₁
𝒱ₛ = hPreorder
