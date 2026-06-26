module Calf.Value where

open import Cubical.Foundations.Prelude renaming (Type to 𝒱) public
open import Cubical.Foundations.Function public
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Calf.Core.Directed public

variable
  X Y Z : 𝒱

hPreorder : 𝒱₁
hPreorder = TypeWithStr _ isPreorder

𝒱ₚ : 𝒱₁
𝒱ₚ = hPreorder
