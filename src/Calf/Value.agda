module Calf.Value where

open import Cubical.Foundations.Prelude renaming (Type to 𝒱) public

open import Calf.Core.Directed public
open import Cubical.Foundations.Equiv public
open import Cubical.Foundations.Function public hiding (idfun)
open import Cubical.Foundations.HLevels public
open import Cubical.Foundations.Isomorphism public
open import Cubical.Foundations.Structure public

variable
  X Y Z : 𝒱

id : X → X
id x = x

𝒱₌ : 𝒱₁
𝒱₌ = TypeWithStr _ λ X → isSet X × isDiscrete X
  where open import Cubical.Data.Sigma

variable
  X₌ Y₌ Z₌ : 𝒱₌

𝒱ₚ : 𝒱₁
𝒱ₚ = TypeWithStr _ isPreorder

⟨_⟩ₚ : 𝒱₌ → 𝒱ₚ
⟨ X ⟩ₚ = ⟨ X ⟩ , isSet∧isDiscrete→isPreorder (str X .fst) (str X .snd)
