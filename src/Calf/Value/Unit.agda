module Calf.Value.Unit where

open import Calf.Value
open import Data.Unit public
open import Cubical.Foundations.Prelude

1ᵛ : 𝒱
1ᵛ .val = ⊤
1ᵛ .isPreorder g = ((λ _ → tt) , refl) , λ _ → refl
