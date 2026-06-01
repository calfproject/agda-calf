module Calf.Value.Unit where

open import Calf.Core.Directed
open import Calf.Value
open import Cubical.Data.Unit public
open import Cubical.Foundations.Prelude

instance
  1ᵛ-isDiscrete : isDiscrete Unit
  1ᵛ-isDiscrete .is-discrete _ .sec = (λ _ _ → tt) , (λ _ → refl)
  1ᵛ-isDiscrete .is-discrete _ .secCong _ _ = (λ _ → refl) , (λ _ → refl)

1ᵛ : 𝒱
1ᵛ .val = Unit
1ᵛ .is-set = isSetUnit
1ᵛ .is-preorder = isDiscrete→isPreorder
