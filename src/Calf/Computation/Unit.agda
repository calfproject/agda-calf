module Calf.Computation.Unit where

open import Calf.Value
open import Calf.Value.Unit public
open import Calf.Computation

1ᶜ : 𝒞
1ᶜ .U = ⊤
1ᶜ .is-preorder = isPreorder⊤
1ᶜ .charge _ _ = tt
1ᶜ .charge-0 = refl
1ᶜ .charge-+ = refl
