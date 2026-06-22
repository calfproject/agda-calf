module Calf.Computation.Unit where

open import Calf.Computation
open import Cubical.Data.Unit public
open import Cubical.Foundations.Prelude using (refl)

1ᶜ : 𝒞
1ᶜ .U = Unit
1ᶜ .is-set = isSetUnit
1ᶜ .charge _ _ = tt
1ᶜ .charge/0 = refl
1ᶜ .charge/+ = refl
