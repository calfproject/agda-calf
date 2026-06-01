module Calf.Computation.Unit where

open import Calf.Computation
open import Calf.Value.Unit public
open import Cubical.Foundations.Prelude using (refl)

1ᶜ : 𝒞
1ᶜ .U = 1ᵛ
1ᶜ .charge _ _ = tt
1ᶜ .charge/0 = refl
1ᶜ .charge/+ = refl
