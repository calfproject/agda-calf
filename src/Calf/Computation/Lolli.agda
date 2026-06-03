module Calf.Computation.Lolli where

open import Calf.Value
open import Calf.Computation
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

_⊸ᶜ_ : 𝒞 → 𝒞 → 𝒞
(A ⊸ᶜ B) .U .val = A ⊸ B
(A ⊸ᶜ B) .U .is-set = {!   !}
(A ⊸ᶜ B) .charge c f .U a = B .charge c (f .U a)
(A ⊸ᶜ B) .charge c f .charge c' a =
  cong (B .charge c) (f .charge c' a)
  ∙ cong ((_$ f .U a) ∘ U) (CHARGE-comm {B} c' c)
(A ⊸ᶜ B) .charge/0 = ⊸-path refl refl (funExt λ a → B .charge/0)
(A ⊸ᶜ B) .charge/+ = ⊸-path refl refl (funExt λ a → B .charge/+)
