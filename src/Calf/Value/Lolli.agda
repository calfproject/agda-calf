open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Calf.Value.Lolli where

open import Calf.Value
open import Calf.Computation

infix 1 _⊸ᵛ_

_⊸ᵛ_ : 𝒞 → 𝒞 → 𝒱
(A ⊸ᵛ B) .val = A ⊸ B
(A ⊸ᵛ B) .is-set =
  isSetRetract
    (λ f → f .U , f .charge)
    (λ (U , charge) → record { U = U ; charge = charge })
    (λ _ → refl)
    (isSetΣSndProp
      (isSetΠ λ _ → B .U .is-set)
      (isProp⊸charge A B))
