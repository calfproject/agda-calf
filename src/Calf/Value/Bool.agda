module Calf.Value.Bool where

open import Calf.Value
open import Calf.Value.Nat
open import Cubical.Data.Bool public
open import Cubical.Foundations.Isomorphism

isDiscreteBool : isDiscrete Bool
isDiscreteBool = isLocalRetract inj prj is-retract isDiscreteℕ
  where
    inj : Bool → ℕ
    inj false = 0
    inj true = 1

    prj : ℕ → Bool
    prj zero = false
    prj (suc _) = true

    is-retract : retract inj prj
    is-retract false = refl
    is-retract true = refl

Boolₛ : 𝒱ₛ
Boolₛ = Bool , isSetBool , isDiscreteBool

Boolₚ : 𝒱ₚ
Boolₚ = ⟨ Boolₛ ⟩ₚ
