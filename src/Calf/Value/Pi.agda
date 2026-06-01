module Calf.Value.Pi where

open import Calf.Value
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

Πᵛ : (X : 𝒱) (Y : val X → 𝒱) → 𝒱
Πᵛ X Y .val = (x : val X) → val (Y x)
Πᵛ X Y .is-set = isSetΠ (λ x → Y x .is-set)

syntax Πᵛ X (λ x → Y) = [ x ∈ X ] →ᵛ Y
