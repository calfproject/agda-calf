module Calf.Value.Pi where

open import Calf.Core.Directed
open import Calf.Value
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

Πᵛ : (X : 𝒱) (Y : val X → 𝒱) → 𝒱
Πᵛ X Y .fst = (x : val X) → val (Y x)
Πᵛ X Y .snd = isSetΠ (λ x → Y x .snd)

syntax Πᵛ X (λ x → Y) = [ x ∈ X ] →ᵛ Y
