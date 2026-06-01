module Calf.Value.Sigma where

open import Calf.Value
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma public
open import Function


Σᵛ : (X : 𝒱) ⦃ _ : isDiscreteᵛ X ⦄ (Y : val X → 𝒱) → 𝒱
Σᵛ X Y .val = Σ (val X) (val ∘ Y)
Σᵛ X Y .is-set = isSetΣ (X .is-set) (λ x → Y x .is-set)
Σᵛ X Y .is-preorder = ?

syntax Σᵛ X (λ x → A) = [ x ∈ X ] ×ᵛ A
