module Calf.Value.Sigma where

open import Calf.Value
open import Data.Product public
open import Function

Σᵛ : (X : 𝒱) ⦃ _ : IsDiscrete X ⦄ (Y : val X → 𝒱) → 𝒱
Σᵛ X Y .val = Σ (val X) (val ∘ Y)
Σᵛ X Y .isPreorder = {!   !}

syntax Σᵛ X (λ x → A) = [ x ∈ X ] ×ᵛ A
