module Calf.Value.Pi where

open import Calf.Core.Directed
open import Calf.Value
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

Πᵛ : (X : 𝒱) (Y : val X → 𝒱) → 𝒱
Πᵛ X Y .val = (x : val X) → val (Y x)
Πᵛ X Y .is-set = isSetΠ (λ x → Y x .is-set)
Πᵛ X Y .is-preorder α .sec .fst f t x = Y x .is-preorder α .sec .fst (λ s → f s x) t
Πᵛ X Y .is-preorder α .sec .snd f = funExt λ s → funExt λ x → cong (_$ s) (Y x .is-preorder α .sec .snd (λ s → f s x))
Πᵛ X Y .is-preorder α .secCong = {!   !}

syntax Πᵛ X (λ x → Y) = [ x ∈ X ] →ᵛ Y
