module Calf.Value.Pi where

open import Calf.Value
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

Πᵛ : (X : 𝒱) (Y : val X → 𝒱) → 𝒱
Πᵛ X Y .val = (x : val X) → val (Y x)
Πᵛ X Y .isPreorder g .fst .fst 𝕚₂ x = Y x .isPreorder (flip g x) .fst .fst 𝕚₂
Πᵛ X Y .isPreorder g .fst .snd i 𝕚∨𝕚 x = (Y x .isPreorder (flip g x) .fst .snd) i 𝕚∨𝕚
Πᵛ X Y .isPreorder g .snd f i .fst 𝕚₂ x = 
  Y x .isPreorder (flip g x) .snd
    ((λ 𝕚₂ → f .fst 𝕚₂ x) , λ j 𝕚∨𝕚 → f .snd j 𝕚∨𝕚 x)
    i .fst 𝕚₂
Πᵛ X Y .isPreorder g .snd f i .snd j 𝕚∨𝕚 x = 
  Y x .isPreorder (flip g x) .snd
    ((λ 𝕚₂ → f .fst 𝕚₂ x) , λ j 𝕚∨𝕚 → f .snd j 𝕚∨𝕚 x) 
    i .snd j 𝕚∨𝕚
syntax Πᵛ X (λ x → Y) = [ x ∈ X ] →ᵛ Y

⊑-funext : {Y : val X → 𝒱}
  → {f f' : (x : val X) → val (Y x)}
  → ((x : val X) → f x ⊑[ Y x ] f' x)
  → f ⊑[ Πᵛ X Y ] f'
⊑-funext pointwise ._⊑_.path 𝕚 x = pointwise x ._⊑_.path 𝕚
⊑-funext pointwise ._⊑_.path₀ = funExt λ x → pointwise x ._⊑_.path₀
⊑-funext pointwise ._⊑_.path₁ = funExt λ x → pointwise x ._⊑_.path₁
