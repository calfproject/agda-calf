module Calf.Value.Pi where

open import Calf.Value

Πᵛ : (X : 𝒱) (Y : val X → 𝒱) → 𝒱
Πᵛ X Y .val = (x : val X) → val (Y x)
Πᵛ X Y .isPreorder = {!   !}

syntax Πᵛ X (λ x → Y) = [ x ∈ X ] →ᵛ Y

⊑-funext : {Y : val X → 𝒱}
  → {f f' : (x : val X) → val (Y x)}
  → ((x : val X) → f x ⊑[ Y x ] f' x)
  → f ⊑[ Πᵛ X Y ] f'
⊑-funext = {!   !}
