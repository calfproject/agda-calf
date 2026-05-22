module Calf.Value.Sigma where

open import Calf.Value
open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma public
open import Function


Σᵛ : (X : 𝒱) ⦃ _ : IsDiscrete X ⦄ (Y : val X → 𝒱) → 𝒱
Σᵛ X Y .val = Σ (val X) (val ∘ Y)
Σᵛ X ⦃ X-discrete ⦄ Y .isPreorder .ortho g .fst .fst 𝕚₂ =
  let X-ortho-𝕀∨𝕀 = mylemma {X = X} X-discrete .ortho (fst ∘ g) in
  let x = X-ortho-𝕀∨𝕀 .fst .fst _ in
  x , Y x .isPreorder .ortho (λ 𝕚∨𝕚 → subst (val ∘ Y) ({!   !} ∙ cong ((_$ _) ∘ fst) (X-ortho-𝕀∨𝕀 .snd (const x , X-ortho-𝕀∨𝕀 .fst .snd))) (snd (g 𝕚∨𝕚))) .fst .fst 𝕚₂
Σᵛ X Y .isPreorder .ortho g .fst .snd = {!   !}
Σᵛ X Y .isPreorder .ortho g .snd = {!   !}

syntax Σᵛ X (λ x → A) = [ x ∈ X ] ×ᵛ A
