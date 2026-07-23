module Calf.Value.Glue.Base where

open import Calf.Value
open import Calf.Value.Open as ◯
open import Calf.Value.Closed as ●

record Glue (X• : 𝒱•) (X◦ : 𝒱◦) (χ• : ⟨ X• ⟩ → ● ⟨ X◦ ⟩) : 𝒱 where
  field
    • : ⟨ X• ⟩
    ◦ : ⟨ X◦ ⟩
    •→◦ : χ• • ≡ η• ◦
open Glue public

record 𝒱-FRAC : 𝒱₁ where
  field
    X• : 𝒱•
    X◦ : 𝒱◦
    χ• : ⟨ X• ⟩ → ● ⟨ X◦ ⟩
open 𝒱-FRAC

fromFRAC : 𝒱-FRAC → 𝒱
fromFRAC F = Glue (F .X•) (F .X◦) (F .χ•)

toFRAC : 𝒱 → 𝒱-FRAC
toFRAC X .X• = ● X , ●.η-isEquiv
toFRAC X .X◦ = ◯ X , ◯.η-isEquiv
toFRAC X .χ• = ●.map η◦

record 𝒱-Square (X Y : 𝒱-FRAC) : 𝒱 where
  field
    f• : ⟨ X .X• ⟩ → ⟨ Y .X• ⟩
    f◦ : ⟨ X .X◦ ⟩ → ⟨ Y .X◦ ⟩
    f-coh : (x• : ⟨ X .X• ⟩) → Y .χ• (f• x•) ≡ ●.map f◦ (X .χ• x•)

square
  : ∀ {X• X◦ χ Y• Y◦ ψ}
  → (f• : X• .fst → Y• .fst)
  → (f◦ : X◦ .fst → Y◦ .fst)
  → ((x• : X• .fst) → ψ (f• x•) ≡ ●.map f◦ (χ x•))
  → Glue X• X◦ χ → Glue Y• Y◦ ψ
square f• f◦ f-coh q .• = f• (q .•)
square f• f◦ f-coh q .◦ = f◦ (q .◦)
square f• f◦ f-coh q .•→◦ = f-coh (q .•) ∙ cong (●.map f◦) (q .•→◦)
