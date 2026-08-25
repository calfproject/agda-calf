open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure

module Calf.Value.Seal where

open import Calf.Core.Cost
open import Calf.Core.Directed
open import Calf.Computation
open import Calf.Value
open import Calf.Value.Product
open import Calf.Value.Closed
open import Calf.Value.Open
open import Calf.Value.Glue

Glueᵈ : (X• X◦ : 𝒱) (χ• : X• → ● X◦) → 𝒱
Glueᵈ X• X◦ χ• = Σ[ (x• , x◦) ∈ X• × X◦ ] χ• x• ⊑ η• x◦

opaque
  isPreorderGlueᵈ : ∀ {X• X◦ χ•}
    → isPreorder X•
    → isPreorder X◦
    → isPreorder (Glueᵈ X• X◦ χ•)
  isPreorderGlueᵈ isPreorderX• isPreorderX◦ =
    isLocalComma isPreorderX• isPreorderX◦ (isPreorder● isPreorderX◦)

open 𝒱-FRACTURE

𝒱-Glueᵈ : 𝒱-FRACTURE → 𝒱
𝒱-Glueᵈ F = Glueᵈ ⟨ F .X• ⟩ ⟨ F .X◦ ⟩ (F .χ•)

Seal : 𝒱 → 𝒱
Seal = 𝒱-Glueᵈ ∘ 𝒱-Fracture

opaque
  isPreorderSeal : isPreorder X → isPreorder (Seal X)
  isPreorderSeal {X} isPreorderX =
    isPreorderGlueᵈ {● X} {◯ X} (isPreorder● isPreorderX) (isPreorder◯ isPreorderX)

-- squareᶜ'≤ : ∀ {A-⊤ A-abs α B-⊤ B-abs β} (f-⊤ : A-⊤ ⊸ B-⊤) (f-abs : A-abs ⊸ B-abs)
--   → ((a-⊤ : cmp A-⊤) → U β (U f-⊤ a-⊤) ⊑[ U B-abs ] U f-abs (U α a-⊤))
--   → DGlueᶜ' A-⊤ A-abs α ⊸ DGlueᶜ' B-⊤ B-abs β
-- squareᶜ'≤ {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} f-⊤ f-abs f-coherence .U a .• = ●ᶜ.map f-⊤ .U (a .•)
-- squareᶜ'≤ {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} f-⊤ f-abs f-coherence .U a .◦ = ◯ᶜ.map f-abs .U (a .◦)
-- squareᶜ'≤ {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} f-⊤ f-abs f-coherence .U a .•→◦ = {! a .•→◦  !}
-- squareᶜ'≤ {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} f-⊤ f-abs f-coherence .charge = {!   !}

-- -- squareᶜ'≤ {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} f-⊤ f-abs f-coherence .U a with a .•
-- -- ... | η• a-⊤ =
-- --       Glueᶜ' B-⊤ B-abs β .seal
-- --         (record { • = η• (f-⊤ .U a-⊤) ; ◦ = η◦ (β .U (f-⊤ .U a-⊤)) ; •→◦ = {! refl !} })
-- --         (λ abs → record { • = ∗ abs ; ◦ = η◦ (f-abs .U (a .◦ abs)) ; •→◦ = {! sym (law _ abs) !} })
-- --         (λ abs → record
-- --           { path = λ 𝕚 → record
-- --             { • = ≡⇒⊑ (●-path-to-star abs (η• (f-⊤ .U a-⊤))) .path 𝕚
-- --             ; ◦ = η◦ (f-coherence a-⊤ .path 𝕚)
-- --             ; •→◦ = {!   !}
-- --             }
-- --           ; path₀ = λ i → record
-- --             { • = η• (f-⊤ .U a-⊤)
-- --             ; ◦ = η◦ (f-coherence a-⊤ .path₀ i)
-- --             ; •→◦ = {!   !}
-- --             }
-- --           ; path₁ = λ i → record
-- --             { • = law (f-⊤ .U a-⊤) abs i
-- --             ; ◦ = η◦ ((f-coherence a-⊤ .path₁ ∙ cong (f-abs .U) (lemma abs)) i)
-- --             ; •→◦ = {!   !}
-- --             }
-- --           })
-- --         where
-- --           lemma : ∀ abs → α .U a-⊤ ≡ a .◦ abs  -- really, need to merge with a .•→◦
-- --           lemma = {!   !}
-- -- ... | ∗ abs = record { • = ∗ abs ; ◦ = η◦ (f-abs .U (a .◦ abs)) ; •→◦ = {! sym (law _ abs) !} }
-- -- ... | law a-⊤ abs i =
-- --         Glueᶜ' B-⊤ B-abs β .seal/abs
-- --           {record { • = η• (f-⊤ .U a-⊤) ; ◦ = η◦ (β .U (f-⊤ .U a-⊤)) ; •→◦ = {! refl !} }}
-- --           {λ abs → record { • = ∗ abs ; ◦ = η◦ (f-abs .U (a .◦ abs)) ; •→◦ = {! sym (law _ abs) !} }}
-- --           {{! ^ same proof as above  !}}
-- --           abs
-- --           i
-- -- squareᶜ'≤ {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} f-⊤ f-abs f-coherence .charge = {!   !}
