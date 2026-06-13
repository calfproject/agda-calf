open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure

module Calf.Computation.DGlue where

open import Calf.Core.Cost
open import Calf.Core.Directed
open import Calf.Computation
open import Calf.Value
import Calf.Value.Closed as ●ᵛ
import Calf.Value.Open as ◯ᵛ
open import Calf.Value.Glue
open import Calf.Computation.Power
open import Calf.Computation.Open as ◯ᶜ
open import Calf.Computation.Closed as ●ᶜ
open import Calf.Computation.Glue

record DGlue (X• : Type•) (X◦ : Type◦) (χ• : ⟨ X• ⟩ → ● ⟨ X◦ ⟩) : Type where
  field
    • : ⟨ X• ⟩
    ◦ : ⟨ X◦ ⟩
    •→◦ : χ• • ⊑ η• ◦
open DGlue public

DGlueᵛ : (X• : 𝒱•) (X◦ : 𝒱◦) (χ• : val (X• .fst) → val (●ᵛ (X◦ .fst))) → 𝒱
DGlueᵛ X• X◦ χ• .val = DGlue (𝒱•→Type• X•) (𝒱◦→Type◦ X◦) χ•
DGlueᵛ X• X◦ χ• .is-set = {!   !}
DGlueᵛ X• X◦ χ• .is-preorder = {!   !}

DGlueᶜ : (A• : 𝒞•) (A◦ : 𝒞◦) (α• : A• .fst ⊸ ●ᶜ (A◦ .fst)) → 𝒞
DGlueᶜ A• A◦ α• .U = DGlueᵛ (U• A•) (U◦ A◦) (α• .U)
DGlueᶜ A• A◦ α• .charge c a .• = A• .fst .charge c (a .•)
DGlueᶜ A• A◦ α• .charge c a .◦ = A◦ .fst .charge c (a .◦)
DGlueᶜ A• A◦ α• .charge c a .•→◦ =
  let open ⊑ᵛ-Reasoning (U (●ᶜ (A◦ .fst))) in
  begin
    α• .U (A• .fst .charge c (a .•))
  ≡ᵛ⟨ α• .charge c (a .•) ⟩
    ●ᶜ (A◦ .fst) .charge c (α• .U (a .•))
  ⊑ᵛ⟨ ⊑ᵛ-mono (●ᶜ (A◦ .fst) .charge c) (a .•→◦) ⟩
    η• (A◦ .fst .charge c (a .◦))
  ∎ᵛ
DGlueᶜ A• A◦ α• .charge/0 {a} i .• = A• .fst .charge/0 {a .•} i
DGlueᶜ A• A◦ α• .charge/0 {a} i .◦ = A◦ .fst .charge/0 {a .◦} i
DGlueᶜ A• A◦ α• .charge/0 {a} i .•→◦ = {! ⊑ᵛ-isProp  !}
DGlueᶜ A• A◦ α• .charge/+ = {! same   !}

DGlueᶜ' : (A-⊤ A-abs : 𝒞) → (A-⊤ ⊸ A-abs) → 𝒞
DGlueᶜ' A-⊤ A-abs α =
  DGlueᶜ
    (●ᶜ A-⊤ , ●ᶜ.η-isEquiv {X = cmp A-⊤})
    (◯ᶜ A-abs , ◯ᶜ.η-isEquiv {X = cmp A-abs})
    (●ᶜ.map (α ⨾ᶜ η◦ᶜ {A = A-abs}))

squareᶜ'≤ : ∀ {A-⊤ A-abs α B-⊤ B-abs β} (f-⊤ : A-⊤ ⊸ B-⊤) (f-abs : A-abs ⊸ B-abs)
  → ((a-⊤ : cmp A-⊤) → U β (U f-⊤ a-⊤) ⊑[ U B-abs ] U f-abs (U α a-⊤))
  → DGlueᶜ' A-⊤ A-abs α ⊸ DGlueᶜ' B-⊤ B-abs β
squareᶜ'≤ {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} f-⊤ f-abs f-coherence .U a .• = ●ᶜ.map f-⊤ .U (a .•)
squareᶜ'≤ {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} f-⊤ f-abs f-coherence .U a .◦ = ◯ᶜ.map f-abs .U (a .◦)
squareᶜ'≤ {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} f-⊤ f-abs f-coherence .U a .•→◦ = {! a .•→◦  !}
squareᶜ'≤ {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} f-⊤ f-abs f-coherence .charge = {!   !}

-- squareᶜ'≤ {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} f-⊤ f-abs f-coherence .U a with a .•
-- ... | η• a-⊤ =
--       Glueᶜ' B-⊤ B-abs β .seal
--         (record { • = η• (f-⊤ .U a-⊤) ; ◦ = η◦ (β .U (f-⊤ .U a-⊤)) ; •→◦ = {! refl !} })
--         (λ abs → record { • = ∗ abs ; ◦ = η◦ (f-abs .U (a .◦ abs)) ; •→◦ = {! sym (law _ abs) !} })
--         (λ abs → record
--           { path = λ 𝕚 → record
--             { • = ≡⇒⊑ (●-path-to-star abs (η• (f-⊤ .U a-⊤))) .path 𝕚
--             ; ◦ = η◦ (f-coherence a-⊤ .path 𝕚)
--             ; •→◦ = {!   !}
--             }
--           ; path₀ = λ i → record
--             { • = η• (f-⊤ .U a-⊤)
--             ; ◦ = η◦ (f-coherence a-⊤ .path₀ i)
--             ; •→◦ = {!   !}
--             }
--           ; path₁ = λ i → record
--             { • = law (f-⊤ .U a-⊤) abs i
--             ; ◦ = η◦ ((f-coherence a-⊤ .path₁ ∙ cong (f-abs .U) (lemma abs)) i)
--             ; •→◦ = {!   !}
--             }
--           })
--         where
--           lemma : ∀ abs → α .U a-⊤ ≡ a .◦ abs  -- really, need to merge with a .•→◦
--           lemma = {!   !}
-- ... | ∗ abs = record { • = ∗ abs ; ◦ = η◦ (f-abs .U (a .◦ abs)) ; •→◦ = {! sym (law _ abs) !} }
-- ... | law a-⊤ abs i =
--         Glueᶜ' B-⊤ B-abs β .seal/abs
--           {record { • = η• (f-⊤ .U a-⊤) ; ◦ = η◦ (β .U (f-⊤ .U a-⊤)) ; •→◦ = {! refl !} }}
--           {λ abs → record { • = ∗ abs ; ◦ = η◦ (f-abs .U (a .◦ abs)) ; •→◦ = {! sym (law _ abs) !} }}
--           {{! ^ same proof as above  !}}
--           abs
--           i
-- squareᶜ'≤ {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} f-⊤ f-abs f-coherence .charge = {!   !}
