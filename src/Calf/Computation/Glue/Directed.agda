module Calf.Computation.Glue.Directed where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence using (ua; ua→; ua-gluePath)
open import Cubical.Functions.Embedding

open import Calf.Core.Directed
open import Calf.Value
open import Calf.Computation
open import Calf.Computation.Open as ◯ᶜ
open import Calf.Computation.Closed as ●ᶜ
open import Calf.Computation.Glue

opaque
  unfolding Glueᶜ'

  squareᶜ'≤ : ∀ {A-⊤ A-abs α B-⊤ B-abs β} (f-⊤ : A-⊤ ⊸ B-⊤) (f-abs : A-abs ⊸ B-abs)
    → ((a-⊤ : cmp A-⊤) → U β (U f-⊤ a-⊤) ⊑[ U B-abs ] U f-abs (U α a-⊤))
    → Glueᶜ' A-⊤ A-abs α ⊸ Glueᶜ' B-⊤ B-abs β
  squareᶜ'≤ {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} f-⊤ f-abs f-coherence .U a .• = ●ᶜ.map f-⊤ .U (a .•)
  squareᶜ'≤ {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} f-⊤ f-abs f-coherence .U a .◦ = ◯ᶜ.map f-abs .U (a .◦)
  squareᶜ'≤ {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} f-⊤ f-abs f-coherence .U a .•→◦ = {! a .•→◦  !}
  squareᶜ'≤ {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} f-⊤ f-abs f-coherence .charge = {!   !}
  squareᶜ'≤ {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} f-⊤ f-abs f-coherence .seal = {!   !}

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
  -- squareᶜ'≤ {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} f-⊤ f-abs f-coherence .seal = {!   !}
