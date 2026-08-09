module Calf.Computation.Abstraction.Properties where

open import Cubical.Foundations.Univalence using (ua; ua→)

open import Calf.Core.Abstract
open import Calf.Value
import Calf.Value.Open as ◯
import Calf.Value.Closed as ●
open import Calf.Computation
open import Calf.Computation.Open as ◯ᶜ
open import Calf.Computation.Closed as ●ᶜ
open import Calf.Computation.Glue as Glueᶜ hiding (squareᶜ)
open 𝒞-FRACTURE

open import Calf.Computation.Abstraction.Base

●ᶜ-Abstractionᶜ : ∀ {A-⊤ A-abs α} → ●ᶜ (Abstractionᶜ A-⊤ A-abs α) ≡ ●ᶜ A-⊤
●ᶜ-Abstractionᶜ {A-⊤} {A-abs} {α} =
  cong ⟨_⟩ᶜ (𝒞-glue•-path (Abstractionᶜ-FRAC A-⊤ A-abs α))

◯ᶜ-Abstractionᶜ : ∀ {A-⊤ A-abs α} → ◯ᶜ (Abstractionᶜ A-⊤ A-abs α) ≡ ◯ᶜ A-abs
◯ᶜ-Abstractionᶜ {A-⊤} {A-abs} {α} =
  cong ⟨_⟩ᶜ (𝒞-glue◦-path (Abstractionᶜ-FRAC A-⊤ A-abs α))

◯[Abstractionᶜ≡A-abs]
  : ∀ {A-⊤ A-abs α}
  → ⟨ ABS ⟩
  → Abstractionᶜ A-⊤ A-abs α ≡ A-abs
◯[Abstractionᶜ≡A-abs] abs = ◯[Glueᶜ≡A◦] abs ∙ ABS-◯ᶜA≡A abs

◯[squareᶜ'≡f-abs]
  : ∀ {A-⊤ A-abs α B-⊤ B-abs β f-⊤ f-abs f-coh}
  → (abs : ⟨ ABS ⟩)
  → PathP
    (λ i →
      ◯[Abstractionᶜ≡A-abs] {A-⊤} {A-abs} {α} abs i
        ⊸ ◯[Abstractionᶜ≡A-abs] {B-⊤} {B-abs} {β} abs i)
    (squareᶜ' f-⊤ f-abs f-coh)
    f-abs
◯[squareᶜ'≡f-abs] {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} {f-⊤} {f-abs} {f-coh} abs =
  {! ◯[squareᶜ≡f◦]  !}

◯[triangleᶜ'≡b-abs] : ∀ {B-⊤ B-abs β b-⊤ b-abs b-coh} (abs : ⟨ ABS ⟩) →
  PathP (λ i → U (◯[Abstractionᶜ≡A-abs] {B-⊤} {B-abs} {β} abs i))
    (triangleᶜ' {B-⊤} {B-abs} {β} b-⊤ b-abs b-coh)
    b-abs
◯[triangleᶜ'≡b-abs] {B-⊤} {B-abs} {β} {b-⊤} {b-abs} {b-coh} abs =
  {!   !}


squareᶜ'-charge
  : ∀ {A-⊤ A-abs α c}
  → (α-charge : (a : U A-⊤) → α .U (A-⊤ .charge c a) ≡ A-abs .charge c (α .U a))
  → squareᶜ'
      (CHARGE {A-⊤} c) (CHARGE {A-abs} c)
      α-charge
    ≡ CHARGE {Abstractionᶜ A-⊤ A-abs α} c
squareᶜ'-charge {A-⊤} {A-abs} {α} {c} α-charge =
  ⊸-path
    refl
    refl
    (funExt λ _ → Abstractionᶜ-path {A-⊤} {A-abs} {α} refl refl)

squareᶜ'-⨾ᶜ : ∀ {A-⊤ A-abs α B-⊤ B-abs β C-⊤ C-abs γ}
  (f-⊤ : A-⊤ ⊸ B-⊤) (f-abs : A-abs ⊸ B-abs)
  (fc : (a : U A-⊤) → β .U (f-⊤ .U a) ≡ f-abs .U (α .U a))
  (g-⊤ : B-⊤ ⊸ C-⊤) (g-abs : B-abs ⊸ C-abs)
  (gc : (b : U B-⊤) → γ .U (g-⊤ .U b) ≡ g-abs .U (β .U b))
  → squareᶜ' {α = α} {β = β} f-⊤ f-abs fc ⨾ᶜ squareᶜ' {α = β} {β = γ} g-⊤ g-abs gc
    ≡ squareᶜ' {α = α} {β = γ} (f-⊤ ⨾ᶜ g-⊤) (f-abs ⨾ᶜ g-abs)
        (λ a → gc (f-⊤ .U a) ∙ cong (g-abs .U) (fc a))
squareᶜ'-⨾ᶜ {C-⊤ = C-⊤} {C-abs} {γ} f-⊤ f-abs fc g-⊤ g-abs gc =
  ⊸-path refl refl $ funExt λ a →
    Abstractionᶜ-path {C-⊤} {C-abs} {γ}
      (●.map-∘ (f-⊤ .U) (g-⊤ .U) (a .•))
      (◯.map-∘ (f-abs .U) (g-abs .U) (a .◦))

squareᶜ'-≡ : ∀ {A-⊤ A-abs α B-⊤ B-abs β}
  {f-⊤ f-⊤' : A-⊤ ⊸ B-⊤} {f-abs f-abs' : A-abs ⊸ B-abs}
  {fc : (a : U A-⊤) → β .U (f-⊤ .U a) ≡ f-abs .U (α .U a)}
  {fc' : (a : U A-⊤) → β .U (f-⊤' .U a) ≡ f-abs' .U (α .U a)}
  → f-⊤ ≡ f-⊤' → f-abs ≡ f-abs'
  → squareᶜ' {α = α} {β = β} f-⊤ f-abs fc ≡ squareᶜ' f-⊤' f-abs' fc'
squareᶜ'-≡ {B-⊤ = B-⊤} {B-abs} {β} {fc = fc} {fc' = fc'} p q =
  ⊸-path refl refl $ funExt λ a →
    Abstractionᶜ-path {B-⊤} {B-abs} {β}
      (cong (λ f → ●.map (f .U) (a .•)) p)
      (cong (λ f → ◯.map (f .U) (a .◦)) q)

-- Abstractionᶜ-Abstractionᶜ-α•-path
--   : ∀ {A-⊤ A-abs α B-⊤ B-abs β f-⊤ f-abs f-coherence}
--   → PathP
--       (λ i →
--         ⟨ 𝒞-glue•-path (Abstractionᶜ-FRAC A-⊤ A-abs α) i ⟩ᶜ
--           ⊸ ●ᶜ ⟨ 𝒞-glue◦-path (Abstractionᶜ-FRAC B-⊤ B-abs β) i ⟩ᶜ)
--       (●ᶜ.map
--         (squareᶜ'-FRAC {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} f-⊤ f-abs f-coherence ⨾ᶜ η◦ᶜ))
--       (●ᶜ.map ((α ⨾ᶜ f-abs) ⨾ᶜ η◦ᶜ))
-- Abstractionᶜ-Abstractionᶜ-α•-path {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} {f-⊤} {f-abs} {f-coherence} =
--   ⊸-path
--     (λ i → ⟨ 𝒞-glue•-path (Abstractionᶜ-FRAC A-⊤ A-abs α) i ⟩ᶜ)
--     (λ i → ●ᶜ ⟨ 𝒞-glue◦-path (Abstractionᶜ-FRAC B-⊤ B-abs β) i ⟩ᶜ)
--     (square-χ•-path
--       (squareᶜ'-FRAC f-⊤ f-abs f-coherence .U)
--       (●ᶜ.map ((α ⨾ᶜ f-abs) ⨾ᶜ η◦ᶜ) .U)
--       (λ g →
--           cong (●.map (◯.map (f-abs .U))) (sym (g .•→◦))
--         ∙ ●.map-∘ ((α ⨾ᶜ η◦ᶜ) .U) (◯.map (f-abs .U)) (g .•)))

-- Abstractionᶜ-Abstractionᶜ-FRAC
--   : ∀ {A-⊤ A-abs α B-⊤ B-abs β f-⊤ f-abs f-coherence}
--   → Abstractionᶜ-FRAC
--       (Abstractionᶜ A-⊤ A-abs α)
--       (Abstractionᶜ B-⊤ B-abs β)
--       (squareᶜ'-FRAC {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} f-⊤ f-abs f-coherence)
--     ≡ Abstractionᶜ-FRAC A-⊤ B-abs (α ⨾ᶜ f-abs)
-- Abstractionᶜ-Abstractionᶜ-FRAC {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} {f-⊤} {f-abs} {f-coherence} =
--   𝒞-FRACTURE-path
--     (𝒞-glue•-path (Abstractionᶜ-FRAC A-⊤ A-abs α))
--     (𝒞-glue◦-path (Abstractionᶜ-FRAC B-⊤ B-abs β))
--     (Abstractionᶜ-Abstractionᶜ-α•-path
--       {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} {f-⊤} {f-abs} {f-coherence})

Abstractionᶜ-Abstractionᶜ : ∀ {A-⊤ A-abs α B-⊤ B-abs β f-⊤ f-abs f-coherence} →
  Abstractionᶜ
    (Abstractionᶜ A-⊤ A-abs α)
    (Abstractionᶜ B-⊤ B-abs β)
    (squareᶜ' {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} f-⊤ f-abs f-coherence)
  ≡ Abstractionᶜ A-⊤ B-abs (α ⨾ᶜ f-abs)
Abstractionᶜ-Abstractionᶜ {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} {f-⊤} {f-abs} {f-coherence} =
  {!    !}
  -- cong 𝒞-Glue
  --   (Abstractionᶜ-Abstractionᶜ-FRAC
  --     {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} {f-⊤} {f-abs} {f-coherence})
