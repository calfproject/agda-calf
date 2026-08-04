module Calf.Computation.Abstraction.Properties where

open import Calf.Value
import Calf.Value.Open as ◯
import Calf.Value.Closed as ●
open import Calf.Computation
open import Calf.Computation.Open as ◯ᶜ
open import Calf.Computation.Closed as ●ᶜ
open import Calf.Computation.Glue as Glueᶜ hiding (squareᶜ)
open 𝒞-FRAC

open import Calf.Computation.Abstraction.Base

opaque
  unfolding Abstractionᶜ

  ●ᶜ-Abstractionᶜ : ∀ {A-⊤ A-abs α} → ●ᶜ (Abstractionᶜ A-⊤ A-abs α) ≡ ●ᶜ A-⊤
  ●ᶜ-Abstractionᶜ {A-⊤} {A-abs} {α} = {!   !}
  -- cong ⟨_⟩ᶜ (𝒞-glue•-path (Abstractionᶜ-FRAC A-⊤ A-abs α))

  ◯ᶜ-Abstractionᶜ : ∀ {A-⊤ A-abs α} → ◯ᶜ (Abstractionᶜ A-⊤ A-abs α) ≡ ◯ᶜ A-abs
  ◯ᶜ-Abstractionᶜ {A-⊤} {A-abs} {α} = {!   !}
  -- cong ⟨_⟩ᶜ (𝒞-glue◦-path (Abstractionᶜ-FRAC A-⊤ A-abs α))

  squareᶜ'-charge
    : ∀ {A-⊤ A-abs α c}
    → (α-charge : (a : U A-⊤) → α .U (A-⊤ .charge c a) ≡ A-abs .charge c (α .U a))
    → squareᶜ'
        (CHARGE c) (CHARGE c)
        α-charge
      ≡ CHARGE {A = Abstractionᶜ A-⊤ A-abs α} c
  squareᶜ'-charge {A-⊤} {A-abs} {α} {c} α-charge = {!   !}

  squareᶜ'-⨾ᶜ : ∀ {A-⊤ A-abs α B-⊤ B-abs β C-⊤ C-abs γ}
    (f-⊤ : A-⊤ ⊸ B-⊤) (f-abs : A-abs ⊸ B-abs)
    (fc : (a : U A-⊤) → β .U (f-⊤ .U a) ≡ f-abs .U (α .U a))
    (g-⊤ : B-⊤ ⊸ C-⊤) (g-abs : B-abs ⊸ C-abs)
    (gc : (b : U B-⊤) → γ .U (g-⊤ .U b) ≡ g-abs .U (β .U b))
    → squareᶜ' {α = α} {β = β} f-⊤ f-abs fc ⨾ᶜ squareᶜ' {α = β} {β = γ} g-⊤ g-abs gc
      ≡ squareᶜ' {α = α} {β = γ} (f-⊤ ⨾ᶜ g-⊤) (f-abs ⨾ᶜ g-abs)
          (λ a → gc (f-⊤ .U a) ∙ cong (g-abs .U) (fc a))
  squareᶜ'-⨾ᶜ f-⊤ f-abs fc g-⊤ g-abs gc = {!   !}

  squareᶜ'-≡ : ∀ {A-⊤ A-abs α B-⊤ B-abs β}
    {f-⊤ f-⊤' : A-⊤ ⊸ B-⊤} {f-abs f-abs' : A-abs ⊸ B-abs}
    {fc : (a : U A-⊤) → β .U (f-⊤ .U a) ≡ f-abs .U (α .U a)}
    {fc' : (a : U A-⊤) → β .U (f-⊤' .U a) ≡ f-abs' .U (α .U a)}
    → f-⊤ ≡ f-⊤' → f-abs ≡ f-abs'
    → squareᶜ' {α = α} {β = β} f-⊤ f-abs fc ≡ squareᶜ' f-⊤' f-abs' fc'
  squareᶜ'-≡ p q = {!   !}

  Abstractionᶜ-Abstractionᶜ-FRAC
    : ∀ {A-⊤ A-abs α B-⊤ B-abs β f-⊤ f-abs f-coherence}
    → Abstractionᶜ-FRAC
        (𝒞-fromFRAC (Abstractionᶜ-FRAC A-⊤ A-abs α))
        (𝒞-fromFRAC (Abstractionᶜ-FRAC B-⊤ B-abs β))
        (squareᶜ'-FRAC {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} f-⊤ f-abs f-coherence)
      ≡ Abstractionᶜ-FRAC A-⊤ B-abs (α ⨾ᶜ f-abs)
  Abstractionᶜ-Abstractionᶜ-FRAC = {!   !}

  Abstractionᶜ-Abstractionᶜ : ∀ {A-⊤ A-abs α B-⊤ B-abs β f-⊤ f-abs f-coherence} →
    Abstractionᶜ (Abstractionᶜ A-⊤ A-abs α) (Abstractionᶜ B-⊤ B-abs β) (squareᶜ' {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} f-⊤ f-abs f-coherence)
    ≡ Abstractionᶜ A-⊤ B-abs (α ⨾ᶜ f-abs)
  Abstractionᶜ-Abstractionᶜ = {!   !}
