open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure

module Calf.Computation.Seal where

open import Calf.Core.Cost
open import Calf.Core.Directed
open import Calf.Computation
open import Calf.Value
import Calf.Value.Closed as ●ᵛ
import Calf.Value.Open as ◯ᵛ
open import Calf.Value.Glue
open import Calf.Value.Seal
open import Calf.Computation.Power
open import Calf.Computation.Open as ◯ᶜ
open import Calf.Computation.Closed as ●ᶜ
open import Calf.Computation.Glue
open import Calf.Computation.Abstraction

Sealᶜ : 𝒞 → 𝒞
Sealᶜ A .U = Seal (A .U)
Sealᶜ A .is-preorder = isPreorderSeal (A .is-preorder)
Sealᶜ A .charge c a .• = ●ᶜ A .charge c (a .•)
Sealᶜ A .charge c a .◦ = ◯ᶜ A .charge c (a .◦)
Sealᶜ A .charge c a .•→◦ = ≡⇒⊑ {!   !}
Sealᶜ A .charge/0 {a} i .• = ●ᶜ A .charge/0 {a .•} i
Sealᶜ A .charge/0 {a} i .◦ = ◯ᶜ A .charge/0 {a .◦} i
Sealᶜ A .charge/0 {a} i .•→◦ = {!   !}
Sealᶜ A .charge/+ {a} {c₁} {c₂} i .• = ●ᶜ A .charge/+ {a .•} {c₁} {c₂} i
Sealᶜ A .charge/+ {a} {c₁} {c₂} i .◦ = ◯ᶜ A .charge/+ {a .◦} {c₁} {c₂} i
Sealᶜ A .charge/+ {a} {c₁} {c₂} i .•→◦ = {!   !}

_⊸ᵈ_ : 𝒞 → 𝒞 → 𝒱
A ⊸ᵈ B = A ⊸ Sealᶜ B

idᵈ : A ⊸ᵈ A
idᵈ .U a .• = η• a
idᵈ .U a .◦ = η◦ a
idᵈ .U a .•→◦ = ⊑-refl
idᵈ {A} .charge c a i .• = η• (A .charge c a)
idᵈ {A} .charge c a i .◦ = η◦ (A .charge c a)
idᵈ {A} .charge c a i .•→◦ = {! isPreorder→isProp⊑ (A .is-preorder) !}

infixl 9 _⨾ᵈ_
_⨾ᵈ_ : (A ⊸ B) → (B ⊸ C) → (A ⊸ C)
f ⨾ᵈ g = {!   !}

squareᵈ' : ∀ {A-⊤ A-abs α B-⊤ B-abs β} (f-⊤ : A-⊤ ⊸ B-⊤) (f-abs : A-abs ⊸ B-abs)
  → ((a-⊤ : U A-⊤) → U β (U f-⊤ a-⊤) ⊑[ B-abs ] U f-abs (U α a-⊤))
  → Abstractionᶜ A-⊤ A-abs α ⊸ᵈ Abstractionᶜ B-⊤ B-abs β
squareᵈ' = {!   !}
