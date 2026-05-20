open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Calf.Phase.Open (φ : Type) (φ-isProp : isProp φ) where

open import Cubical.Foundations.Equiv
open import Function

◯ : Type → Type
◯ X = (p : φ) → X

◯' : (φ → Type) → Type
◯' X = (p : φ) → X p

η∘ : {X : Type} → X → ◯ X
η∘ x _ = x

map : {X Y : Type} → (X → Y) → ◯ X → ◯ Y
map f x∘ p = f (x∘ p)

η∘-isNatural : {X Y : Type} (f : X → Y) → η∘ ∘ f ≡ map f ∘ η∘
η∘-isNatural f = funExt λ x → refl

Type∘ : Type₁
Type∘ = Σ[ X ∈ Type ] isEquiv (η∘ {X})
