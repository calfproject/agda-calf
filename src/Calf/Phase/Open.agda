open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Function

module Calf.Phase.Open (φ : Type) (φ-isProp : isProp φ) where

◯ : Type → Type
◯ X = (p : φ) → X

◯' : (φ → Type) → Type
◯' X = (p : φ) → X p

η◦ : {X : Type} → X → ◯ X
η◦ x _ = x

map : {X Y : Type} → (X → Y) → ◯ X → ◯ Y
map f x◦ p = f (x◦ p)

η◦-isNatural : {X Y : Type} (f : X → Y) → η◦ ∘ f ≡ map f ∘ η◦
η◦-isNatural f = funExt λ x → refl

Type◦ : Type₁
Type◦ = TypeWithStr _ λ X → isEquiv (η◦ {X})

◯-join : {X : Type} → ◯ (◯ X) → ◯ X
◯-join x p = x p p

◯-η-isEquiv : {X : Type} → isEquiv (η◦ {◯ X})
◯-η-isEquiv = isoToIsEquiv (iso η◦ ◯-join sec ret)
  where
  sec : {X : Type} → (x : ◯ (◯ X)) → η◦ (◯-join x) ≡ x
  sec x = funExt λ p → funExt λ q → cong (λ r → x r q) (φ-isProp q p)

  ret : {X : Type} → (x : ◯ X) → ◯-join (η◦ x) ≡ x
  ret x = refl
