open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Calf.Phase.Closed (φ : Type) (φ-isProp : isProp φ) where

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure

data ● (X : Type) : Type where
  η• : (x : X) → ● X
  ∗ : (p : φ) → ● X
  law : (x : X) (p : φ) → η• x ≡ ∗ p

ind : {X : Type} (R : ● X → Type)
  → (η•-case : (x : X) → R (η• x))
  → (∗-case : (p : φ) → R (∗ p))
  → (law-case : (x : X) (p : φ) → PathP (λ i → R (law x p i)) (η•-case x) (∗-case p))
  → (x• : ● X) → R x•
ind R η•-case ∗-case law-case (η• x) = η•-case x
ind R η•-case ∗-case law-case (∗ p) = ∗-case p
ind R η•-case ∗-case law-case (law x p i) = law-case x p i

map : {X Y : Type} → (X → Y) → ● X → ● Y
map f (η• x) = η• (f x)
map f (∗ p) = ∗ p
map f (law x p i) = law (f x) p i

Type• : Type₁
Type• = TypeWithStr _ λ X → isEquiv (η• {X})
