module Calf.Directed.Path where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Relation.Binary using (_⇒_)
open import Relation.Binary.Definitions

open import Calf.Core.Interval

module _ {X : Type} where

  record _⊑_ (x x' : X) : Type where
    field
      path : 𝟚 → X
      path₀ : path 0𝟚 ≡ x
      path₁ : path 1𝟚 ≡ x'
  open _⊑_ public

  ≡⇒⊑ : _≡_ ⇒ _⊑_
  ≡⇒⊑ {x = x} x≡x' .path _ = x
  ≡⇒⊑ {x = x} x≡x' .path₀ = refl
  ≡⇒⊑ {x = x} x≡x' .path₁ = x≡x'

  ⊑-refl : Reflexive _⊑_
  ⊑-refl = ≡⇒⊑ refl

private variable X Y : Type

⊑-mono : (f : X → Y) {x x' : X} → x ⊑ x' → f x ⊑ f x'
⊑-mono f x⊑x' .path = f ∘ x⊑x' .path
⊑-mono f x⊑x' .path₀ = cong f (x⊑x' .path₀)
⊑-mono f x⊑x' .path₁ = cong f (x⊑x' .path₁)

⊑-funext : {Y : X → Type}
  → {f f' : (x : X) → Y x}
  → ((x : X) → f x ⊑ f' x)
  → f ⊑ f'
⊑-funext pointwise .path 𝕚 x = pointwise x .path 𝕚
⊑-funext pointwise .path₀ = funExt λ x → pointwise x .path₀
⊑-funext pointwise .path₁ = funExt λ x → pointwise x .path₁
