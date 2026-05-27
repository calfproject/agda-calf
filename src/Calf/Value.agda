module Calf.Value where

open import Calf.Core.Directed
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.PathSplit
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.HITs.Join
open import Cubical.HITs.Localization
open import Relation.Binary using (_⇒_)
open import Relation.Binary.Definitions


record 𝒱 : Type₁ where
  field
    val : Type
    is-set : isSet val
    is-preorder : isPreorder val
open 𝒱 public

𝒱-path : {X Y : 𝒱} → val X ≡ val Y → X ≡ Y
𝒱-path {X} {Y} p i .val = p i
𝒱-path {X} {Y} p i .is-set = {!   !}
𝒱-path {X} {Y} p i .is-preorder =
  isProp→PathP
    (λ i → isPropIsPreorder {p i})
    (X .is-preorder)
    (Y .is-preorder)
    i

variable
  X Y Z : 𝒱

module _ {X : 𝒱} where
  _⊑ᵛ_ : val X → val X → Type
  x ⊑ᵛ x' = x ⊑ x'

  ≡⇒⊑ᵛ : _≡_ ⇒ _⊑ᵛ_
  ≡⇒⊑ᵛ = ≡⇒⊑

  ⊑ᵛ-refl : Reflexive _⊑ᵛ_
  ⊑ᵛ-refl = ⊑-refl

  ⊑ᵛ-trans : Transitive _⊑ᵛ_
  ⊑ᵛ-trans = ⊑-trans (X .is-preorder)

⊑ᵛ-syntax : val X → val X → Type
⊑ᵛ-syntax {X} = _⊑ᵛ_ {X}

syntax ⊑ᵛ-syntax {X} x x' = x ⊑[ X ] x'

⊑ᵛ-mono : (f : val X → val Y) {x x' : val X} → x ⊑[ X ] x' → f x ⊑[ Y ] f x'
⊑ᵛ-mono = ⊑-mono

-- ⊑-antisym : Antisymmetric _≡_ (_⊑_ {X})
-- ⊑-antisym {X} x⊑x' x'⊑x = {!    !}

IsDiscreteᵛ : 𝒱 → Type
IsDiscreteᵛ = IsDiscrete ∘ val

fromProp : {X : Type} → isProp X → 𝒱
fromProp {X} X-isProp .val = X
fromProp {X} X-isProp .is-set = isProp→isSet X-isProp
fromProp {X} X-isProp .is-preorder = {!   !}
