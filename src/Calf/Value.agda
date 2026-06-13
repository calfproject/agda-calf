module Calf.Value where

open import Calf.Core.Directed
open import Calf.Core.Directed using (BEH) public
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
𝒱-path {X} {Y} p i .is-set =
  isProp→PathP
    (λ i → isPropIsSet {_} {p i})
    (X .is-set)
    (Y .is-set)
    i
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

⊑ᵛ-isProp : {x x' : val X} → isProp (x ⊑[ X ] x')
⊑ᵛ-isProp {X} = isPreorder→isProp⊑ (X .is-preorder) _ _

-- ⊑-antisym : Antisymmetric _≡_ (_⊑_ {X})
-- ⊑-antisym {X} x⊑x' x'⊑x = {!    !}

isDiscreteᵛ : 𝒱 → Type
isDiscreteᵛ X = isDiscrete (val X)

⊑ᵛ-beh : BEH → isDiscreteᵛ X
⊑ᵛ-beh = ⊑-beh

fromProp : hProp ℓ-zero → 𝒱
fromProp P .val = ⟨ P ⟩
fromProp P .is-set = isProp→isSet (P .snd)
fromProp P .is-preorder = isProp→isPreorder (P .snd)

module ⊑ᵛ-Reasoning (X : 𝒱) where
  open import Relation.Binary

  ≡-isEquivalence : IsEquivalence (_≡_ {A = val X})
  ≡-isEquivalence = record { refl = refl ; sym = sym ; trans = _∙_ }

  open Preorder hiding (refl)
  open IsPreorder hiding (refl)

  ⊑ᵛ-preorder : Preorder _ _ _
  ⊑ᵛ-preorder .Carrier = val X
  ⊑ᵛ-preorder ._≈_ = _≡_
  ⊑ᵛ-preorder ._≲_ = _⊑ᵛ_ {X}
  ⊑ᵛ-preorder .Preorder.isPreorder .isEquivalence = ≡-isEquivalence
  ⊑ᵛ-preorder .Preorder.isPreorder .reflexive = ≡⇒⊑ᵛ {X}
  ⊑ᵛ-preorder .Preorder.isPreorder .trans = ⊑ᵛ-trans {X}

  open import Relation.Binary.Reasoning.Preorder ⊑ᵛ-preorder as P public
    renaming (_∎ to _∎ᵛ)

  infixr 2 step-⊑ᵛ
  step-⊑ᵛ = step-≲
  syntax step-⊑ᵛ x yRz x⊑ᵛy = x ⊑ᵛ⟨ x⊑ᵛy ⟩ yRz

  infixr 2 step-≡ᵛ
  step-≡ᵛ = step-≈
  syntax step-≡ᵛ x yRz x⊑ᵛy = x ≡ᵛ⟨ x⊑ᵛy ⟩ yRz
