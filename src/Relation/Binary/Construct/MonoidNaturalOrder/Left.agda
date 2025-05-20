------------------------------------------------------------------------
-- Conversion of a monoid into a preorder via the left natural order.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Core using (Op₂)
open import Algebra.Structures using (IsMonoid)
open import Relation.Binary.Core using (Rel; _⇒_; _Preserves₂_⟶_⟶_)

module Relation.Binary.Construct.MonoidNaturalOrder.Left
  {a ℓ} {A : Set a} (_≈_ : Rel A ℓ) (_∙_ : Op₂ A) (ε : A) (monoid : IsMonoid _≈_ _∙_ ε) where

open import Data.Product.Base using (_,_)
open import Level
open import Relation.Binary.Bundles using (Preorder)
open import Relation.Binary.Structures using (IsEquivalence; IsPreorder)
open import Relation.Binary.Definitions
  using (Symmetric; Transitive; Reflexive; _Respectsʳ_; _Respectsˡ_; _Respects₂_; Minimum)
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

open import Algebra.Bundles
open import Algebra.Definitions _≈_
import Algebra.Properties.CommutativeSemigroup as Interchange

------------------------------------------------------------------------
-- Definition

infix 4 _≤_

record _≤_ (x y : A) : Set (a ⊔ ℓ) where
  field
    diff : A
    proof : (x ∙ diff) ≈ y
open _≤_

------------------------------------------------------------------------
-- Relational properties

reflexive : _≈_ ⇒ _≤_
reflexive x≈y .diff = ε
reflexive {x} {y} x≈y .proof = begin
  x ∙ ε ≈⟨ identityʳ x ⟩
  x     ≈⟨ x≈y ⟩
  y     ∎
  where open IsMonoid monoid; open ≈-Reasoning setoid

refl : Reflexive _≤_
refl = reflexive (IsMonoid.refl monoid)

trans : Transitive _≤_
trans x≤y y≤z .diff = x≤y .diff ∙ y≤z .diff
trans {x} {y} {z} x≤y y≤z .proof = begin
  (x ∙ (x≤y .diff ∙ y≤z .diff)) ≈⟨ assoc x (x≤y .diff) (y≤z .diff) ⟨
  ((x ∙ x≤y .diff) ∙ y≤z .diff) ≈⟨ ∙-congʳ (x≤y .proof) ⟩
  (y ∙ y≤z .diff)               ≈⟨ y≤z .proof ⟩
  z                             ∎
  where open IsMonoid monoid; open ≈-Reasoning setoid

respʳ : _≤_ Respectsʳ _≈_
respʳ y≈z x≤y .diff = x≤y .diff
respʳ {x} {y} {z} y≈z x≤y .proof = begin
  (x ∙ x≤y .diff) ≈⟨ x≤y .proof ⟩
  y               ≈⟨ y≈z ⟩
  z               ∎
  where open IsMonoid monoid; open ≈-Reasoning setoid

respˡ : _≤_ Respectsˡ _≈_
respˡ y≈z y≤x .diff = y≤x .diff
respˡ {x} {y} {z} y≈z y≤x .proof = begin
  (z ∙ y≤x .diff) ≈⟨ ∙-congʳ (sym y≈z) ⟩
  (y ∙ y≤x .diff) ≈⟨ y≤x .proof ⟩
  x               ∎
  where open IsMonoid monoid; open ≈-Reasoning setoid

resp₂ : _≤_ Respects₂ _≈_
resp₂ = respʳ , respˡ

∙-mono-≤ : Commutative _∙_ → _∙_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
∙-mono-≤ comm x≤y u≤v .diff = x≤y .diff ∙ u≤v .diff
∙-mono-≤ comm {x} {y} {u} {v} x≤y u≤v .proof = begin
  ((x ∙ u) ∙ (x≤y .diff ∙ u≤v .diff)) ≈⟨ interchange x u (x≤y .diff) (u≤v .diff) ⟩
  ((x ∙ x≤y .diff) ∙ (u ∙ u≤v .diff)) ≈⟨ ∙-cong (x≤y .proof) (u≤v .proof) ⟩
  (y ∙ v)               ∎
  where
    open IsMonoid monoid
    open ≈-Reasoning setoid
    open Interchange
      ( record
          { Carrier = A
          ; _≈_ = _≈_
          ; _∙_ = _∙_
          ; isCommutativeSemigroup = record { isSemigroup = isSemigroup ; comm = comm }
          }
      ) using (interchange)

≤-minimum : Minimum _≤_ ε
≤-minimum x .diff = x
≤-minimum x .proof = IsMonoid.identityˡ monoid x

x≤x∙y : ∀ x y → x ≤ (x ∙ y)
x≤x∙y x y .diff = y
x≤x∙y x y .proof = IsEquivalence.refl isEquivalence
  where open IsMonoid monoid; open ≈-Reasoning setoid

------------------------------------------------------------------------
-- Structures

isPreorder : IsPreorder _≈_ _≤_
isPreorder = record
  { isEquivalence = isEquivalence
  ; reflexive     = reflexive
  ; trans         = trans
  }
  where open IsMonoid monoid hiding (reflexive; trans)

------------------------------------------------------------------------
-- Bundles

preorder : Preorder a ℓ (a ⊔ ℓ)
preorder = record
  { isPreorder = isPreorder
  }
