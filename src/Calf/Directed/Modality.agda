module Calf.Directed.Modality where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Fiberwise
open import Cubical.Foundations.Equiv.PathSplit
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Bool hiding (elim)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.HITs.Localization as Localization hiding (rec)
open import Cubical.HITs.S1 hiding (rec; elim)
open import Relation.Binary.Definitions

open import Calf.Core.Interval
open import Calf.Directed.Set
open import Calf.Directed.Transitive
open import Calf.Directed.Thin
open import Calf.Directed.Localization
open import Calf.Directed.Path

private variable X Y Z : Type

data Requirements : Type where
  transitive thin hset : Requirements

opaque
  Sᴾ : Requirements → Type
  Sᴾ transitive = Λ²
  Sᴾ thin = 𝕊 Bool
  Sᴾ hset = S¹

  Tᴾ : Requirements → Type
  Tᴾ transitive = Δ²
  Tᴾ thin = 𝕊 Unit
  Tᴾ hset = Unit

  Fᴾ : (α : Requirements) → Sᴾ α → Tᴾ α
  Fᴾ transitive = ι
  Fᴾ thin = 𝕊map (terminal Bool)
  Fᴾ hset = terminal S¹

isPreorder : Type → Type
isPreorder = isLocal Fᴾ

∥_∥ᴾ : Type → Type
∥_∥ᴾ = Localize Fᴾ

ηᴾ : X → ∥ X ∥ᴾ
ηᴾ = ∣_∣

isPreorderP : isPreorder ∥ X ∥ᴾ
isPreorderP = isLocal-Localize Fᴾ _

isPropIsPreorder : isProp (isPreorder X)
isPropIsPreorder = isPropΠ (λ _ → isPropIsPathSplitEquiv _)

rec : isPreorder Y → (X → Y) → ∥ X ∥ᴾ → Y
rec = Localization.rec

mapᴾ : (X → Y) → ∥ X ∥ᴾ → ∥ Y ∥ᴾ
mapᴾ f = rec isPreorderP (ηᴾ ∘ f)

map2ᴾ : (X → Y → Z) → ∥ X ∥ᴾ → ∥ Y ∥ᴾ → ∥ Z ∥ᴾ
map2ᴾ f = rec (isLocalΠ λ _ → isPreorderP) (mapᴾ ∘ f)

open isPathSplitEquiv

opaque
  unfolding Fᴾ

  ⊑-trans : isPreorder X → Transitive (_⊑_ {X})
  ⊑-trans isPreorderX = isPathTransitive→Transitive[⊑] (const (isPreorderX transitive))

  isPreorder→isThin : isPreorder X → isThin X
  isPreorder→isThin isPreorderX = transport isBoundarySeparated≡isThin (const (isPreorderX thin))

  isPreorder→isSet : isPreorder X → isSet X
  isPreorder→isSet isPreorderX =
    transport isS¹Null≡isSet λ _ →
    fromIsEquiv _ $ equivIsEquiv $
    compEquiv (invEquiv (UnitToType≃ _)) (_ , toIsEquiv _ (isPreorderX hset))

  isProp→isPreorder : isProp X → isPreorder X
  isProp→isPreorder =
    isProp→isLocal λ
      { transitive → inl 0𝟚
      ; thin → inr true
      ; hset → base
      }

rec-unique :
  isPreorder Y
  → (f g : ∥ X ∥ᴾ → Y)
  → ((x : X) → f (ηᴾ x) ≡ g (ηᴾ x))
  → (z : ∥ X ∥ᴾ) → f z ≡ g z
rec-unique = recUnique

rec-unique2 :
  isPreorder Z
  → (f g : ∥ X ∥ᴾ → ∥ Y ∥ᴾ → Z)
  → ((x : X) (y : Y) → f (ηᴾ x) (ηᴾ y) ≡ g (ηᴾ x) (ηᴾ y))
  → (x : ∥ X ∥ᴾ) (y : ∥ Y ∥ᴾ) → f x y ≡ g x y
rec-unique2 isPreorderZ f g p x y =
  funExt⁻
    (rec-unique (isLocalΠ λ _ → isPreorderZ) f g
      (λ x → funExt (rec-unique isPreorderZ (f (ηᴾ x)) (g (ηᴾ x)) (p x)))
      x)
    y
