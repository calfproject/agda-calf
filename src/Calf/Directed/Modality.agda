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

private variable X Y : Type

data Requirements : Type where
  transitive thin hset : Requirements

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

open isPathSplitEquiv public

⊑-trans : isPreorder X → Transitive _⊑_
⊑-trans isPreorderX = isPathTransitive→Transitive[⊑] (const (isPreorderX transitive))

isPreorder→isProp⊑ : isPreorder X → (x x' : X) → isProp (x ⊑ x')
isPreorder→isProp⊑ isPreorderX = transport isBoundarySeparated≡isThin (const (isPreorderX thin))

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
