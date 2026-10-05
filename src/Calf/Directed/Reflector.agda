module Calf.Directed.Reflector where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.PathSplit
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence using (hPropExt)
open import Cubical.Data.Bool hiding (elim)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.HITs.Localization as Localization
open import Cubical.HITs.S1

open import Calf.Core.Interval
open import Calf.Directed.Localization
open import Calf.Directed.Set
open import Calf.Directed.Thin as 𝕊
open import Calf.Directed.Transitive

private variable X Y Z : Type

data Requirements : Type where
  tran thin hset : Requirements

opaque
  Sᴾ : Requirements → Type
  Sᴾ tran = Λ²
  Sᴾ thin = 𝕊 Bool
  Sᴾ hset = S¹

  Tᴾ : Requirements → Type
  Tᴾ tran = Δ²
  Tᴾ thin = 𝕊 Unit
  Tᴾ hset = Unit

  Fᴾ : (α : Requirements) → Sᴾ α → Tᴾ α
  Fᴾ tran = ι-horn
  Fᴾ thin = 𝕊.map (terminal Bool)
  Fᴾ hset = terminal S¹

isPreorder : Type → Type
isPreorder = isLocal Fᴾ

∥_∥ᴾ : Type → Type
∥_∥ᴾ = Localize Fᴾ

ηᴾ : X → ∥ X ∥ᴾ
ηᴾ = ∣_∣

isPreorderᴾ : isPreorder ∥ X ∥ᴾ
isPreorderᴾ = isLocal-Localize Fᴾ _

isPropIsPreorder : isProp (isPreorder X)
isPropIsPreorder = isPropΠ (λ _ → isPropIsPathSplitEquiv _)

recᴾ : isPreorder Y → (X → Y) → ∥ X ∥ᴾ → Y
recᴾ = Localization.rec

mapᴾ : (X → Y) → ∥ X ∥ᴾ → ∥ Y ∥ᴾ
mapᴾ f = recᴾ isPreorderᴾ (ηᴾ ∘ f)

map2ᴾ : (X → Y → Z) → ∥ X ∥ᴾ → ∥ Y ∥ᴾ → ∥ Z ∥ᴾ
map2ᴾ f = recᴾ (isLocalΠ λ _ → isPreorderᴾ) (mapᴾ ∘ f)

open isPathSplitEquiv

opaque
  unfolding Fᴾ

  isPreorder→isPathTransitive : isPreorder X → isPathTransitive X
  isPreorder→isPathTransitive isPreorderX = const (isPreorderX tran)

  ⊑-trans : isPreorder X → isTransitive X
  ⊑-trans isPreorderX =
    isPathTransitive→isTransitive (isPreorder→isPathTransitive isPreorderX)

  isPreorder→isThin : isPreorder X → isThin X
  isPreorder→isThin isPreorderX =
    equivFun isBoundarySeparated≃isThin (const (isPreorderX thin))

  isPreorder→isSet : isPreorder X → isSet X
  isPreorder→isSet isPreorderX =
    equivFun isS¹Local≃isSet (const (isPreorderX hset))

  isProp→isPreorder : isProp X → isPreorder X
  isProp→isPreorder =
    isProp→isLocal λ
      { tran → inl 0𝟚
      ; thin → inr true
      ; hset → base
      }

  isSet∧isThin∧isPathTransitive→isPreorder :
    isSet X → isThin X → isPathTransitive X → isPreorder X
  isSet∧isThin∧isPathTransitive→isPreorder setX thinX pathTransX tran =
    pathTransX _
  isSet∧isThin∧isPathTransitive→isPreorder setX thinX pathTransX thin =
    invEq isBoundarySeparated≃isThin thinX _
  isSet∧isThin∧isPathTransitive→isPreorder setX thinX pathTransX hset =
    invEq isS¹Local≃isSet setX _

isPreorder≡ : isPreorder X ≡ (isSet X × isThin X × isPathTransitive X)
isPreorder≡ {X} =
  hPropExt isPropIsPreorder
    (isProp× isPropIsSet
      (isProp× (isPropΠ2 λ _ _ → isPropIsProp) (isPropΠ λ _ → isPropIsPathSplitEquiv _)))
    (λ pre → isPreorder→isSet pre , isPreorder→isThin pre , isPreorder→isPathTransitive pre)
    (λ (setX , thinX , pathTransX) →
      isSet∧isThin∧isPathTransitive→isPreorder setX thinX pathTransX)

recᴾ-unique :
  isPreorder Y
  → (f g : ∥ X ∥ᴾ → Y)
  → ((x : X) → f (ηᴾ x) ≡ g (ηᴾ x))
  → (z : ∥ X ∥ᴾ) → f z ≡ g z
recᴾ-unique = Calf.Directed.Localization.rec-unique

isContrᴾ : (x₀ : X) → ((x : X) → ηᴾ x₀ ≡ ηᴾ x) → isContr ∥ X ∥ᴾ
isContrᴾ x₀ h = ηᴾ x₀ , recᴾ-unique isPreorderᴾ (λ _ → ηᴾ x₀) (λ z → z) h

recᴾ-uniqueP : (P : I → Type) → isPreorder (P i1)
  → (f : ∥ X ∥ᴾ → P i0) (g : ∥ X ∥ᴾ → P i1)
  → ((x : X) → PathP P (f (ηᴾ x)) (g (ηᴾ x)))
  → (z : ∥ X ∥ᴾ) → PathP P (f z) (g z)
recᴾ-uniqueP P isPreorderᴾ₁ f g h z =
  toPathP (recᴾ-unique isPreorderᴾ₁ (transport (λ i → P i) ∘ f) g (λ x → fromPathP (h x)) z)

recᴾ-unique2 :
  isPreorder Z
  → (f g : ∥ X ∥ᴾ → ∥ Y ∥ᴾ → Z)
  → ((x : X) (y : Y) → f (ηᴾ x) (ηᴾ y) ≡ g (ηᴾ x) (ηᴾ y))
  → (x : ∥ X ∥ᴾ) (y : ∥ Y ∥ᴾ) → f x y ≡ g x y
recᴾ-unique2 isPreorderZ f g p x y =
  funExt⁻
    (recᴾ-unique (isLocalΠ λ _ → isPreorderZ) f g
      (λ x → funExt (recᴾ-unique isPreorderZ (f (ηᴾ x)) (g (ηᴾ x)) (p x)))
      x)
    y
