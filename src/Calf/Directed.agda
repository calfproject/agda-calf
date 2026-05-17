{-# OPTIONS --cubical --allow-unsolved-metas #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Data.Bool
open import Data.Empty
open import Data.List
open import Data.Nat
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Function
open import Relation.Binary.Definitions

module Calf.Directed where  -- (BEH : Type) (BEH-isProp : isProp BEH) (𝕀 : Type) (𝕀0 𝕀1 : 𝕀) (𝕀-isAlgorithmic : BEH → isContr 𝕀) where

IsPreorder : Type → Type
IsPreorder = {!   !}

record 𝒱 : Type₁ where
  field
    val : Type
    isPreorder : IsPreorder val
open 𝒱 public

variable
  X Y Z : 𝒱

_⊑_ : val X → val X → Type
_⊑_ = {!   !}

⊑-syntax : val X → val X → Type
⊑-syntax {X} = _⊑_ {X}

syntax ⊑-syntax {X} x x' = x ⊑[ X ] x'

⊑-isProp : {x x' : val X} → isProp (x ⊑[ X ] x')
⊑-isProp = {!   !}

≡⇒⊑ : ∀ {x x'} → x ≡ x' → x ⊑[ X ] x'
≡⇒⊑ = {!   !} -- {x = x} x≡x' = ∣ const x , refl , x≡x' ∣₁

⊑-refl : Reflexive (_⊑_ {X})
⊑-refl = {!   !} --  x = ≡⇒⊑ refl

⊑-mono : ∀ (f : val X → val Y) {x x'} → x ⊑[ X ] x' → f x ⊑[ Y ] f x'
⊑-mono = {!   !} -- f = map λ (path , path₀ , path₁) → f ∘ path , cong f path₀ , cong f path₁

⊑-trans : Transitive (_⊑_ {X})
⊑-trans = {!   !}

IsDiscrete : 𝒱 → Type
IsDiscrete X = {x x' : val X} → isEquiv (≡⇒⊑ {X} {x} {x'})

module _ (BEH : Type) (BEH-isProp : isProp BEH) where
  ⊑-beh : BEH → IsDiscrete X
  ⊑-beh = {!   !}


1ᵛ : 𝒱
1ᵛ .val = ⊤
1ᵛ .isPreorder = {!   !}

_×ᵛ_ : 𝒱 → 𝒱 → 𝒱
(X ×ᵛ Y) .val = val X × val Y
(X ×ᵛ Y) .isPreorder = {!   !}

Πᵛ : (X : 𝒱) (Y : val X → 𝒱) → 𝒱
Πᵛ X Y .val = (x : val X) → val (Y x)
Πᵛ X Y .isPreorder = {!   !}

⊑-funext : {Y : val X → 𝒱}
  → {f f' : (x : val X) → val (Y x)}
  → ((x : val X) → f x ⊑[ Y x ] f' x)
  → f ⊑[ Πᵛ X Y ] f'
⊑-funext = {!   !}

_→ᵛ_ : 𝒱 → 𝒱 → 𝒱
X →ᵛ Y = Πᵛ X (const Y)

⊥ᵛ : 𝒱
⊥ᵛ .val = ⊥
⊥ᵛ .isPreorder = {!   !}

_+ᵛ_ : 𝒱 → 𝒱 → 𝒱
(X +ᵛ Y) .val = val X ⊎ val Y
(X +ᵛ Y) .isPreorder = {!   !}

Σᵛ : (X : 𝒱) ⦃ _ : IsDiscrete X ⦄ (Y : val X → 𝒱) → 𝒱
Σᵛ X Y .val = Σ (val X) (val ∘ Y)
Σᵛ X Y .isPreorder = {!   !}

ℕᵛ : 𝒱
ℕᵛ .val = ℕ
ℕᵛ .isPreorder = {!   !}

Listᵛ : 𝒱 → 𝒱
Listᵛ X .val = List (X .val)
Listᵛ X .isPreorder = {!   !}

instance
  ℕᵛ-isDiscrete : IsDiscrete ℕᵛ
  ℕᵛ-isDiscrete = {!   !}

ω : 𝒱
ω .val = ℕ
ω .isPreorder = {!   !}
