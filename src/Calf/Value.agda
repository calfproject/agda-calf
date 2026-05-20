open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Function
open import Relation.Binary.Definitions

module Calf.Value where  -- (BEH : Type) (BEH-isProp : isProp BEH) (𝕀 : Type) (𝕀0 𝕀1 : 𝕀) (𝕀-isAlgorithmic : BEH → isContr 𝕀) where

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

-- ⊑-isProp : {x x' : val X} → isProp (x ⊑[ X ] x')
-- ⊑-isProp = {!   !}

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

fromProp : {X : Type} → isProp X → 𝒱
fromProp {X} X-isProp .val = X
fromProp {X} X-isProp .isPreorder = {!   !}
