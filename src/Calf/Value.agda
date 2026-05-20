open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Bool
open import Cubical.Data.Sigma
open import Function
open import Relation.Binary.Definitions

module Calf.Value where

IsOrthogonal : {X Y : Type} (f : X → Y) → Type → Type
IsOrthogonal {X} {Y} f Z = (g : X → Z) → ∃![ g' ∈ (Y → Z) ] g' ∘ f ≡ g

opaque
  𝕀 : Type
  𝕀 = Bool

  𝕀0 𝕀1 : 𝕀
  𝕀0 = false
  𝕀1 = true

  isSet𝕀 : isSet 𝕀
  isSet𝕀 = isSetBool

BEH : Type
BEH = 𝕀0 ≡ 𝕀1

BEH-isProp : isProp BEH
BEH-isProp = isSet𝕀 𝕀0 𝕀1

opaque
  unfolding 𝕀

  𝕀-isAlgorithmic : BEH → isContr 𝕀
  𝕀-isAlgorithmic beh = false , λ { false → refl ; true → beh }

𝕀₂ : Type
𝕀₂ = Σ[ i ∈ 𝕀 ] Σ[ j ∈ 𝕀 ] (i ≡ 𝕀1 → j ≡ 𝕀1)

data 𝕀∨𝕀 : Type where
  inj₀ : 𝕀 → 𝕀∨𝕀
  inj₁ : 𝕀 → 𝕀∨𝕀
  law : inj₀ 𝕀1 ≡ inj₁ 𝕀0

ι : 𝕀∨𝕀 → 𝕀₂
ι (inj₀ i) = 𝕀0 , i , λ beh → isContr→isProp (𝕀-isAlgorithmic beh) i 𝕀1
ι (inj₁ i) = i , 𝕀1 , λ _ → refl
ι (law i) = 𝕀0 , 𝕀1 , λ beh → isSet𝕀 𝕀1 𝕀1 (isContr→isProp (𝕀-isAlgorithmic beh) 𝕀1 𝕀1) refl i


IsPreorder : Type → Type
IsPreorder = IsOrthogonal ι

record 𝒱 : Type₁ where
  field
    val : Type
    isPreorder : IsPreorder val

  isSet𝒱 : isSet val
  isSet𝒱 x x' p p' = {!   !}
open 𝒱 public

variable
  X Y Z : 𝒱

record _⊑_ (x x' : val X) : Type where
  field
    path : 𝕀 → val X
    path₀ : path 𝕀0 ≡ x
    path₁ : path 𝕀1 ≡ x'
open _⊑_

⊑-syntax : val X → val X → Type
⊑-syntax {X} = _⊑_ {X}

syntax ⊑-syntax {X} x x' = x ⊑[ X ] x'

≡⇒⊑ : ∀ {x x'} → x ≡ x' → x ⊑[ X ] x'
≡⇒⊑ {x = x} x≡x' .path _ = x
≡⇒⊑ {x = x} x≡x' .path₀ = refl
≡⇒⊑ {x = x} x≡x' .path₁ = x≡x'

⊑-refl : Reflexive (_⊑_ {X})
⊑-refl {x} = ≡⇒⊑ refl

⊑-mono : ∀ (f : val X → val Y) {x x'} → x ⊑[ X ] x' → f x ⊑[ Y ] f x'
⊑-mono f x⊑x' .path = f ∘ x⊑x' .path
⊑-mono f x⊑x' .path₀ = cong f (x⊑x' .path₀)
⊑-mono f x⊑x' .path₁ = cong f (x⊑x' .path₁)

⊑-trans : Transitive (_⊑_ {X})
⊑-trans {X} {x} {x'} {x''} x⊑x' x'⊑x'' =
  record
    { path = λ i → X .isPreorder aux .fst .fst (i , i , λ i≡1 → i≡1)
    ; path₀ =
        cong (X .isPreorder aux .fst .fst ∘ (𝕀0 ,_) ∘ (𝕀0 ,_)) (λ i beh → isSet𝕀 𝕀0 𝕀1 beh (isContr→isProp (𝕀-isAlgorithmic beh) 𝕀0 𝕀1) i)
        ∙ cong (_$ inj₀ 𝕀0) (X .isPreorder aux .fst .snd)
        ∙ x⊑x' .path₀
    ; path₁ =
        cong (X .isPreorder aux .fst .fst ∘ (𝕀1 ,_) ∘ (𝕀1 ,_)) (λ i beh → isSet𝕀 𝕀1 𝕀1 beh (λ _ → 𝕀1) i)
        ∙ cong (_$ inj₁ 𝕀1) (X .isPreorder aux .fst .snd)
        ∙ x'⊑x'' .path₁
    }
  where
    aux : 𝕀∨𝕀 → val X
    aux (inj₀ i) = x⊑x' .path i
    aux (inj₁ i) = x'⊑x'' .path i
    aux (law i) = (x⊑x' .path₁ ∙ sym (x'⊑x'' .path₀)) i

IsDiscrete : 𝒱 → Type
IsDiscrete X = {x x' : val X} → isEquiv (≡⇒⊑ {X} {x} {x'})

⊑-beh : BEH → IsDiscrete X
⊑-beh beh .equiv-proof x⊑x' .fst .fst =
  sym (x⊑x' .path₀)
  ∙ cong (x⊑x' .path) (isContr→isProp (𝕀-isAlgorithmic beh) 𝕀0 𝕀1)
  ∙ x⊑x' .path₁
⊑-beh beh .equiv-proof x⊑x' .fst .snd = {!   !}
⊑-beh beh .equiv-proof x⊑x' .snd = {!   !}

fromProp : {X : Type} → isProp X → 𝒱
fromProp {X} X-isProp .val = X
fromProp {X} X-isProp .isPreorder = {!   !}
