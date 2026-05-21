module Calf.Value where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Function
open import Relation.Binary using (_⇒_)
open import Relation.Binary.Definitions

IsOrthogonal : {X Y : Type} (f : X → Y) → Type → Type
IsOrthogonal {X} {Y} f Z = (g : X → Z) → ∃![ g' ∈ (Y → Z) ] g' ∘ f ≡ g

opaque
  open import Cubical.Data.Unit

  𝕀 : Type
  𝕀 = Unit

  isSet𝕀 : isSet 𝕀
  isSet𝕀 = isSetUnit

  _≤𝕀_ : 𝕀 → 𝕀 → Type
  tt ≤𝕀 tt = Unit

  ≤𝕀-isProp : ∀ {i j} → isProp (i ≤𝕀 j)
  ≤𝕀-isProp = isContr→isProp isContrUnit

  ≤𝕀-refl : Reflexive _≤𝕀_
  ≤𝕀-refl = tt

  ≤𝕀-trans : Transitive _≤𝕀_
  ≤𝕀-trans _ _ = tt

  ≤𝕀-antisym : Antisymmetric _≡_ _≤𝕀_
  ≤𝕀-antisym = isContr→isProp isContrUnit

  𝕀0 𝕀1 : 𝕀
  𝕀0 = tt
  𝕀1 = tt

  𝕀0-minimum : Minimum _≤𝕀_ 𝕀0
  𝕀0-minimum _ = tt

  𝕀1-maximum : Maximum _≤𝕀_ 𝕀1
  𝕀1-maximum tt = tt


𝕀₂ : Type
𝕀₂ = Σ[ 𝕚 ∈ 𝕀 ] Σ[ 𝕛 ∈ 𝕀 ] 𝕚 ≤𝕀 𝕛

data 𝕀∨𝕀 : Type where
  inj₀ : (𝕚 : 𝕀) → 𝕀∨𝕀
  inj₁ : (𝕚 : 𝕀) → 𝕀∨𝕀
  law : inj₀ 𝕀1 ≡ inj₁ 𝕀0

ι : 𝕀∨𝕀 → 𝕀₂
ι (inj₀ 𝕚) = 𝕀0 , 𝕚 , 𝕀0-minimum 𝕚
ι (inj₁ 𝕚) = 𝕚 , 𝕀1 , 𝕀1-maximum 𝕚
ι (law i) = 𝕀0 , 𝕀1 , ≤𝕀-isProp (𝕀0-minimum 𝕀1) (𝕀1-maximum 𝕀0) i


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

≡⇒⊑ : _≡_ ⇒  _⊑_ {X}
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
    { path = λ 𝕚 → X .isPreorder aux .fst .fst (𝕚 , 𝕚 , ≤𝕀-refl)
    ; path₀ =
        cong (X .isPreorder aux .fst .fst ∘ (𝕀0 ,_) ∘ (𝕀0 ,_)) (≤𝕀-isProp _ _)
        ∙ cong (_$ inj₀ 𝕀0) (X .isPreorder aux .fst .snd)
        ∙ x⊑x' .path₀
    ; path₁ =
        cong (X .isPreorder aux .fst .fst ∘ (𝕀1 ,_) ∘ (𝕀1 ,_)) (≤𝕀-isProp _ _)
        ∙ cong (_$ inj₁ 𝕀1) (X .isPreorder aux .fst .snd)
        ∙ x'⊑x'' .path₁
    }
  where
    aux : 𝕀∨𝕀 → val X
    aux (inj₀ 𝕚) = x⊑x' .path 𝕚
    aux (inj₁ 𝕚) = x'⊑x'' .path 𝕚
    aux (law i) = (x⊑x' .path₁ ∙ sym (x'⊑x'' .path₀)) i

⊑-antisym : Antisymmetric _≡_ (_⊑_ {X})
⊑-antisym {X} x⊑x' x'⊑x = {!   !}

IsDiscrete : 𝒱 → Type
IsDiscrete X = {x x' : val X} → isEquiv (≡⇒⊑ {X} {x} {x'})

fromProp : {X : Type} → isProp X → 𝒱
fromProp {X} X-isProp .val = X
fromProp {X} X-isProp .isPreorder g =
  (g ∘ inj₀ ∘ fst , λ i i∨i → X-isProp (g (inj₀ (fst (ι i∨i)))) (g i∨i) i) ,
  λ (g' , pf) i → (λ i₂ → X-isProp (g (inj₀ (fst i₂))) (g' i₂) i) , {!   !}

module _ where
  BEH : Type
  BEH = 𝕀0 ≡ 𝕀1

  BEH-isProp : isProp BEH
  BEH-isProp = isSet𝕀 𝕀0 𝕀1

  𝕀-isAlgorithmic : BEH → isContr 𝕀
  𝕀-isAlgorithmic beh .fst = 𝕀0
  𝕀-isAlgorithmic beh .snd i =
    ≤𝕀-antisym
      (𝕀0-minimum _)
      (≤𝕀-trans (𝕀1-maximum _) (subst (_≤𝕀 𝕀0) beh ≤𝕀-refl))

  ⊑-beh : BEH → IsDiscrete X
  ⊑-beh {X} beh {x} {x'} = isoToEquiv (iso ≡⇒⊑ ⊑⇒≡ sec ret) .snd
    where
      ⊑⇒≡ : _⊑_ ⇒ _≡_
      ⊑⇒≡ x⊑x' = sym (x⊑x' .path₀) ∙ cong (x⊑x' .path) beh ∙ x⊑x' .path₁

      sec : section ≡⇒⊑ ⊑⇒≡
      sec x⊑x' i .path 𝕚 =
        ( sym (x⊑x' .path₀)
        ∙ cong (x⊑x' .path) (isContr→isProp (𝕀-isAlgorithmic beh) 𝕀0 𝕚)
        ) i
      sec x⊑x' i .path₀ = {!   !}
      sec x⊑x' i .path₁ = {!   !}

      ret : retract ≡⇒⊑ ⊑⇒≡
      ret x≡x' i = isSet𝒱 X x x' (⊑⇒≡ (≡⇒⊑ x≡x')) x≡x' i
