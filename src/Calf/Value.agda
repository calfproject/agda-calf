module Calf.Value where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma
open import Relation.Unary using (_⊆_)
open import Relation.Binary using (_⇒_)
open import Relation.Binary.Definitions

record IsOrthogonal {X Y : Type} (f : X → Y) (Z : Type) : Type where
  field
    ortho : (g : X → Z) → ∃![ g' ∈ (Y → Z) ] g' ∘ f ≡ g
open IsOrthogonal public


module _ where
  retract-orthogonal : ∀ {X Y Z' Z} {f : X → Y} (sec : Z' → Z) (ret : Z → Z') → retract sec ret → IsOrthogonal f Z → IsOrthogonal f Z'
  retract-orthogonal sec ret is-ret Z-ortho .ortho g =
    let (([sec∘g]' , [sec∘g]'-lift) , [sec∘g]'-unique) = Z-ortho .ortho (sec ∘ g) in
    (ret ∘ [sec∘g]' , cong (ret ∘_) [sec∘g]'-lift ∙ cong (_∘ g) (funExt is-ret) ∙ ∘-idʳ g) ,
    λ (h , h-lift) → let foo = [sec∘g]'-unique (sec ∘ h , cong (sec ∘_) h-lift) in {!   !}



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

P : Type → Type
P = {!   !}

record _⊑'_ {X : Type} (x x' : X) : Type where
  field
    path : 𝕀 → X
    path₀ : path 𝕀0 ≡ x
    path₁ : path 𝕀1 ≡ x'
open _⊑'_ public

_⊑_ : val X → val X → Type
x ⊑ x' = x ⊑' x'

⊑-syntax : val X → val X → Type
⊑-syntax {X} = _⊑_ {X}

syntax ⊑-syntax {X} x x' = x ⊑[ X ] x'

≡⇒⊑' : {X : Type} → _≡_ ⇒ _⊑'_ {X}
≡⇒⊑' {x = x} x≡x' .path _ = x
≡⇒⊑' {x = x} x≡x' .path₀ = refl
≡⇒⊑' {x = x} x≡x' .path₁ = x≡x'

≡⇒⊑ : _≡_ ⇒ _⊑_ {X}
≡⇒⊑ = ≡⇒⊑'

⊑'-refl : {X : Type} → Reflexive (_⊑'_ {X})
⊑'-refl = ≡⇒⊑' refl

⊑-refl : Reflexive (_⊑_ {X})
⊑-refl = ⊑'-refl

⊑'-mono : {X Y : Type} (f : X → Y) {x x' : X} → x ⊑' x' → f x ⊑' f x'
⊑'-mono f x⊑x' .path = f ∘ x⊑x' .path
⊑'-mono f x⊑x' .path₀ = cong f (x⊑x' .path₀)
⊑'-mono f x⊑x' .path₁ = cong f (x⊑x' .path₁)

⊑-mono : (f : val X → val Y) {x x' : val X} → x ⊑[ X ] x' → f x ⊑[ Y ] f x'
⊑-mono = ⊑'-mono

⊑-trans : Transitive (_⊑_ {X})
⊑-trans {X} {x} {x'} {x''} x⊑x' x'⊑x'' =
  record
    { path = λ 𝕚 → X .isPreorder .ortho aux .fst .fst (𝕚 , 𝕚 , ≤𝕀-refl)
    ; path₀ =
        cong (X .isPreorder .ortho aux .fst .fst ∘ (𝕀0 ,_) ∘ (𝕀0 ,_)) (≤𝕀-isProp _ _)
        ∙ cong (_$ inj₀ 𝕀0) (X .isPreorder .ortho aux .fst .snd)
        ∙ x⊑x' .path₀
    ; path₁ =
        cong (X .isPreorder .ortho aux .fst .fst ∘ (𝕀1 ,_) ∘ (𝕀1 ,_)) (≤𝕀-isProp _ _)
        ∙ cong (_$ inj₁ 𝕀1) (X .isPreorder .ortho aux .fst .snd)
        ∙ x'⊑x'' .path₁
    }
  where
    aux : 𝕀∨𝕀 → val X
    aux (inj₀ 𝕚) = x⊑x' .path 𝕚
    aux (inj₁ 𝕚) = x'⊑x'' .path 𝕚
    aux (law i) = (x⊑x' .path₁ ∙ sym (x'⊑x'' .path₀)) i

-- -- ⊑-antisym : Antisymmetric _≡_ (_⊑_ {X})
-- -- ⊑-antisym {X} x⊑x' x'⊑x = {!    !}

IsDiscrete' : Type → Type
IsDiscrete' = IsOrthogonal (const {B = 𝕀} tt)

IsDiscrete : 𝒱 → Type
IsDiscrete = IsDiscrete' ∘ val

IsDiscrete'⊆IsPreorder : {X : Type} ⦃ _ : IsDiscrete' X ⦄ → IsPreorder X
IsDiscrete'⊆IsPreorder = {!   !}

IsDiscrete⇒isEquiv[≡⇒⊑] : ⦃ _ : IsDiscrete X ⦄ → {x x' : val X} → isEquiv (≡⇒⊑ {X} {x} {x'})
IsDiscrete⇒isEquiv[≡⇒⊑] = {!   !}

fromProp : {X : Type} → isProp X → 𝒱
fromProp {X} X-isProp .val = X
fromProp {X} X-isProp .isPreorder .ortho g =
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

  ⊑'-beh : {X : hSet ℓ-zero} → BEH → IsDiscrete' ⟨ X ⟩
  ⊑'-beh beh .ortho g .fst .fst _ = g 𝕀0
  ⊑'-beh beh .ortho g .fst .snd = funExt λ x → cong g (isContr→isProp (𝕀-isAlgorithmic beh) 𝕀0 x)
  ⊑'-beh beh .ortho g .snd y i .fst _ = sym (cong (_$ 𝕀0) (y .snd)) i
  ⊑'-beh {X} beh .ortho g .snd y i .snd j x = {!   !}

  ⊑-beh : BEH → IsDiscrete X
  ⊑-beh {X} = ⊑'-beh {val X , isSet𝒱 X}

--   -- ⊑-beh {X} beh {x} {x'} = {!   !}
--   -- isoToEquiv (iso ≡⇒⊑ ⊑⇒≡ sec ret) .snd
--   --   where
--   --     ⊑⇒≡ : _⊑_ ⇒ _≡_
--   --     ⊑⇒≡ x⊑x' = sym (x⊑x' .path₀) ∙ cong (x⊑x' .path) beh ∙ x⊑x' .path₁

--   --     sec : section ≡⇒⊑ ⊑⇒≡
--   --     sec x⊑x' i .path 𝕚 =
--   --       ( sym (x⊑x' .path₀)
--   --       ∙ cong (x⊑x' .path) (isContr→isProp (𝕀-isAlgorithmic beh) 𝕀0 𝕚)
--   --       ) i
--   --     sec x⊑x' i .path₀ = {!   !}
--   --     sec x⊑x' i .path₁ = {!   !}

--   --     ret : retract ≡⇒⊑ ⊑⇒≡
--   --     ret x≡x' i = isSet𝒱 X x x' (⊑⇒≡ (≡⇒⊑ x≡x')) x≡x' i

module _ where
  open import Cubical.Data.Nat
  open import Cubical.Data.Bool

  instance
    opaque
      unfolding 𝕀

      ℕ-isDiscrete' : IsDiscrete' ℕ
      ℕ-isDiscrete' = ⊑'-beh {ℕ , isSetℕ} refl

    Bool-isDiscrete' : IsDiscrete' Bool
    Bool-isDiscrete' = retract-orthogonal sec ret is-retract ℕ-isDiscrete'
      where
        sec : Bool → ℕ
        sec false = 0
        sec true = 1

        ret : ℕ → Bool
        ret zero = false
        ret (suc _) = true

        is-retract : retract sec ret
        is-retract false = refl
        is-retract true = refl


mylemma : IsDiscrete X → IsOrthogonal (const {B = 𝕀∨𝕀} tt) (val X)
mylemma = {!    !}
