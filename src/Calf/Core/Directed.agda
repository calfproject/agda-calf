module Calf.Core.Directed where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.PathSplit
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma
open import Cubical.HITs.Join
open import Cubical.HITs.Localization
open import Relation.Binary using (_⇒_)
open import Relation.Binary.Definitions

opaque
  open import Cubical.Data.Unit

  𝟚 : Type
  𝟚 = Unit

  isSet𝟚 : isSet 𝟚
  isSet𝟚 = isSetUnit

  _≤𝟚_ : 𝟚 → 𝟚 → Type
  tt ≤𝟚 tt = Unit

  ≤𝟚-isProp : ∀ {i j} → isProp (i ≤𝟚 j)
  ≤𝟚-isProp = isContr→isProp isContrUnit

  ≤𝟚-refl : Reflexive _≤𝟚_
  ≤𝟚-refl = tt

  ≤𝟚-trans : Transitive _≤𝟚_
  ≤𝟚-trans _ _ = tt

  ≤𝟚-antisym : Antisymmetric _≡_ _≤𝟚_
  ≤𝟚-antisym = isContr→isProp isContrUnit

  0𝟚 1𝟚 : 𝟚
  0𝟚 = tt
  1𝟚 = tt

  0𝟚-minimum : Minimum _≤𝟚_ 0𝟚
  0𝟚-minimum _ = tt

  1𝟚-maximum : Maximum _≤𝟚_ 1𝟚
  1𝟚-maximum tt = tt

Δ² : Type
Δ² = Σ[ (𝕚 , 𝕛) ∈ 𝟚 × 𝟚 ] 𝕚 ≤𝟚 𝕛

Λ² : Type
Λ² = Σ[ (𝕚 , 𝕛) ∈ 𝟚 × 𝟚 ] join (𝕚 ≡ 0𝟚) (𝕛 ≡ 1𝟚)

ι : Λ² → Δ²
ι (𝕚𝕛 , inl 𝕚≡0𝟚) = 𝕚𝕛 , subst (_≤𝟚 _) (sym 𝕚≡0𝟚) (0𝟚-minimum _)
ι (𝕚𝕛 , inr 𝕛≡1𝟚) = 𝕚𝕛 , subst (_ ≤𝟚_) (sym 𝕛≡1𝟚) (1𝟚-maximum _)
ι (𝕚𝕛 , push _ _ i) .fst = 𝕚𝕛
ι (𝕚𝕛 , push 𝕚≡0𝟚 𝕛≡1𝟚 i) .snd = ≤𝟚-isProp (subst (_≤𝟚 _) (sym 𝕚≡0𝟚) (0𝟚-minimum _)) (subst (_ ≤𝟚_) (sym 𝕛≡1𝟚) (1𝟚-maximum _)) i


𝒱-family : (_ : Unit) → Λ² → Δ²
𝒱-family _ = ι

IsPreorder : Type → Type
IsPreorder = isLocal 𝒱-family

P : Type → Type
P = Localize 𝒱-family

private variable X Y : Type

isPropIsPreorder : isProp (IsPreorder X)
isPropIsPreorder = isPropΠ (λ _ → isPropIsPathSplitEquiv _)


module _ {A : Type} {S : A → Type} {T : A → Type} {F : ∀ α → S α → T α} where
  retract-local : {Z' Z : Type} (sec : Z' → Z) (ret : Z → Z') → retract sec ret → isLocal F Z → isLocal F Z'
  retract-local sec ret is-ret Z-local = {!   !}

module _ {X : Type} where

  record _⊑_ (x x' : X) : Type where
    field
      path : 𝟚 → X
      path₀ : path 0𝟚 ≡ x
      path₁ : path 1𝟚 ≡ x'
  open _⊑_ public

  ≡⇒⊑ : _≡_ ⇒ _⊑_
  ≡⇒⊑ {x = x} x≡x' .path _ = x
  ≡⇒⊑ {x = x} x≡x' .path₀ = refl
  ≡⇒⊑ {x = x} x≡x' .path₁ = x≡x'

  ⊑-refl : Reflexive _⊑_
  ⊑-refl = ≡⇒⊑ refl

  ⊑-trans : IsPreorder X → Transitive _⊑_
  ⊑-trans X-isPreorder {x} {x'} {x''} x⊑x' x'⊑x'' =
    record
      { path = λ 𝕚 → X-isPreorder _ .sec .fst aux ((𝕚 , 𝕚) , ≤𝟚-refl)
      ; path₀ =
          cong (X-isPreorder _ .sec .fst aux ∘ ((0𝟚 , 0𝟚) ,_)) (≤𝟚-isProp _ _)
          ∙ cong (_$ (0𝟚 , 0𝟚) , inl refl) (X-isPreorder _ .sec .snd aux)
          ∙ x⊑x' .path₀
      ; path₁ =
          cong (X-isPreorder _ .sec .fst aux ∘ ((1𝟚 , 1𝟚) ,_)) (≤𝟚-isProp _ _)
          ∙ cong (_$ (1𝟚 , 1𝟚) , inr refl) (X-isPreorder _ .sec .snd aux)
          ∙ x'⊑x'' .path₁
      }
    where
      open isPathSplitEquiv

      aux : Λ² → X
      aux ((𝕚 , 𝕛) , inl 𝕚≡0𝟚) = x⊑x' .path 𝕛
      aux ((𝕚 , 𝕛) , inr 𝕛≡1𝟚) = x'⊑x'' .path 𝕚
      aux ((𝕚 , 𝕛) , push 𝕚≡0𝟚 𝕛≡1𝟚 i) =
        ( cong (x⊑x' .path) 𝕛≡1𝟚
        ∙ x⊑x' .path₁
        ∙ sym (cong (x'⊑x'' .path) 𝕚≡0𝟚 ∙ x'⊑x'' .path₀))
        i

⊑-mono : (f : X → Y) {x x' : X} → x ⊑ x' → f x ⊑ f x'
⊑-mono f x⊑x' .path = f ∘ x⊑x' .path
⊑-mono f x⊑x' .path₀ = cong f (x⊑x' .path₀)
⊑-mono f x⊑x' .path₁ = cong f (x⊑x' .path₁)

⊑-funext : {Y : X → Type}
  → {f f' : (x : X) → Y x}
  → ((x : X) → f x ⊑ f' x)
  → f ⊑ f'
⊑-funext pointwise .path 𝕚 x = pointwise x .path 𝕚
⊑-funext pointwise .path₀ = funExt λ x → pointwise x .path₀
⊑-funext pointwise .path₁ = funExt λ x → pointwise x .path₁

record IsDiscrete (X : Type) : Type where
  field
    ortho : isLocal {A = Unit} {S = const 𝟚} (λ _ _ → tt) X
open IsDiscrete

IsDiscrete⊆IsPreorder : ⦃ _ : IsDiscrete X ⦄ → IsPreorder X
IsDiscrete⊆IsPreorder = {!   !}

IsDiscrete⇒isEquiv[≡⇒⊑] : ⦃ _ : IsDiscrete X ⦄ → {x x' : X} → isEquiv (≡⇒⊑ {X} {x} {x'})
IsDiscrete⇒isEquiv[≡⇒⊑] = {!   !}

BEH : Type
BEH = 0𝟚 ≡ 1𝟚

BEH-isProp : isProp BEH
BEH-isProp = isSet𝟚 0𝟚 1𝟚

𝟚-isAlgorithmic : BEH → isContr 𝟚
𝟚-isAlgorithmic beh .fst = 0𝟚
𝟚-isAlgorithmic beh .snd i =
  ≤𝟚-antisym
    (0𝟚-minimum _)
    (≤𝟚-trans (1𝟚-maximum _) (subst (_≤𝟚 0𝟚) beh ≤𝟚-refl))

⊑-beh : isSet X → BEH → IsDiscrete X
⊑-beh = {!   !}
-- ⊑'-beh beh .ortho g .fst .fst _ = g 0𝟚
-- ⊑'-beh beh .ortho g .fst .snd = funExt λ x → cong g (isContr→isProp (𝟚-isAlgorithmic beh) 0𝟚 x)
-- ⊑'-beh beh .ortho g .snd y i .fst _ = sym (cong (_$ 0𝟚) (y .snd)) i
-- ⊑'-beh {X} beh .ortho g .snd y i .snd j x = {!   !}

-- ⊑-beh : BEH → IsDiscrete X
-- ⊑-beh {X} = ⊑'-beh {val X , isSet𝒱 X}

--   -- ⊑-beh {X} beh {x} {x'} = {!   !}
--   -- isoToEquiv (iso ≡⇒⊑ ⊑⇒≡ sec ret) .snd
--   --   where
--   --     ⊑⇒≡ : _⊑_ ⇒ _≡_
--   --     ⊑⇒≡ x⊑x' = sym (x⊑x' .path₀) ∙ cong (x⊑x' .path) beh ∙ x⊑x' .path₁

--   --     sec : section ≡⇒⊑ ⊑⇒≡
--   --     sec x⊑x' i .path 𝕚 =
--   --       ( sym (x⊑x' .path₀)
--   --       ∙ cong (x⊑x' .path) (isContr→isProp (𝟚-isAlgorithmic beh) 0𝟚 𝕚)
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
      unfolding 𝟚

      ℕ-isDiscrete : IsDiscrete ℕ
      ℕ-isDiscrete = ⊑-beh isSetℕ refl

    Bool-isDiscrete : IsDiscrete Bool
    Bool-isDiscrete .ortho = retract-local inj prj is-retract (ℕ-isDiscrete .ortho)
      where
        inj : Bool → ℕ
        inj false = 0
        inj true = 1

        prj : ℕ → Bool
        prj zero = false
        prj (suc _) = true

        is-retract : retract inj prj
        is-retract false = refl
        is-retract true = refl


-- mylemma : IsDiscrete X → IsOrthogonal (const {B = Λ²} tt) (val X)
-- mylemma = {!    !}


record dhom {Y : X → Type} {x x' : X} (x⊑x' : x ⊑ x') (y : Y x) (y' : Y x') : Type where
  field
    path : (𝕚 : 𝟚) → Y (x⊑x' .path 𝕚)
    path₀ : PathP (λ i → Y (x⊑x' .path₀ i)) (path 0𝟚) y
    path₁ : PathP (λ i → Y (x⊑x' .path₁ i)) (path 1𝟚) y'

IsCovariant : (X → Type) → Type
IsCovariant {X} Y = {x x' : X} (x⊑x' : x ⊑ x') (y : Y x) → ∃![ y' ∈ Y x' ] dhom x⊑x' y y'

RS-8∙11 : {Y : X → Type} → IsPreorder X → IsCovariant Y → IsPreorder (Σ X Y)
RS-8∙11 = {!   !}
