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

private variable X Y : Type

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


opaque
  𝒱-family-A : Type
  𝒱-family-A = Unit

  𝒱-family-S : 𝒱-family-A → Type
  𝒱-family-S _ = Λ²

  𝒱-family-T : 𝒱-family-A → Type
  𝒱-family-T _ = Δ²

  𝒱-family : (α : 𝒱-family-A) → 𝒱-family-S α → 𝒱-family-T α
  𝒱-family _ = ι

isPreorder : Type → Type
isPreorder = isLocal 𝒱-family

opaque
  P : Type → Type
  P = Localize 𝒱-family

  ηᴾ : X → P X
  ηᴾ = ∣_∣

  isPreorder-P : isPreorder (P X)
  isPreorder-P = isLocal-Localize 𝒱-family _

  isPropIsPreorder : isProp (isPreorder X)
  isPropIsPreorder = isPropΠ (λ _ → isPropIsPathSplitEquiv _)

open isPathSplitEquiv public

module _
  {A : Type} {S : A → Type} {T : A → Type} {F : ∀ α → S α → T α}
  {Z' Z : Type} (Z'→Z : Z' → Z) (Z→Z' : Z → Z')
  (Z'-isSet : isSet Z')
  (Z◃Z' : retract Z'→Z Z→Z')
  where

  retract-local : isLocal F Z → isLocal F Z'
  retract-local Z-local α .sec .fst S→Z' t = Z→Z' (Z-local α .sec .fst (Z'→Z ∘ S→Z') t)
  retract-local Z-local α .sec .snd S→Z' =
      (λ x → Z→Z' (Z-local α .sec .fst (λ x₁ → Z'→Z (S→Z' x₁)) (F α x)))
    ≡⟨ cong (Z→Z' ∘_) (Z-local α .sec .snd (Z'→Z ∘ S→Z')) ⟩
      (Z→Z' ∘ Z'→Z) ∘ S→Z'
    ≡⟨ cong (_∘ S→Z') (funExt Z◃Z') ⟩
      S→Z'
    ∎
  retract-local Z-local α .secCong T→Z'₁ T→Z'₂ .fst h =
      T→Z'₁
    ≡⟨ sym (cong (_∘ T→Z'₁) (funExt Z◃Z')) ⟩
      (Z→Z' ∘ Z'→Z) ∘ T→Z'₁
    ≡⟨ cong (Z→Z' ∘_) (Z-local α .secCong (Z'→Z ∘ T→Z'₁) (Z'→Z ∘ T→Z'₂) .fst (cong (Z'→Z ∘_) h)) ⟩
      (Z→Z' ∘ Z'→Z) ∘ T→Z'₂
    ≡⟨ cong (_∘ T→Z'₂) (funExt Z◃Z') ⟩
      T→Z'₂
    ∎
  retract-local Z-local α .secCong T→Z'₁ T→Z'₂ .snd h = isSet→ Z'-isSet _ _ _ h

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

  opaque
    unfolding 𝒱-family

    ⊑-trans : isPreorder X → Transitive _⊑_
    ⊑-trans X-is-preorder {x} {x'} {x''} x⊑x' x'⊑x'' =
      record
        { path = λ 𝕚 → X-is-preorder _ .sec .fst aux ((𝕚 , 𝕚) , ≤𝟚-refl)
        ; path₀ =
            cong (X-is-preorder _ .sec .fst aux ∘ ((0𝟚 , 0𝟚) ,_)) (≤𝟚-isProp _ _)
            ∙ cong (_$ (0𝟚 , 0𝟚) , inl refl) (X-is-preorder _ .sec .snd aux)
            ∙ x⊑x' .path₀
        ; path₁ =
            cong (X-is-preorder _ .sec .fst aux ∘ ((1𝟚 , 1𝟚) ,_)) (≤𝟚-isProp _ _)
            ∙ cong (_$ (1𝟚 , 1𝟚) , inr refl) (X-is-preorder _ .sec .snd aux)
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

record isDiscrete (X : Type) : Type where
  field
    is-discrete : isLocal {A = Unit} {S = const 𝟚} (λ _ _ → tt) X
open isDiscrete public

opaque
  unfolding 𝒱-family

  isDiscrete→isPreorder : ⦃ _ : isDiscrete X ⦄ → isPreorder X
  isDiscrete→isPreorder {X} ⦃ X-discrete ⦄ α .sec .fst S→X (𝕚𝕛 , p) = S→X (𝕚𝕛 , {!   !}) -- X-discrete .is-discrete _ .sec .fst (λ 𝕚 → S→X ({!   !} , {!   !})) _
  isDiscrete→isPreorder {X} ⦃ X-discrete ⦄ α .sec .snd b = {! X-discrete .is-discrete _ .sec .fst  !}
  isDiscrete→isPreorder {X} ⦃ X-discrete ⦄ α .secCong = {!   !}

-- isDiscrete→isEquiv[≡⇒⊑] : ⦃ _ : isDiscrete X ⦄ → {x x' : X} → isEquiv (≡⇒⊑ {X} {x} {x'})
-- isDiscrete→isEquiv[≡⇒⊑] = {!   !}

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

⊑-beh : BEH → isDiscrete X
⊑-beh beh .is-discrete _ .sec .fst f _ = f 0𝟚
⊑-beh beh .is-discrete _ .sec .snd f =
  funExt (cong (f $_) ∘ isContr→isProp (𝟚-isAlgorithmic beh) 0𝟚)
⊑-beh beh .is-discrete _ .secCong g g' .fst p = funExt λ _ → cong (_$ 0𝟚) p
⊑-beh beh .is-discrete _ .secCong g g' .snd p i j 𝕚 =
  p j (isContr→isProp (𝟚-isAlgorithmic beh) 0𝟚 𝕚 i)

module _ where
  open import Cubical.Data.Nat
  open import Cubical.Data.Bool

  instance
    opaque
      unfolding 𝟚

      ℕ-isDiscrete : isDiscrete ℕ
      ℕ-isDiscrete = ⊑-beh refl

    Bool-isDiscrete : isDiscrete Bool
    Bool-isDiscrete .is-discrete = retract-local inj prj isSetBool is-retract (ℕ-isDiscrete .is-discrete)
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


-- mylemma : isDiscrete X → IsOrthogonal (const {B = Λ²} tt) (val X)
-- mylemma = {!    !}


-- record dhom {Y : X → Type} {x x' : X} (x⊑x' : x ⊑ x') (y : Y x) (y' : Y x') : Type where
--   field
--     path : (𝕚 : 𝟚) → Y (x⊑x' .path 𝕚)
--     path₀ : PathP (λ i → Y (x⊑x' .path₀ i)) (path 0𝟚) y
--     path₁ : PathP (λ i → Y (x⊑x' .path₁ i)) (path 1𝟚) y'

-- isCovariant : (X → Type) → Type
-- isCovariant {X} Y = {x x' : X} (x⊑x' : x ⊑ x') (y : Y x) → ∃![ y' ∈ Y x' ] dhom x⊑x' y y'
