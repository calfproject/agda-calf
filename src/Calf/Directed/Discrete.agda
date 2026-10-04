module Calf.Directed.Discrete where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.PathSplit
open import Cubical.Foundations.Equiv.Properties
  using (isEquiv[f∘equivFunA≃B]→isEquiv[f])
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path using (symIso)
open import Cubical.Data.Bool
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.HITs.Localization

open import Calf.Core.Interval
open import Calf.Directed.Modality
open import Calf.Directed.Path
open import Calf.Directed.Thin
open import Calf.Directed.Transitive

private variable X Y : Type

isDiscrete : Type → Type
isDiscrete X = isLocal {A = Unit} (λ _ → terminal 𝟚) X

const-𝟚-≃ : isDiscrete X → X ≃ (𝟚 → X)
const-𝟚-≃ {X} isDiscreteX =
  compEquiv (invEquiv (UnitToType≃ X)) (_ , toIsEquiv _ (isDiscreteX tt))

isDiscrete→isEquiv[⊑-reflexive] : isDiscrete X → {x x' : X} → isEquiv (⊑-reflexive {X} {x} {x'})
isDiscrete→isEquiv[⊑-reflexive] {X} isDiscreteX {x} {x'} = equivIsEquiv ≡≃⊑
  where
    isContrP : isContr (Σ[ p ∈ (𝟚 → X) ] (p 0𝟚 ≡ x))
    isContrP = isOfHLevelRespectEquiv 0
      ( Σ[ y ∈ X ] (x ≡ y)
      ≃⟨ Σ-cong-equiv-fst (const-𝟚-≃ isDiscreteX) ⟩
        Σ[ p ∈ (𝟚 → X) ] (x ≡ p 0𝟚)
      ≃⟨ Σ-cong-equiv-snd (λ _ → isoToEquiv symIso) ⟩
        Σ[ p ∈ (𝟚 → X) ] (p 0𝟚 ≡ x)
      ■)
      (isContrSingl x)

    ≡≃⊑ : (x ≡ x') ≃ (x ⊑ x')
    ≡≃⊑ =
        (x ≡ x')
      ≃⟨ invEquiv (Σ-contractFst isContrP) ⟩
        Σ[ (p , p₀) ∈ (Σ[ p ∈ (𝟚 → X) ] (p 0𝟚 ≡ x)) ] (p 1𝟚 ≡ x')
      ≃⟨ Σ-assoc-≃ ⟩
        x ⊑ x'
      ■

isSet∧isDiscrete→isThin : isSet X → isDiscrete X → isThin X
isSet∧isDiscrete→isThin isSetX isDiscreteX x x' =
  isOfHLevelRespectEquiv 1 (⊑-reflexive , isDiscrete→isEquiv[⊑-reflexive] isDiscreteX) (isSetX x x')

isEquivEv→isEquivConst : (y₀ : Y)
  → isEquiv (λ (f : Y → X) → f y₀) → isEquiv (const {A = X} {B = Y})
isEquivEv→isEquivConst k₀ = composesToId→Equiv _ const refl

isLocalTerminal→isEquivConst : {A : Type} {S : A → Type}
  → isLocal (λ α → terminal (S α)) X → (α : A) → isEquiv (const {A = X} {B = S α})
isLocalTerminal→isEquivConst l α =
  equivIsEquiv (compEquiv (invEquiv (UnitToType≃ _)) (_ , toIsEquiv _ (l α)))

null[Unit] : isEquiv (const {A = X} {B = Unit})
null[Unit] {X} = isEquivEv→isEquivConst tt (equivIsEquiv (UnitToType≃ X))

null[𝟚] : isDiscrete X → isEquiv (const {A = X} {B = 𝟚})
null[𝟚] isDiscreteX = isLocalTerminal→isEquivConst isDiscreteX tt

null[Λ²] : isDiscrete X → isEquiv (const {A = X} {B = Λ²})
null[Λ²] {X} isDiscreteX =
  isEquivEv→isEquivConst (inl 0𝟚) (precomposesToId→Equiv _ (chain .fst) refl (chain .snd))
  where
    chain : X ≃ (Λ² → X)
    chain =
        X
      ≃⟨ invEquiv (Σ-contractSnd λ _ → isContrSingl _) ⟩
        Σ[ a ∈ X ] Σ[ b ∈ X ] (a ≡ b)
      ≃⟨ Σ-cong-equiv-snd (λ _ → Σ-cong-equiv-fst (const-𝟚-≃ isDiscreteX)) ⟩
        Σ[ a ∈ X ] Σ[ q ∈ (𝟚 → X) ] (a ≡ q 0𝟚)
      ≃⟨ Σ-cong-equiv-fst (const-𝟚-≃ isDiscreteX) ⟩
        Σ[ p ∈ (𝟚 → X) ] Σ[ q ∈ (𝟚 → X) ] (p 1𝟚 ≡ q 0𝟚)
      ≃⟨ invEquiv Λ²-elim≃ ⟩
        (Λ² → X)
      ■

null[𝕊Unit] : isDiscrete X → isEquiv (const {A = X} {B = 𝕊 Unit})
null[𝕊Unit] {X} isDiscreteX =
  isEquivEv→isEquivConst (inr false) (precomposesToId→Equiv _ (chain .fst) refl (chain .snd))
  where
    chain : X ≃ (𝕊 Unit → X)
    chain =
        X
      ≃⟨ invEquiv (Σ-contractSnd λ _ → isContrSingl _) ⟩
        Σ[ x ∈ X ] Σ[ y ∈ X ] (x ≡ y)
      ≃⟨ Σ-cong-equiv-snd (λ _ → Σ-cong-equiv-snd (λ _ →
           ⊑-reflexive , isDiscrete→isEquiv[⊑-reflexive] isDiscreteX)) ⟩
        Σ[ x ∈ X ] Σ[ y ∈ X ] (x ⊑ y)
      ≃⟨ Σ-cong-equiv-snd (λ _ → Σ-cong-equiv-snd (λ _ → invEquiv (UnitToType≃ _))) ⟩
        Σ[ x ∈ X ] Σ[ y ∈ X ] (Unit → x ⊑ y)
      ≃⟨ invEquiv (𝕊-elim≃ Unit) ⟩
        (𝕊 Unit → X)
      ■

null[Δ²] : isDiscrete X → isEquiv (const {A = X} {B = Δ²})
null[Δ²] {X} isDiscreteX = isoToIsEquiv const-Δ²-iso
  where
  ⊑⇒≡ : {x y : X} → x ⊑ y → x ≡ y
  ⊑⇒≡ = invEq (_ , isDiscrete→isEquiv[⊑-reflexive] isDiscreteX)

  initial-Δ² : (d : Δ²) → (0𝟚 , 0𝟚 , ≤𝟚-refl) ⊑ d
  initial-Δ² (i , j , p) =
      (λ t → (i ∧𝟚 t) , (j ∧𝟚 t) , ∧𝟚-mono p ≤𝟚-refl)
    , Δ²-ext (∧𝟚-zero i) (∧𝟚-zero j)
    , Δ²-ext (∧𝟚-one i) (∧𝟚-one j)

  const-Δ²-iso : Iso X (Δ² → X)
  const-Δ²-iso .Iso.fun = const
  const-Δ²-iso .Iso.inv f = f (0𝟚 , 0𝟚 , ≤𝟚-refl)
  const-Δ²-iso .Iso.rightInv f = funExt λ d → ⊑⇒≡ (mono f (initial-Δ² d))
  const-Δ²-iso .Iso.leftInv x = refl

isDiscrete→isPathTransitive : isDiscrete X → isPathTransitive X
isDiscrete→isPathTransitive isDiscreteX _ = fromIsEquiv _
  (isEquiv[f∘equivFunA≃B]→isEquiv[f] (_∘ ι-horn)
    (const , null[Δ²] isDiscreteX) (null[Λ²] isDiscreteX))

opaque
  isSet∧isDiscrete→isPreorder : isSet X → isDiscrete X → isPreorder X
  isSet∧isDiscrete→isPreorder isSetX isDiscreteX =
    isSet∧isThin∧isPathTransitive→isPreorder isSetX
      (isSet∧isDiscrete→isThin isSetX isDiscreteX)
      (isDiscrete→isPathTransitive isDiscreteX)

opaque
  unfolding Fᴾ

  isSet∧isDiscrete→nullᴾ : isSet X → isDiscrete X
    → (α : Requirements) → isEquiv (const {A = X} {B = Tᴾ α})
  isSet∧isDiscrete→nullᴾ isSetX isDiscreteX tran = null[Δ²] isDiscreteX
  isSet∧isDiscrete→nullᴾ isSetX isDiscreteX thin = null[𝕊Unit] isDiscreteX
  isSet∧isDiscrete→nullᴾ isSetX isDiscreteX hset = null[Unit]
