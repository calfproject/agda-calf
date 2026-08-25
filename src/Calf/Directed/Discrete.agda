module Calf.Directed.Discrete where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Fiberwise
open import Cubical.Foundations.Equiv.PathSplit
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.HITs.Localization
open import Cubical.Data.Bool
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.HITs.S1

open import Calf.Core.Interval
open import Calf.Directed.Transitive
open import Calf.Directed.Path
open import Calf.Directed.Thin
open import Calf.Directed.Modality
open import Calf.Directed.Set

private variable X Y : Type

isDiscrete : Type → Type
isDiscrete X = isLocal {A = Unit} (λ _ → terminal 𝟚) X

isDiscrete→isEquiv[≡⇒⊑] : isDiscrete X → {x x' : X} → isEquiv (≡⇒⊑ {X} {x} {x'})
isDiscrete→isEquiv[≡⇒⊑] {X} isDiscreteX {x} {x'} = equivIsEquiv ≡≃⊑
  where
    discreteness : X ≃ (𝟚 → X)
    discreteness = compEquiv (invEquiv (UnitToType≃ X)) (_ , toIsEquiv _ (isDiscreteX tt))

    isContrP : isContr (Σ[ p ∈ (𝟚 → X) ] (x ≡ p 0𝟚))
    isContrP = isOfHLevelRespectEquiv 0 (Σ-cong-equiv-fst discreteness) (isContrSingl x)

    ⊑≃Σ : (x ⊑ x') ≃ (Σ[ p ∈ (𝟚 → X) ] ((x ≡ p 0𝟚) × (p 1𝟚 ≡ x')))
    ⊑≃Σ =
      isoToEquiv $
      iso
        (λ q → path q , sym (path₀ q) , path₁ q)
        (λ (p , p₀ , p₁) → p , sym p₀ , p₁)
        (λ _ → refl)
        (λ _ → refl)

    ≡≃⊑ : (x ≡ x') ≃ (x ⊑ x')
    ≡≃⊑ =
      compEquiv (invEquiv (Σ-contractFst isContrP)) $
      compEquiv Σ-assoc-≃ $
      invEquiv ⊑≃Σ

isSet∧isDiscrete→isThin : isSet X → isDiscrete X → isThin X
isSet∧isDiscrete→isThin isSetX isDiscreteX x x' =
  isOfHLevelRespectEquiv 1 (≡⇒⊑ , isDiscrete→isEquiv[≡⇒⊑] isDiscreteX) (isSetX x x')

opaque
  unfolding Fᴾ

  isSet∧isDiscrete→isPreorder : isSet X → isDiscrete X → isPreorder X
  isSet∧isDiscrete→isPreorder {X} isSetX isDiscreteX transitive =
    isThin∧Transitive[⊑]→isPathTransitive
      (isSet∧isDiscrete→isThin isSetX isDiscreteX)
      (λ x⊑x' x'⊑x'' → ≡⇒⊑ (⊑⇒≡ x⊑x' ∙ ⊑⇒≡ x'⊑x''))
      _
    where
      ⊑⇒≡ : {x x' : X} → x ⊑ x' → x ≡ x'
      ⊑⇒≡ {x} {x'} = invEq (≡⇒⊑ , isDiscrete→isEquiv[≡⇒⊑] isDiscreteX)
  isSet∧isDiscrete→isPreorder isSetX isDiscreteX thin =
    transport (sym isBoundarySeparated≡isThin) (isSet∧isDiscrete→isThin isSetX isDiscreteX) _
  isSet∧isDiscrete→isPreorder {X} isSetX isDiscreteX hset =
    fromIsEquiv _ $ equivIsEquiv $
    compEquiv (UnitToType≃ _) (_ , toIsEquiv _ (transport (sym isS¹Null≡isSet) isSetX _))

private
  diag≃ : X ≃ (Σ[ (x , x') ∈ X × X ] (x ≡ x'))
  diag≃ = isoToEquiv (iso
    (λ x → (x , x) , refl)
    (λ ((x , _) , _) → x)
    (λ ((x , x') , p) i → (x , p i) , λ j → p (i ∧ j))
    (λ _ → refl))

  unitConst≃ : (A : Type) → A ≃ (Unit → A)
  unitConst≃ A = isoToEquiv (iso const (λ f → f tt) (λ _ → refl) (λ _ → refl))

null[Unit] : isEquiv (const {A = X} {B = Unit})
null[Unit] {X} = equivIsEquiv (unitConst≃ X)

null[𝕊Unit] : isDiscrete X → isEquiv (const {A = X} {B = 𝕊 Unit})
null[𝕊Unit] {X} isDiscreteX = subst isEquiv chain≡const (equivIsEquiv chain)
  where
    chain : X ≃ (𝕊 Unit → X)
    chain =
        X
      ≃⟨ diag≃ ⟩
        Σ[ p ∈ X × X ] (fst p ≡ snd p)
      ≃⟨ Σ-cong-equiv-snd (λ _ → ≡⇒⊑ , isDiscrete→isEquiv[≡⇒⊑] isDiscreteX) ⟩
        Σ[ p ∈ X × X ] (fst p ⊑ snd p)
      ≃⟨ Σ-cong-equiv-snd (λ _ → unitConst≃ _) ⟩
        Σ[ p ∈ X × X ] (Unit → fst p ⊑ snd p)
      ≃⟨ isoToEquiv (invIso (𝕊-elim Unit)) ⟩
        (𝕊 Unit → X)
      ■

    chain≡const : chain .fst ≡ const
    chain≡const = funExt λ x → funExt λ
      { (inl (y , 𝕚)) → refl
      ; (inr false) → refl
      ; (inr true) → refl
      ; (push (y , false) j) → refl
      ; (push (y , true) j) → refl
      }

null[𝟚] : isDiscrete X → isEquiv (const {A = X} {B = 𝟚})
null[𝟚] {X} isDiscreteX =
  subst isEquiv
    (funExt λ x → funExt λ _ → secEq (UnitToType≃ X) x)
    (compEquiv (invEquiv (UnitToType≃ X)) (_ , toIsEquiv _ (isDiscreteX tt)) .snd)

null[Λ²] : isDiscrete X → isEquiv (const {A = X} {B = Λ²})
null[Λ²] {X} isDiscreteX = subst isEquiv chain≡const (chain .snd)
  where
    constₚ : X ≃ (𝟚 → X)
    constₚ = const , null[𝟚] isDiscreteX

    diag2 : X ≃ (Σ[ a ∈ X ] Σ[ b ∈ X ] (a ≡ b))
    diag2 = isoToEquiv (iso
      (λ a → a , a , refl)
      (λ (a , _ , _) → a)
      (λ (a , b , p) i → a , p i , λ j → p (i ∧ j))
      (λ _ → refl))

    chain : X ≃ (Λ² → X)
    chain =
        X
      ≃⟨ diag2 ⟩
        Σ[ a ∈ X ] Σ[ b ∈ X ] (a ≡ b)
      ≃⟨ Σ-cong-equiv-snd (λ _ → Σ-cong-equiv-fst constₚ) ⟩
        Σ[ a ∈ X ] Σ[ q ∈ (𝟚 → X) ] (a ≡ q 0𝟚)
      ≃⟨ Σ-cong-equiv-fst constₚ ⟩
        Σ[ p ∈ (𝟚 → X) ] Σ[ q ∈ (𝟚 → X) ] (p 1𝟚 ≡ q 0𝟚)
      ≃⟨ isoToEquiv (invIso Λ²-elim) ⟩
        (Λ² → X)
      ■

    chain≡const : equivFun chain ≡ const
    chain≡const = funExt λ x → funExt λ
      { (inl 𝕚) → refl
      ; (inr 𝕚) → refl
      ; (push tt j) → refl
      }

-- A map `Δ² → X` is a horn plus a composite edge; over a discrete *set* the horn
-- collapses (null[Λ²]) and the composite edge `x ⊑ x` is contractible.
null[Δ²] : isSet X → isDiscrete X → isEquiv (const {A = X} {B = Δ²})
null[Δ²] {X} isSetX isDiscreteX = subst isEquiv chain≡const (chain .snd)
  where
    contr⊑ : (x : X) → isContr (x ⊑ x)
    contr⊑ x =
      isOfHLevelRespectEquiv 0
        (≡⇒⊑ , isDiscrete→isEquiv[≡⇒⊑] isDiscreteX)
        (refl , isSetX x x refl)

    constΣ⊑ : X ≃ (Σ[ x ∈ X ] (x ⊑ x))
    constΣ⊑ = isoToEquiv (iso
      (λ x → x , ≡⇒⊑ refl)
      fst
      (λ (x , e) i → x , isContr→isProp (contr⊑ x) (≡⇒⊑ refl) e i)
      (λ _ → refl))

    chain : X ≃ (Δ² → X)
    chain =
      X
        ≃⟨ constΣ⊑ ⟩
      Σ[ x ∈ X ] (x ⊑ x)
        ≃⟨ Σ-cong-equiv-fst (const , null[Λ²] isDiscreteX) ⟩
      Σ[ h ∈ (Λ² → X) ] (h (inl 0𝟚) ⊑ h (inr 1𝟚))
        ≃⟨ isoToEquiv (invIso Δ²-elim) ⟩
      (Δ² → X) ■

    chain≡const : chain .fst ≡ const
    chain≡const = funExt λ x → funExt λ
      { (inl b) → refl
      ; (inr 𝕚) → refl
      ; (push false i) → refl
      ; (push true i) → refl }
