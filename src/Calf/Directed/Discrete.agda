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
        (λ q → q .path , sym (q .path₀) , q .path₁)
        (λ (p , p₀ , p₁) → record { path = p ; path₀ = sym p₀ ; path₁ = p₁ })
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
