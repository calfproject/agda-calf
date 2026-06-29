module Calf.Directed.Set where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.PathSplit
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.HITs.S1
open import Cubical.HITs.Nullification

private variable X Y : Type

isS¹Null≡isSet : isNull (const {B = Unit} S¹) X ≡ isSet X
isS¹Null≡isSet {X} =
  hPropExt isPropIsNull isPropIsSet isNull→isSet isSet→isNull
  where
    isNull→isSet : isNull (const {B = Unit} S¹) X → isSet X
    isNull→isSet nullX =
      isOfHLevelΩ→isOfHLevel 0 λ x → isContr→isProp (isContrLoop x)
      where
        const-isEquiv : isEquiv (const {A = X} {B = S¹})
        const-isEquiv = toIsEquiv _ (nullX tt)

        X≃ΣLoop : X ≃ (Σ[ x ∈ X ] (x ≡ x))
        X≃ΣLoop =
          compEquiv (const {A = X} {B = S¹} , const-isEquiv) (isoToEquiv IsoFunSpaceS¹)

        fst-isEquiv : isEquiv (fst {A = X} {B = λ x → x ≡ x})
        fst-isEquiv = precomposesToId→Equiv fst (equivFun X≃ΣLoop) refl (snd X≃ΣLoop)

        isContrLoop : (x : X) → isContr (x ≡ x)
        isContrLoop x =
          isOfHLevelRespectEquiv 0
            (invEquiv (fiberProjEquiv X (λ y → y ≡ y) x))
            (fst-isEquiv .equiv-proof x)

    isSet→isNull : isSet X → isNull (const {B = Unit} S¹) X
    isSet→isNull setX _ = fromIsEquiv _ const-isEquiv
      where
        loopContr : (y : X) → isContr (y ≡ y)
        loopContr y = refl , λ p → setX y y refl p

        e : X ≃ (S¹ → X)
        e =
          compEquiv (invEquiv (Σ-contractSnd loopContr))
            (invEquiv (isoToEquiv IsoFunSpaceS¹))

        e≡ : equivFun e ≡ const {A = X} {B = S¹}
        e≡ = funExt λ x → funExt λ { base → refl ; (loop i) → refl }

        const-isEquiv : isEquiv (const {A = X} {B = S¹})
        const-isEquiv = subst isEquiv e≡ (e .snd)
