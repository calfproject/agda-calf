module Calf.Directed.Set where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.PathSplit
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Data.Unit
open import Cubical.HITs.Nullification
open import Cubical.HITs.S1

private variable X : Type

isS¹Null≡isSet : isNull (const {B = Unit} S¹) X ≡ isSet X
isS¹Null≡isSet {X} = 
  hPropExt isPropIsNull isPropIsSet isNull→isSet isSet→isNull
  where
  isNull→isSet : isNull (const {B = Unit} S¹) X → isSet X
  isNull→isSet nullX = isOfHLevelΩ→isOfHLevel 0 loops-isProp
    where
    constant-loops : X ≃ (Σ[ x ∈ X ] (x ≡ x))
    constant-loops =
        X 
      ≃⟨ _ , toIsEquiv _ (nullX tt) ⟩
        (S¹ → X) 
      ≃⟨ isoToEquiv IsoFunSpaceS¹ ⟩
        Σ[ x ∈ X ] (x ≡ x)
      ■

    K : (x : X) (p : x ≡ x) → p ≡ refl
    K x p = J (λ (y , q) _ → q ≡ refl) refl constant-loop-path
      where
      constant-loop-path : (invEq constant-loops (x , p) , refl) ≡ (x , p)
      constant-loop-path = secEq constant-loops (x , p)

    loops-isProp : (x : X) → isProp (x ≡ x) 
    loops-isProp x p q = K x p ∙ sym (K x q)

  isSet→isNull : isSet X → isNull (const {B = Unit} S¹) X
  isSet→isNull setX _ = fromIsEquiv (λ x _ → x) (isoToIsEquiv S¹→XIso)
    where
    S¹→XIso : Iso X (S¹ → X)
    S¹→XIso .Iso.fun x _ = x
    S¹→XIso .Iso.inv f = f base
    S¹→XIso .Iso.rightInv f = funExt (toPropElim (λ _ → setX _ _) refl)
    S¹→XIso .Iso.leftInv x = refl
