module Calf.Directed.Set where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.PathSplit
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Unit
open import Cubical.HITs.Localization
open import Cubical.HITs.S1

private variable X : Type

isS¹Local≃isSet : isLocal {A = Unit} (const (terminal S¹)) X ≃ isSet X
isS¹Local≃isSet {X} =
  propBiimpl→Equiv
    (isPropΠ λ _ → isPropIsPathSplitEquiv _)
    isPropIsSet
    isLocal→isSet
    isSet→isLocal
  where
  isLocal→isSet : isLocal {A = Unit} (const (terminal S¹)) X → isSet X
  isLocal→isSet localX = isOfHLevelΩ→isOfHLevel 0 loops-isProp
    where
    constant-loops : X ≃ (Σ[ x ∈ X ] (x ≡ x))
    constant-loops =
        X
      ≃⟨ invEquiv (UnitToType≃ X) ⟩
        (Unit → X)
      ≃⟨ _ , toIsEquiv _ (localX tt) ⟩
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

  isSet→isLocal : isSet X → isLocal {A = Unit} (const (terminal S¹)) X
  isSet→isLocal setX _ = fromIsEquiv (_∘ terminal S¹) (isoToIsEquiv S¹→XIso)
    where
    S¹→XIso : Iso (Unit → X) (S¹ → X)
    S¹→XIso .Iso.fun f = f ∘ terminal S¹
    S¹→XIso .Iso.inv f _ = f base
    S¹→XIso .Iso.rightInv f = funExt (toPropElim (λ _ → setX _ _) refl)
    S¹→XIso .Iso.leftInv f = funExt λ { tt → refl }
