module Calf.Value.Sum where

open import Calf.Core.Directed
open import Calf.Value
open import Cubical.Data.Sum renaming (inl to inj₁; inr to inj₂) public

open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence using (ua)
open import Cubical.Data.Bool
open import Calf.Value.Bool
open import Calf.Value.Sigma

isPreorder⊎ : isPreorder X → isPreorder Y → isPreorder (X ⊎ Y)
isPreorder⊎ isPreorderX isPreorderY =
  subst isPreorder
    (isoToPath lemma)
    (isPreorderΣ Boolₛ λ { false → isPreorderX ; true → isPreorderY })
  where
    open Iso

    lemma : Iso (Σ Bool (if_then Y else X)) (X ⊎ Y)
    lemma .fun (false , v) = inj₁ v
    lemma .fun (true , v) = inj₂ v
    lemma .inv (inj₁ x) = false , x
    lemma .inv (inj₂ y) = true , y
    lemma .rightInv (inj₁ x) = refl
    lemma .rightInv (inj₂ y) = refl
    lemma .leftInv (false , v) = refl
    lemma .leftInv (true , v) = refl
