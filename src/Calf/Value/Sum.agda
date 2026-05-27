module Calf.Value.Sum where

open import Calf.Value
open import Data.Sum public

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence using (ua)
open import Cubical.Data.Bool
open import Calf.Value.Bool
open import Calf.Value.Sigma

_+ᵛ_ : 𝒱 → 𝒱 → 𝒱
(X +ᵛ Y) .val = val X ⊎ val Y
(X +ᵛ Y) .is-preorder =
  subst isPreorder
    (ua (isoToEquiv lemma))
    (Σᵛ Boolᵛ (if_then Y else X) .is-preorder)
  where
    lemma : Iso (Σ Bool (val ∘ (if_then Y else X))) (val X ⊎ val Y)
    lemma .Iso.fun (false , v) = inj₁ v
    lemma .Iso.fun (true , v) = inj₂ v
    lemma .Iso.inv (inj₁ x) = false , x
    lemma .Iso.inv (inj₂ y) = true , y
    lemma .Iso.rightInv (inj₁ x) = refl
    lemma .Iso.rightInv (inj₂ y) = refl
    lemma .Iso.leftInv (false , v) = refl
    lemma .Iso.leftInv (true , v) = refl
