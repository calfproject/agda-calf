module Calf.Value.List where

open import Calf.Value
open import Cubical.Data.List
  using (List; []; _∷_; foldr; _++_; [_]; length)
  renaming (rev to reverse)
  public
open import Cubical.Data.List using (isOfHLevelList)

open import Calf.Core.Directed
open import Calf.Value.Nat
open import Calf.Value.Product
open import Calf.Value.Sigma
open import Calf.Value.Unit
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

isSetList : isSet X → isSet (List X)
isSetList = isOfHLevelList 0

module _ {X : 𝒱} where
  private
    Vec : ℕ → Type
    Vec n = iter n (X ×_) Unit

    fwd : Σ ℕ Vec → List X
    fwd (zero , tt) = []
    fwd (suc n , x , xs) = x ∷ fwd (n , xs)

    bwd : List X → Σ ℕ Vec
    bwd [] = 0 , tt
    bwd (x ∷ xs) = let (n , v) = bwd xs in suc n , x , v

    fwd-bwd : section fwd bwd
    fwd-bwd [] = refl
    fwd-bwd (x ∷ l) = cong (x ∷_) (fwd-bwd l)

  isPreorderList : isPreorder X → isPreorder (List X)
  isPreorderList isPreorderX = isLocalRetract bwd fwd fwd-bwd (isPreorderΣ ℕₛ isPreorderVec)
    where
      isPreorderVec : (n : ℕ) → isPreorder (Vec n)
      isPreorderVec zero = isPreorder⊤
      isPreorderVec (suc n) = isPreorder× isPreorderX (isPreorderVec n)
