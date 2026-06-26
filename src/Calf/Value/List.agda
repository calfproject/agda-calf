module Calf.Value.List where

open import Calf.Value
open import Cubical.Data.List
  using (List; []; _∷_; foldr; _++_; [_]; length)
  renaming (rev to reverse)
  public

open import Calf.Core.Directed
open import Calf.Value.Nat
open import Calf.Value.Product
open import Calf.Value.Sigma
open import Calf.Value.Unit
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

isSetList : isSet X → isSet (List X)
isSetList {X} isSetX = subst isSet (ua ΣVec≃List) (isSetΣ isSetℕ isSetVec)
  where
    Vec : ℕ → Type
    Vec n = iter n (X ×_) Unit

    isSetVec : (n : ℕ) → isSet (Vec n)
    isSetVec zero = isSetUnit
    isSetVec (suc n) = isSet× isSetX (isSetVec n)

    fwd : Σ ℕ Vec → List X
    fwd (zero , tt) = []
    fwd (suc n , x , xs) = x ∷ fwd (n , xs)

    bwd : List X → Σ ℕ Vec
    bwd [] = 0 , tt
    bwd (x ∷ xs) = let (n , v) = bwd xs in suc n , x , v

    fwd-bwd : section fwd bwd
    fwd-bwd [] = refl
    fwd-bwd (x ∷ l) = cong (x ∷_) (fwd-bwd l)

    bwd-fwd : retract fwd bwd
    bwd-fwd (zero , tt) = refl
    bwd-fwd (suc n , x , v) i .fst = suc (bwd-fwd (n , v) i .fst)
    bwd-fwd (suc n , x , v) i .snd = x , bwd-fwd (n , v) i .snd

    ΣVec≃List : Σ ℕ Vec ≃ List X
    ΣVec≃List .fst = fwd
    ΣVec≃List .snd = isoToIsEquiv (iso fwd bwd fwd-bwd bwd-fwd)

isPreorderList : isPreorder X → isPreorder (List X)
isPreorderList = {!   !}
