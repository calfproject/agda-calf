module Calf.Value.List where

open import Calf.Value
open import Cubical.Data.List
  using (List; []; _∷_; foldr; _++_; [_]; length)
  renaming (rev to reverse)
  public

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
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

    fwd′ : (n : ℕ) → Vec n → List X
    fwd′ zero tt = []
    fwd′ (suc n) (x , xs) = x ∷ fwd′ n xs

    fwd : Σ ℕ Vec → List X
    fwd (n , xs) = fwd′ n xs

    bwd : List X → Σ ℕ Vec
    bwd [] = 0 , tt
    bwd (x ∷ xs) = let (n , v) = bwd xs in suc n , x , v

    fwd-bwd : section fwd bwd
    fwd-bwd [] = refl
    fwd-bwd (x ∷ l) = cong (x ∷_) (fwd-bwd l)

    bwd-fwd′ : (n : ℕ) (v : Vec n) → bwd (fwd′ n v) ≡ (n , v)
    bwd-fwd′ zero tt = refl
    bwd-fwd′ (suc n) (x , v) i =
      suc (bwd-fwd′ n v i .fst) , x , bwd-fwd′ n v i .snd

    bwd-fwd : retract fwd bwd
    bwd-fwd (n , v) = bwd-fwd′ n v

    ΣVec≃List : Σ ℕ Vec ≃ List X
    ΣVec≃List .fst = fwd
    ΣVec≃List .snd = isoToIsEquiv (iso fwd bwd fwd-bwd bwd-fwd)
