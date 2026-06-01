module Calf.Value.List where

open import Calf.Value
open import Cubical.Data.List
  using (List; []; _∷_; _++_; [_]; length)
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

Listᵛ : 𝒱 → 𝒱
Listᵛ X .val = List (X .val)
Listᵛ X .is-set = subst isSet (ua ΣVec≃List) (isSetΣ isSetℕ isSetVec)
  where
    Vec : ℕ → Type
    Vec n = iter n (val X ×_) Unit

    isSetVec : (n : ℕ) → isSet (Vec n)
    isSetVec zero = isSetUnit
    isSetVec (suc n) = isSet× (X .is-set) (isSetVec n)

    fwd : Σ ℕ Vec → List (val X)
    fwd (zero , tt) = []
    fwd (suc n , x , xs) = x ∷ fwd (n , xs)

    bwd : List (val X) → Σ ℕ Vec
    bwd [] = 0 , tt
    bwd (x ∷ xs) = let (n , v) = bwd xs in suc n , x , v

    fwd-bwd : section fwd bwd
    fwd-bwd [] = refl
    fwd-bwd (x ∷ l) = cong (x ∷_) (fwd-bwd l)

    bwd-fwd : retract fwd bwd
    bwd-fwd (zero , tt) = refl
    bwd-fwd (suc n , x , v) i .fst = suc (bwd-fwd (n , v) i .fst)
    bwd-fwd (suc n , x , v) i .snd = x , bwd-fwd (n , v) i .snd

    ΣVec≃List : Σ ℕ Vec ≃ List (val X)
    ΣVec≃List .fst = fwd
    ΣVec≃List .snd = isoToIsEquiv (iso fwd bwd fwd-bwd bwd-fwd)
