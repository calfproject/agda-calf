module Calf.Value.List where

open import Calf.Value
open import Cubical.Data.List
  using (List; []; _∷_; _++_; [_]; length)
  renaming (rev to reverse)
  public

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Calf.Core.Directed
open import Calf.Value.Nat
open import Calf.Value.Product
open import Calf.Value.Sigma
open import Calf.Value.Unit

Listᵛ : 𝒱 → 𝒱
Listᵛ X .val = List (X .val)
Listᵛ X .is-set = {!   !}
Listᵛ X .is-preorder = subst isPreorder lemma (Σᵛ ℕᵛ Vec .is-preorder)
  where
    Vec : ℕ → 𝒱
    Vec zero = 1ᵛ
    Vec (suc n) = X ×ᵛ Vec n

    lemma : Σ ℕ (val ∘ Vec) ≡ List (X .val)
    lemma = {!   !}
