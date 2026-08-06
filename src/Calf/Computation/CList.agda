open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure

module Calf.Computation.CList where

open import Calf.Value.Nat
open import Calf.Computation
open import Calf.Computation.Copower
open import Calf.Computation.Tensor
open import Calf.Computation.Copower

opaque
  CList : 𝒞 → 𝒞
  CList A = [ n ∈ ℕₛ ] ⋊ ⊗ᵏ n A

  cnil : U (CList A)
  cnil = 0 , trivᶜ

  ccons : A ⊗ CList A ⊸ CList A
  ccons {A} = subst (_⊸ CList A) (sym (A⊗[X⋊B]≡X⋊[A⊗B] {X = ℕₛ} {A = A} {B = λ n → ⊗ᵏ n A})) ccons'
    where
      ccons' : [ n ∈ ℕₛ ] ⋊ (A ⊗ ⊗ᵏ n A) ⊸ CList A
      ccons' .U (n , as) = suc n , as
      ccons' .charge c (n , as) = refl

  cfoldr : U B
    → (A ⊗ B ⊸ B)
    → CList A ⊸ B
  cfoldr {B} {A} e[] e∷ = ⋊-splitᶜ {X = ℕₛ} cfoldr'
    where
      cfoldr' : (n : ℕ) → ⊗ᵏ n A ⊸ B
      cfoldr' zero = U→cmp e[]
      cfoldr' (suc n') = map₂ idᶜ (cfoldr' n') ⨾ᶜ e∷
