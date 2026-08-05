open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure

module Calf.Computation.CList where

open import Calf.Core.Abstract
open import Calf.Core.Cost
open import Calf.Value
open import Calf.Value.List
open import Calf.Value.Nat
import Calf.Value.Closed as ●
import Calf.Value.Open as ◯
open import Calf.Computation
open import Calf.Computation.Free as F
open import Calf.Computation.Copower
open import Calf.Computation.Open as ◯ᶜ
open import Calf.Computation.Closed as ●ᶜ
open import Calf.Computation.Glue
open import Calf.Computation.Abstraction
open import Calf.Computation.Potential
open import Calf.Computation.Credit
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

  cfoldr' : ∀ {n : ℕ}
    → U B
    → (A ⊗ B ⊸ B)
    → ⊗ᵏ n A ⊸ B
  cfoldr' {n = zero} e[] e∷ = U→cmp e[]
  cfoldr' {n = suc n'} e[] e∷ = map₂ idᶜ (cfoldr' {n = n'} e[] e∷) ⨾ᶜ e∷

  cfoldr : U B
    → (A ⊗ B ⊸ B)
    → CList A ⊸ B
  cfoldr e[] e∷ .U (n , as) = cfoldr' {n = n} e[] e∷ .U as
  cfoldr e[] e∷ .charge c (n , as) = cfoldr' {n = n} e[] e∷ .charge c as
