open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure

module Calf.Computation.CList1 where

open import Calf.Core.Cost
open import Calf.Computation
open import Calf.Computation.Credit
open import Calf.Computation.Tensor
open import Calf.Computation.CList

opaque
  CList₁ : ℂ → 𝒞 → 𝒞
  CList₁ c A = CList (▷[ c ] A)

  cnil₁ : U (CList₁ c A)
  cnil₁ {c} = cnil

  ccons₁ : ▷[ c ] (A ⊗ CList₁ c A) ⊸ CList₁ c A
  ccons₁ {c} {A} = subst (_⊸ CList₁ c A) (▷A⊗B≡▷[A⊗B] c) ccons

  cfoldr₁ :
      U B
    → (▷[ c ] (A ⊗ B) ⊸ B)
    → CList₁ c A ⊸ B
  cfoldr₁ {B} {c} {A} e[] e∷ = cfoldr e[] (subst (_⊸ B) (sym (▷A⊗B≡▷[A⊗B] c)) e∷)
