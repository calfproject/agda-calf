open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure

module Calf.Computation.CList1 where

open import Calf.Core.Cost
open import Calf.Value.Nat
open import Calf.Computation
open import Calf.Computation.Credit
open import Calf.Computation.Tensor
open import Calf.Computation.List
open import Calf.Computation.Copower

opaque
  CList₁ : ℂ → 𝒞 → 𝒞
  CList₁ c A = Listᶜ (▷[ c ] A)

  cnil₁ : U (CList₁ c A)
  cnil₁ {c} = nil

  ccons₁ : ▷[ c ] (A ⊗ CList₁ c A) ⊸ CList₁ c A
  ccons₁ {c} {A} = subst (_⊸ CList₁ c A) (▷A⊗B≡▷[A⊗B] c) cons

  cfoldr₁ :
      U B
    → (▷[ c ] (A ⊗ B) ⊸ B)
    → CList₁ c A ⊸ B
  cfoldr₁ {B} {c} e[] e∷ = foldr e[] (subst (_⊸ B) (sym (▷A⊗B≡▷[A⊗B] c)) e∷)

opaque
  unfolding CList₁
  unfolding Listᶜ
  unfolding Listᶜ'

  CList₁' : ℂ → 𝒞 → 𝒞
  CList₁' c A = [ n ∈ ℕₛ ] ⋊ ▷[ n ⊙ c ] (⊗ᵏ-fixed A n)

  CList₁≡CList₁' : ∀ {c A} → CList₁ c A ≡ CList₁' c A
  CList₁≡CList₁' {c} {A} = cong (Σᶜ ℕₛ) (funExt ⊗ᵏ▷≡▷⊗ᵏ)
    where
      ⊗ᵏ▷≡▷⊗ᵏ : (n : ℕ) → ⊗ᵏ-fixed (▷[ c ] A) n ≡ ▷[ n ⊙ c ] (⊗ᵏ-fixed A n)
      ⊗ᵏ▷≡▷⊗ᵏ zero = sym ▷/0
      ⊗ᵏ▷≡▷⊗ᵏ (suc n) =
          (▷[ c ] A) ⊗ ⊗ᵏ-fixed (▷[ c ] A) n
        ≡⟨ cong (_ ⊗_) (⊗ᵏ▷≡▷⊗ᵏ n) ⟩
          (▷[ c ] A) ⊗ (▷[ n ⊙ c ] (⊗ᵏ-fixed A n))
        ≡⟨ ▷A⊗B≡▷[A⊗B] c ∙ cong (▷[ c ]_) (A⊗▷B≡▷[A⊗B] _) ⟩
          ▷[ c ] (▷[ n ⊙ c ] (A ⊗ ⊗ᵏ-fixed A n))
        ≡⟨ sym ▷/+ ⟩
          ▷[ c +ℂ (n ⊙ c) ] ⊗ᵏ-fixed A (suc n)
        ∎
