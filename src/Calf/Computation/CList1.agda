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
open import Calf.Computation.CreditInterface


module _ (▷-impl : ▷-Laws) where
  open ▷-Laws ▷-impl

  opaque
    CList₁ : ℂ → 𝒞 → 𝒞
    CList₁ c A = Listᶜ (▷ⁱ[ c ] A)

    cnil₁ : U (CList₁ c A)
    cnil₁ {c} = nil

    ccons₁ : ▷ⁱ[ c ] (A ⊗ CList₁ c A) ⊸ CList₁ c A
    ccons₁ {c} {A} = subst (_⊸ CList₁ c A) (▷ⁱA⊗B≡▷ⁱ[A⊗B] c) cons

    cfoldr₁ :
        U B
      → (▷ⁱ[ c ] (A ⊗ B) ⊸ B)
      → CList₁ c A ⊸ B
    cfoldr₁ {B} {c} e[] e∷ = foldr e[] (subst (_⊸ B) (sym (▷ⁱA⊗B≡▷ⁱ[A⊗B] c)) e∷)

  opaque
    unfolding CList₁
    unfolding Listᶜ
    unfolding Listᶜ'

    CList₁' : ℂ → 𝒞 → 𝒞
    CList₁' c A = [ n ∈ ℕₛ ] ⋊ ▷ⁱ[ n ⊙ c ] (⊗ᵏ-fixed A n)

    CList₁≡CList₁' : ∀ {c A} → CList₁ c A ≡ CList₁' c A
    CList₁≡CList₁' {c} {A} = cong (Σᶜ ℕₛ) (funExt ⊗ᵏ▷ⁱ≡▷ⁱ⊗ᵏ)
      where
        ⊗ᵏ▷ⁱ≡▷ⁱ⊗ᵏ : (n : ℕ) → ⊗ᵏ-fixed (▷ⁱ[ c ] A) n ≡ ▷ⁱ[ n ⊙ c ] (⊗ᵏ-fixed A n)
        ⊗ᵏ▷ⁱ≡▷ⁱ⊗ᵏ zero = sym ▷ⁱ/0
        ⊗ᵏ▷ⁱ≡▷ⁱ⊗ᵏ (suc n) =
            (▷ⁱ[ c ] A) ⊗ ⊗ᵏ-fixed (▷ⁱ[ c ] A) n
          ≡⟨ cong (_ ⊗_) (⊗ᵏ▷ⁱ≡▷ⁱ⊗ᵏ n) ⟩
            (▷ⁱ[ c ] A) ⊗ (▷ⁱ[ n ⊙ c ] (⊗ᵏ-fixed A n))
          ≡⟨ ▷ⁱA⊗▷ⁱB≡▷ⁱ[A⊗B] c (n ⊙ c) ⟩
            ▷ⁱ[ c +ℂ (n ⊙ c) ] ⊗ᵏ-fixed A (suc n)
          ∎
