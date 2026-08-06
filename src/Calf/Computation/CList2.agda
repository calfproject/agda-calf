open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure

module Calf.Computation.CList2 where

open import Calf.Core.Cost
open import Calf.Value.Nat
open import Calf.Value.Sigma
open import Calf.Computation
open import Calf.Computation.Credit
open import Calf.Computation.Tensor
open import Calf.Computation.CList

binom2 : ℕ → ℕ
binom2 zero = zero
binom2 (suc n) = n + binom2 n

clist₂-potential : ℂ → ℂ → ℕ → ℂ
clist₂-potential c-lin c-quad n =
  (n ⊙ c-lin) +ℂ (binom2 n ⊙ c-quad)

opaque
  CList₂ : ℂ → ℂ → 𝒞 → 𝒞
  CList₂ c-lin c-quad A = CList' (▷[ c-lin ] A) (▷[ c-quad ]_)

  cnil₂ : ∀ {c-lin c-quad} → U (CList₂ c-lin c-quad A)
  cnil₂ {A} {c-lin} {c-quad} = cnil'

  ccons₂ : ∀ {c-lin c-quad} → ▷[ c-lin ] (A ⊗ CList₂ (c-quad +ℂ c-lin) c-quad A) ⊸ CList₂ c-lin c-quad A
  ccons₂ {A} {c-lin} {c-quad} =
    subst (_⊸ CList₂ c-lin c-quad A)
      (▷A⊗B≡▷[A⊗B] c-lin ∙ cong (λ A' → ▷[ c-lin ] (A ⊗ CList' A' _)) (sym ▷/+))
      ccons'

  cfoldr₂ : ∀ {c-lin c-quad} (B : ℂ → 𝒞)
    → (∀ c-lin' → U (B c-lin'))
    → (∀ c-lin' → (▷[ c-lin' ] (A ⊗ B (c-quad +ℂ c-lin'))) ⊸ B c-lin')
    → CList₂ c-lin c-quad A ⊸ B c-lin
  cfoldr₂ {A = A} {c-lin = c-lin} {c-quad = c-quad} B e[] e∷ =
    cfoldr'
      (λ A' → Σ[ c ∈ ℂ ] (A' ≡ ▷[ c ] A))
      (λ A' (c-lin' , _) → B c-lin')
      (λ A' (c-lin' , _) → e[] c-lin')
      (λ A' (c-lin' , ap') → ((c-quad +ℂ c-lin' , cong (▷[ c-quad ]_) ap' ∙ (sym ▷/+))) ,
        subst (_⊸ _) (sym (▷A⊗B≡▷[A⊗B] c-lin') ∙ cong (_⊗ _) (sym ap')) (e∷ c-lin'))
      (c-lin , refl)
