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
clist₂-potential c₁ c₂ n =
  (n ⊙ c₁) +ℂ (binom2 n ⊙ c₂)

opaque
  CList₂ : ℂ → ℂ → 𝒞 → 𝒞
  CList₂ c₁ c₂ A = CList' (λ c₁' → ▷[ c₁' ] A) (λ c₁' → c₂ +ℂ c₁') c₁

  cnil₂ : ∀ {c₁ c₂} → U (CList₂ c₁ c₂ A)
  cnil₂ {A} {c₁} {c₂} = cnil'

  ccons₂ : ∀ {c₁ c₂} → ▷[ c₁ ] (A ⊗ CList₂ (c₂ +ℂ c₁) c₂ A) ⊸ CList₂ c₁ c₂ A
  ccons₂ {A} {c₁} {c₂} = subst (_⊸ CList₂ c₁ c₂ A) (▷A⊗B≡▷[A⊗B] c₁) ccons'

  cfoldr₂ : ∀ {c₁ c₂} (B : ℂ → 𝒞)
    → (∀ c₁' → U (B c₁'))
    → (∀ c₁' → (▷[ c₁' ] (A ⊗ B (c₂ +ℂ c₁'))) ⊸ B c₁')
    → CList₂ c₁ c₂ A ⊸ B c₁
  cfoldr₂ {A = A} {c₁ = c₁} {c₂ = c₂} B e[] e∷ = cfoldr' B e[] (λ c₁' → subst (_⊸ _) (sym (▷A⊗B≡▷[A⊗B] c₁')) (e∷ c₁'))

opaque
  open import Calf.Computation.Abstraction
  open import Calf.Computation.Copower

  CList₂' : ℂ → ℂ → 𝒞 → 𝒞
  CList₂' c₁ c₂ A = Abstractionᶜ (CList A) (CList A) (clength ⨾ᶜ charger)
    where
      charger : ℕₛ ⋊ CList A ⊸ CList A
      charger = ⋊-splitᶜ {X = ℕₛ} (λ n → CHARGE {CList A} (clist₂-potential c₁ c₂ n))

opaque
  CList₂≡CList₂' : ∀ {c₁ c₂ A} → CList₂ c₁ c₂ A ≡ CList₂' c₁ c₂ A
  CList₂≡CList₂' = {!   !}
