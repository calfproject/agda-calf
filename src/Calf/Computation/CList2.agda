{-# OPTIONS --allow-unsolved-metas #-}

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
open import Calf.Computation.Copower

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
  cfoldr₂ B e[] e∷ = cfoldr' B e[] (λ c₁' → subst (_⊸ _) (sym (▷A⊗B≡▷[A⊗B] c₁')) (e∷ c₁'))

module _ where
  binom2 : ℕ → ℕ
  binom2 zero = zero
  binom2 (suc n) = n + binom2 n

  clist₂-pot : ℂ → ℂ → ℕ → ℂ
  clist₂-pot c₁ c₂ n = (n ⊙ c₁) +ℂ (binom2 n ⊙ c₂)

module _ where
  clist₂-pot-zero : ∀ c₁ c₂ → clist₂-pot c₁ c₂ zero ≡ 0ℂ
  clist₂-pot-zero c₁ c₂ = +ℂ-identityʳ 0ℂ

  clist₂-pot-suc : ∀ n c₁ c₂ → clist₂-pot c₁ c₂ (suc n) ≡ c₁ +ℂ clist₂-pot (c₂ +ℂ c₁) c₂ n
  clist₂-pot-suc n c₁ c₂ =
      clist₂-pot c₁ c₂ (suc n)
    ≡⟨ refl ⟩
      (c₁ +ℂ (n ⊙ c₁)) +ℂ ((n + binom2 n) ⊙ c₂)
    ≡⟨ cong ((c₁ +ℂ (n ⊙ c₁)) +ℂ_) (⊙-+-left n (binom2 n) c₂) ⟩
      (c₁ +ℂ (n ⊙ c₁)) +ℂ ((n ⊙ c₂) +ℂ (binom2 n ⊙ c₂))
    ≡⟨ +ℂ-assoc c₁ (n ⊙ c₁) ((n ⊙ c₂) +ℂ (binom2 n ⊙ c₂)) ⟩
      c₁ +ℂ ((n ⊙ c₁) +ℂ ((n ⊙ c₂) +ℂ (binom2 n ⊙ c₂)))
    ≡⟨ cong (c₁ +ℂ_) (sym (+ℂ-assoc (n ⊙ c₁) (n ⊙ c₂) (binom2 n ⊙ c₂))) ⟩
      c₁ +ℂ (((n ⊙ c₁) +ℂ (n ⊙ c₂)) +ℂ (binom2 n ⊙ c₂))
    ≡⟨ cong (λ c → c₁ +ℂ (c +ℂ (binom2 n ⊙ c₂))) (+ℂ-comm (n ⊙ c₁) (n ⊙ c₂)) ⟩
      c₁ +ℂ (((n ⊙ c₂) +ℂ (n ⊙ c₁)) +ℂ (binom2 n ⊙ c₂))
    ≡⟨ cong (c₁ +ℂ_) (cong (_+ℂ (binom2 n ⊙ c₂)) (sym (⊙-+ n c₂ c₁))) ⟩
      c₁ +ℂ clist₂-pot (c₂ +ℂ c₁) c₂ n
    ∎

opaque
  unfolding CList₂
  unfolding CList'
  -- unfolding CList

  CList₂' : ℂ → ℂ → 𝒞 → 𝒞
  CList₂' c₁ c₂ A = [ n ∈ ℕₛ ] ⋊ ▷[ clist₂-pot c₁ c₂ n ] (⊗ᵏ-fixed A n)

  CList₂≡CList₂' : ∀ {c₁ c₂ A} → CList₂ c₁ c₂ A ≡ CList₂' c₁ c₂ A
  CList₂≡CList₂' {c₁} {c₂} {A} = cong (Σᶜ ℕₛ) (funExt ⊗ᵏ▷≡▷⊗ᵏ)
    where
      ⊗ᵏ▷≡▷⊗ᵏ : ∀ {c₁} → (n : ℕ) →
        ⊗ᵏ (λ c₁' → ▷[ c₁' ] A) (λ c₁' → c₂ +ℂ c₁') c₁ n ≡ ▷[ clist₂-pot c₁ c₂ n ] (⊗ᵏ-fixed A n)
      ⊗ᵏ▷≡▷⊗ᵏ {c₁} zero = sym ▷/0 ∙ cong (▷[_] ⊤) (sym (clist₂-pot-zero c₁ c₂))
      ⊗ᵏ▷≡▷⊗ᵏ {c₁} (suc n) =
          (▷[ c₁ ] A) ⊗ ⊗ᵏ (λ c₁' → ▷[ c₁' ] A) (_+ℂ_ c₂) (c₂ +ℂ c₁) n
        ≡⟨ cong (_ ⊗_) (⊗ᵏ▷≡▷⊗ᵏ n) ⟩
          (▷[ c₁ ] A) ⊗ (▷[ clist₂-pot (c₂ +ℂ c₁) c₂ n ] ⊗ᵏ-fixed A n)
        ≡⟨ ▷A⊗B≡▷[A⊗B] c₁ ∙ cong (▷[ c₁ ]_) (A⊗▷B≡▷[A⊗B] _) ⟩
          ▷[ c₁ ] (▷[ clist₂-pot (c₂ +ℂ c₁) c₂ n ] (A ⊗ ⊗ᵏ-fixed A n))
        ≡⟨ sym ▷/+ ⟩
          ▷[ c₁ +ℂ clist₂-pot (c₂ +ℂ c₁) c₂ n ] (A ⊗ ⊗ᵏ-fixed A n)
        ≡⟨ cong (▷[_] (A ⊗ _)) (sym (clist₂-pot-suc n c₁ c₂)) ⟩
          ▷[ clist₂-pot c₁ c₂ (suc n) ] (A ⊗ ⊗ᵏ-fixed A n)
        ∎

  -- CList₂'' : ℂ → ℂ → 𝒞 → 𝒞
  -- CList₂'' c₁ c₂ A =
  --   Abstractionᶜ (CList A) (CList A) charge-pot
  --     where
  --     charge-pot : CList A ⊸ CList A
  --     charge-pot = ⋊-splitᶜ {X = ℕₛ} {A = λ n → ⊗ᵏ _ _ _ n} (λ n → ⋊-pairᶜ {X = ℕₛ} {A = λ n → ⊗ᵏ _ _ _ n} n ⨾ᶜ CHARGE (clist₂-pot c₁ c₂ n))

  -- CList₂'≡CList₂'' : CList₂'' ≡ CList₂'
  -- CList₂'≡CList₂'' = {!   !}
