module Examples.Giralf.Id where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Calf.Core.Cost
open import Calf.Value
open import Calf.Value.Nat
open import Calf.Value.List
open import Calf.Computation
open import Calf.Computation.Free
open import Calf.Computation.CList1
open import Calf.Computation.CList2
open import Calf.Giralf


module _ (impl : Giralf) where
  open Giralf impl

  id₁ : [ CList₁ᴳ (1 +ℂ p) A ] ⨾ 0ℂ ⊢ CList₁ᴳ p A
  id₁ {p} =
    foldr₁ᴳ
      nil₁ᴳ
      (
        spendᴳ 1 refl $
        cons₁ᴳ (left all-right) (cong (p +ℂ_) (+ℂ-identityʳ 0ℂ) ∙ +ℂ-identityʳ p)
          (idᴳ refl)
          (idᴳ refl)
      )
      (idᴳ refl)

  id₂ : ∀ p → [ CList₂ᴳ p 1 A ] ⨾ 0ℂ ⊢ CList₁ᴳ p A
  id₂ {A} p =
    foldr₂ᴳ
      (λ r → CList₁ᴳ r A)
      (λ r → nil₁ᴳ)
      (λ r → cons₁ᴳ (left all-right) (cong (r +ℂ_) (+ℂ-identityʳ 0ℂ) ∙ +ℂ-identityʳ r) (idᴳ refl) id₁)
      (idᴳ refl)
