module Examples.Giralf.Reverse where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Calf.Core.Cost
open import Calf.Value
open import Calf.Computation.CList1
open import Calf.Computation.CList2
open import Calf.Giralf

snoc : ∀ p → ⟨ Xₛ ⟩ → CList₁ (1 +ℂ p) Xₛ , p ⊢ CList₁ p Xₛ
snoc p x =
  payᴳ (+ℂ-identityʳ _) $
  foldr₁ᴳ
    ( getᴳ p (+ℂ-identityʳ p) $
      cons₁ᴳ (+ℂ-identityʳ p) x $
      nil₁ᴳ
    )
    (λ y →
      spendᴳ 1 refl $
      getᴳ p refl $
      cons₁ᴳ refl y $
      payᴳ (+ℂ-identityʳ p) $
      idᴳ refl
    )
    (idᴳ refl)

qreverse : CList₂ 0 1 Xₛ , 0ℂ ⊢ CList₁ 0 Xₛ
qreverse {X} =
  foldr₂ᴳ
    (λ r → CList₁ r X)
    (λ r → nil₁ᴳ)
    snoc
    (idᴳ refl)
