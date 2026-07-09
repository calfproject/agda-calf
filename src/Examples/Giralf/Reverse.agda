module Examples.Giralf.Reverse where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Calf.Core.Cost
open import Calf.Value
open import Calf.Computation.PList1
open import Calf.Computation.PList2
open import Calf.Giralf

snoc : ∀ p → X → PList₁ (1 +ℂ p) X , p ⊢ PList₁ p X
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

qreverse : PList₂ 0 1 X , 0ℂ ⊢ PList₁ 0 X
qreverse {X} =
  foldr₂ᴳ
    (λ r → PList₁ r X)
    (λ r → nil₁ᴳ)
    snoc
    (idᴳ refl)
