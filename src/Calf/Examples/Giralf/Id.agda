module Calf.Examples.Giralf.Id where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Calf.Core.Cost
open import Calf.Value
open import Calf.Computation.PList1
open import Calf.Computation.PList2
open import Calf.Giralf

id₁ : PList₁ (1 +ℂ p) X , 0ℂ ⊢ PList₁ p X
id₁ =
  foldr₁ᴳ
    nil₁ᴳ
    (λ x →
      chargeᴳ 1 refl $
      cons₁ᴳ (+ℂ-identityʳ _) x $
      idᴳ
    )
    idᴳ

id₂ : ∀ p → PList₂ p 1 X , 0ℂ ⊢ PList₁ p X
id₂ {X} p =
  foldr₂ᴳ
    (λ r → PList₁ r X)
    (λ r → nil₁ᴳ)
    (λ r x → cons₁ᴳ (+ℂ-identityʳ r) x id₁)
    idᴳ
