module Examples.Giralf.InsertionSort where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Calf.Core.Cost
open import Calf.Value
open import Calf.Value.List
open import Calf.Computation
open import Calf.Computation.Product
open import Calf.Computation.Tensor
open import Calf.Computation.Credit
open import Calf.Computation.Debit
open import Calf.Computation.CList1
open import Calf.Computation.CList2
open import Calf.Computation.Free
open import Calf.Giralf

open import Cubical.Data.Bool
open import Cubical.Data.Nat
import Cubical.Data.Nat.Properties as Nat
open import Cubical.Data.Nat.Order
open import Cubical.Relation.Nullary

_≤ᵇ_ : ℕ → ℕ → Bool
m ≤ᵇ n with ≤Dec m n
... | yes p = true
... | no ¬p = false

module _ (impl : Giralf) where
  open Giralf impl
  open Perm-Split

  insert : ∀ p → ℕ → ([ (CList₁ᴳ (1 +ℂ p) (F ℕ)) ] ⨾ p ⊢ (CList₁ᴳ p (F ℕ)))
  insert p x =
    payᴳ (+ℂ-identityʳ p) $
    proj₁ᴳ {B = CList₁ᴳ p (F ℕ)} $
    foldr₁ᴳ
      {B = ◁ᴳ[ p ] CList₁ᴳ p (F ℕ) ×ᶜ CList₁ᴳ p (F ℕ)}
      (pairᴳ
        (getᴳ p (+ℂ-identityʳ p) (cons₁ᴳ base (cong (p +ℂ_) (+ℂ-identityʳ 0ℂ) ∙ +ℂ-identityʳ p) (retᴳ x) nil₁ᴳ))
        nil₁ᴳ
      )
      (
        spendᴳ 1 refl $
        pairᴳ
          (
            bindᴳ (left all-right) (+ℂ-identityˡ p) (idᴳ refl) $ λ y →
            getᴳ p refl $
            if x ≤ᵇ y
            then (
              cons₁ᴳ all-right {!   !} (retᴳ x) $
              cons₁ᴳ all-right (cong (p +ℂ_) (+ℂ-identityʳ 0ℂ) ∙ +ℂ-identityʳ p) (retᴳ y) (proj₂ᴳ {A = ◁ᴳ[ p ] CList₁ᴳ p (F ℕ)} (idᴳ refl))
            ) else (
              cons₁ᴳ all-right {!   !} (retᴳ y) $
              payᴳ (+ℂ-identityʳ p) (proj₁ᴳ {B = CList₁ᴳ p (F ℕ)} (idᴳ refl))
            )
          )
          (cons₁ᴳ (left all-right) {!   !} (idᴳ refl) (proj₂ᴳ {A = ◁ᴳ[ p ] CList₁ᴳ p (F ℕ)} (idᴳ refl)))
      )
      (idᴳ refl)

  isort : [ CList₂ᴳ 0 1 (F ℕ) ] ⨾ 0ℂ ⊢ CList₁ᴳ 0 (F ℕ)
  isort =
    foldr₂ᴳ
      (λ r → CList₁ᴳ r (F ℕ))
      (λ r → nil₁ᴳ)
      (λ r → bindᴳ (left all-right) (+ℂ-identityˡ r) (idᴳ refl) (insert r))
      (idᴳ refl)
