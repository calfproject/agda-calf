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
open import Calf.Solver.Nat using (solveNat0)

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

  opaque
    unfolding ℂ

    insert : ∀ p → ℕ → ([ (CList₁ᴳ (1 +ℂ p) (F ℕ)) ] ⨾ p ⊢ (CList₁ᴳ p (F ℕ)))
    insert p x =
      payᴳ (+ℂ-identityʳ p) $
      proj₁ᴳ {B = CList₁ᴳ p (F ℕ)} $
      foldr₁ᴳ
        {B = ◁ᴳ[ p ] CList₁ᴳ p (F ℕ) ×ᶜ CList₁ᴳ p (F ℕ)}
        (pairᴳ
          (getᴳ p refl (cons₁ᴳ base refl (retᴳ x) (nil₁ᴳ refl)))
          (nil₁ᴳ refl)
        )
        (
          spendᴳ 1 refl $
          pairᴳ
            (
              bindᴳ (left all-right) (+ℂ-identityˡ p) idᴳ $ λ y →
              getᴳ p refl $
              if x ≤ᵇ y
              then (
                cons₁ᴳ all-right arith-0 (retᴳ x) $
                cons₁ᴳ all-right arith-1 (retᴳ y) $
                proj₂ᴳ {A = ◁ᴳ[ p ] CList₁ᴳ p (F ℕ)} idᴳ
              ) else (
                cons₁ᴳ all-right arith-2 (retᴳ y) $
                payᴳ refl $
                proj₁ᴳ {B = CList₁ᴳ p (F ℕ)} idᴳ
              )
            )
            (
              cons₁ᴳ (left all-right) arith-1 idᴳ $
              proj₂ᴳ {A = ◁ᴳ[ p ] CList₁ᴳ p (F ℕ)} idᴳ
            )
        )
        idᴳ
      where
        arith-0 : (p +ℂ p) ⋎₂ (p , (0ℂ +ℂ p))
        arith-0 = solveNat0

        arith-1 : p ⋎₂ (p , (0ℂ +ℂ 0ℂ))
        arith-1 = solveNat0

        arith-2 : (p +ℂ p) ⋎₂ (p , (0ℂ +ℂ (p +ℂ 0ℂ)))
        arith-2 = solveNat0

    isort : [ CList₂ᴳ 0 1 (F ℕ) ] ⨾ 0ℂ ⊢ CList₁ᴳ 0 (F ℕ)
    isort =
      foldr₂ᴳ
        (λ r → CList₁ᴳ r (F ℕ))
        (λ r → (nil₁ᴳ refl))
        (λ r → bindᴳ (left all-right) (+ℂ-identityˡ r) idᴳ (insert r))
        idᴳ
