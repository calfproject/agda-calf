module Examples.Giralf.MergeSort where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Calf.Core.Cost
open import Calf.Value
open import Calf.Value.List
open import Calf.Computation
open import Calf.Computation.Product
open import Calf.Computation.Tensor
open import Calf.Computation.CreditInterface
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
    unfolding Vecᶜ

    merge : ∀ (n₁ n₂ : ℕ) →
      Vecᶜ (F ℕ) n₁ ∷ Vecᶜ (F ℕ) n₂ ∷ [] ⨾ ` (n₁ + n₂) ⊢ Vecᶜ (F ℕ) (n₁ + n₂)
    merge (zero) (zero) = checkᴳ (left all-right) refl idᴳ idᴳ
    merge (zero) (suc n₂) =
      checkᴳ (left all-right) refl idᴳ $
      spendᴳ (suc n₂) (+ℂ-identityʳ _) $ idᴳ
    merge (suc n₁) (zero) =
      checkᴳ (right all-left) refl idᴳ $
      spendᴳ (suc (n₁ + 0)) (+ℂ-identityʳ _) $
      substᴳ {p = suc n₁} {p' = suc n₁ + 0} (Vecᶜ (F ℕ)) solveNat0 idᴳ
    merge (suc n₁) (suc n₂) =
      -- isolate heads of the 2 element vecs
      splitᴳ (right all-left) refl idᴳ $ bindᴳ (left all-right) refl idᴳ $ λ h₂ →
      splitᴳ (right all-left) refl idᴳ $ bindᴳ (left all-right) refl idᴳ $ λ h₁ →
      -- recursive call to merge
      substᵐᴳ {q = suc (suc (n₁ + n₂))} {q' = suc n₁ + suc n₂} solveNat0 $
      letᴳ {q₁ = n₁ + n₂} {q₂ = 2} all-left (+ℂ-comm _ 2) (merge n₁ n₂) $
      -- spend potential, compare 2 heads, and output merged list
      spendᴳ 2 refl $
      substᴳ {p = suc (suc (n₁ + n₂))} {p' = suc n₁ + suc n₂} (Vecᶜ (F ℕ)) solveNat0 $
      if h₁ ≤ᵇ h₂ then (
        tensorᴳ all-right refl (retᴳ h₁) $ tensorᴳ all-right refl (retᴳ h₂) idᴳ
      ) else (
        tensorᴳ all-right refl (retᴳ h₂) $ tensorᴳ all-right refl (retᴳ h₁) idᴳ
      )

    halve : ℕ → ℕ × ℕ
    halve zero = zero , zero
    halve (suc n) = suc (halve n .proj₂) , halve n .proj₁

    halve-≡ : (n : ℕ) → halve n .proj₁ + halve n .proj₂ ≡ n
    halve-≡ zero = refl
    halve-≡ (suc n) = cong suc (+ℂ-comm (halve n .proj₂) _ ∙ halve-≡ n)

    split : ∀ (n : ℕ) (p : ℂ) →
      [ Vecᶜ (▷ᴳ[ 1 +ℂ p ] A) n ] ⨾ 0ℂ ⊢
        ▷ᴳ[ ` n ] (Vecᶜ (▷ᴳ[ p ] A) (halve n .proj₁) ⊗ Vecᶜ (▷ᴳ[ p ] A) (halve n .proj₂))
    split zero p = storeᴳ 0 refl (tensorᴳ all-left refl idᴳ trivᴳ)
    split (suc n) p =
      splitᴳ all-left refl idᴳ $
      releaseᴳ (left all-right) refl idᴳ $
      letᴳ (right all-left) (+ℂ-identityˡ _) (split n p) $
      releaseᴳ (left all-right) refl idᴳ $
      splitᴳ (left all-right) refl idᴳ $
      storeᴳ {q = suc p + n} {q' = p} (suc n) solveNat0 $
        tensorᴳ (right all-left) (+ℂ-identityʳ _)
          (tensorᴳ (right all-left) (+ℂ-identityʳ _) (storeᴳ p (+ℂ-identityʳ _) idᴳ) idᴳ)
          idᴳ

    msort : ∀ n k → [ Vecᶜ (▷ᴳ[ k ] (F ℕ)) n ] ⨾ 0ℂ ⊢ Vecᶜ (F ℕ) n
    msort zero zero = idᴳ
    msort (suc n) zero =
      splitᴳ all-left refl idᴳ $
      releaseᴳ (left all-right) refl idᴳ $
      tensorᴳ (left all-right) refl idᴳ (msort n zero)
    msort n (suc k) =
      -- split incoming vec into 2 halves, and release potential needed for merge
      letᴳ all-left refl (split n k) $
      releaseᴳ (left all-right) refl idᴳ $
      splitᴳ all-left refl idᴳ $
      -- recursive calls to msort
      letᴳ (right all-left) refl (msort (halve n .proj₂) k) $
      letᴳ (right all-left) refl (msort (halve n .proj₁) k) $
      -- merge to get final sorted list
      substᵐᴳ (halve-≡ n) $
      substᴳ (Vecᶜ _) (halve-≡ n) $
      merge (halve n .proj₁) (halve n .proj₂)
