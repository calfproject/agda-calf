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

    id₁ : ∀ n → Vecᶜ (▷ᴳ[ 1 ] ⊤) n ∷ [] ⨾ 0ℂ ⊢ ⊤
    id₁ zero = idᴳ
    id₁ (suc n) =
      splitᴳ (left all-right) refl idᴳ $
      releaseᴳ (left all-right) refl idᴳ $
      spendᴳ 1 refl $
      checkᴳ (left all-right) refl idᴳ $
      id₁ n

    merge : ∀ (n₁ n₂ : ℕ) →
      Vecᶜ (F ℕ) n₁ ∷ Vecᶜ (F ℕ) n₂ ∷ Vecᶜ (▷ᴳ[ 1 ] ⊤) (n₁ + n₂) ∷ [] ⨾ 0ℂ ⊢ Vecᶜ (F ℕ) (n₁ + n₂)
    merge (zero) (zero) =
      checkᴳ (left all-right) refl idᴳ $
      checkᴳ (left all-right) refl idᴳ idᴳ
    merge (zero) (suc n₂) =
      checkᴳ (left all-right) refl idᴳ $
      substᴳ (Vecᶜ (F ℕ)) (sym (+ℂ-identityˡ (suc n₂))) $
      checkᴳ (right all-left) refl (id₁ (suc n₂)) idᴳ
    merge (suc n₁) (zero) =
      checkᴳ (right (left all-right)) refl idᴳ $
      substᴳ (Vecᶜ (F ℕ)) (sym (+ℂ-identityʳ (suc n₁))) $
      checkᴳ (right all-left) refl (id₁ (suc (n₁ + 0))) idᴳ
    merge (suc n₁) (suc n₂) =
      -- release potential stored in first 2 elems of potential vec
      splitᴳ (right (right all-left)) refl
        (substᴳ {p = suc n₁ + suc n₂} {p' = suc (suc (n₁ + n₂))} (Vecᶜ (▷ᴳ[ 1 ] ⊤)) solveNat0 idᴳ) $
      splitᴳ (right (left all-right)) refl idᴳ $
      releaseᴳ (left all-right) refl idᴳ $ checkᴳ (left all-right) refl idᴳ $
      releaseᴳ (right (left all-right)) refl idᴳ $ checkᴳ (left all-right) refl idᴳ $
      -- isolate heads of the 2 element vecs
      splitᴳ (right (right all-left)) refl idᴳ $ bindᴳ (left all-right) refl idᴳ $ λ h₂ →
      splitᴳ (right (right all-left)) refl idᴳ $ bindᴳ (left all-right) refl idᴳ $ λ h₁ →
      -- -- recursive call to merge
      letᴳ all-left refl (merge n₁ n₂) $
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

    halve-≡ : (n : ℕ) → n ≡ halve n .proj₁ + halve n .proj₂
    halve-≡ zero = refl
    halve-≡ (suc n) = cong suc (halve-≡ n ∙ +ℂ-comm (halve n .proj₁) _)

    split : ∀ (n : ℕ) (p : ℂ) →
      [ Vecᶜ (▷ᴳ[ 1 +ℂ p ] A) n ] ⨾ 0ℂ ⊢
        Vecᶜ (▷ᴳ[ 1 ] ⊤) n ⊗ (Vecᶜ (▷ᴳ[ p ] A) (halve n .proj₁) ⊗ Vecᶜ (▷ᴳ[ p ] A) (halve n .proj₂))
    split zero p = tensorᴳ all-left refl idᴳ (tensorᴳ base refl trivᴳ trivᴳ)
    split (suc n) p =
      splitᴳ all-left refl idᴳ $
      releaseᴳ (left all-right) refl idᴳ $
      letᴳ (right all-left) (+ℂ-identityˡ _) (split n p) $
      splitᴳ (left all-right) (+ℂ-identityˡ _) idᴳ $
      splitᴳ (right (left all-right)) (+ℂ-identityˡ _) idᴳ $
        tensorᴳ (right (right (left all-right))) (+ℂ-identityʳ _)
          (tensorᴳ all-right (+ℂ-identityʳ _) (storeᴳ 1 (+ℂ-identityʳ _) trivᴳ) idᴳ)
          (
            tensorᴳ (right all-left) refl
              ( tensorᴳ (right all-left) (+ℂ-identityʳ _) (storeᴳ p (+ℂ-identityʳ _) idᴳ) idᴳ )
              idᴳ
          )

    msort : ∀ n k → [ Vecᶜ (▷ᴳ[ k ] (F ℕ)) n ] ⨾ 0ℂ ⊢ Vecᶜ (F ℕ) n
    msort zero zero = idᴳ
    msort (suc n) zero =
      splitᴳ all-left refl idᴳ $
      releaseᴳ (left all-right) refl idᴳ $
      tensorᴳ (left all-right) refl idᴳ (msort n zero)
    msort n (suc k) =
      -- split incoming vec into 2 halves, and a potential vec
      letᴳ all-left refl (split n k) $
      splitᴳ all-left refl idᴳ $
      splitᴳ (right all-left) refl idᴳ $
      -- recursive calls to msort
      letᴳ (left all-right) refl (msort (halve n .proj₁) k) $
      letᴳ (right (left all-right)) refl (msort (halve n .proj₂) k) $
      -- dumb lets to do halve-≡ transport and rearrange context
      letᴳ (right (right all-left)) refl (substᴳ (Vecᶜ _) (halve-≡ n) idᴳ) $
      letᴳ (right (left all-right)) refl idᴳ $
      letᴳ (right (right all-left)) refl idᴳ $
      -- merge to output sorted list
      substᴳ (Vecᶜ _) (sym (halve-≡ n)) $
      merge (halve n .proj₁) (halve n .proj₂)
