module Examples.Giralf.Sort where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Calf.Core.Cost
open import Calf.Value
open import Calf.Computation
open import Calf.Computation.Product
open import Calf.Computation.Tensor
open import Calf.Computation.Credit
open import Calf.Computation.Debit
open import Calf.Computation.PList1
open import Calf.Computation.PList2
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

insert : ∀ p → ℕ → PList₁ (1 +ℂ p) ℕ , p ⊢ PList₁ p ℕ
insert p x =
  payᴳ (+ℂ-identityʳ p) $
  proj₁ᴳ $
  foldr₁ᴳ
    {A = (◁'[ p ] PList₁ p ℕ) ×ᶜ PList₁ p ℕ}
    (pairᴳ
      (getᴳ p (+ℂ-identityʳ p) (cons₁ᴳ (+ℂ-identityʳ p) x nil₁ᴳ))
      nil₁ᴳ
    )
    (λ y →
      chargeᴳ 1 refl $
      pairᴳ
        ( getᴳ p refl $
          if x ≤ᵇ y
            then cons₁ᴳ refl x (cons₁ᴳ (+ℂ-identityʳ p) y (proj₂ᴳ (idᴳ refl)))
            else cons₁ᴳ refl y (payᴳ (+ℂ-identityʳ p) (proj₁ᴳ (idᴳ refl)))
        )
        (cons₁ᴳ (+ℂ-identityʳ p) y (proj₂ᴳ (idᴳ refl)))
    )
    (idᴳ refl)

isort : PList₂ 0 1 ℕ , 0ℂ ⊢ PList₁ 0 ℕ
isort =
  foldr₂ᴳ
    (λ r → PList₁ r ℕ)
    (λ r → nil₁ᴳ)
    insert
    (idᴳ refl)


variable
  k : ℕ

split : PList₁ c ℕ , 0ℂ ⊢ PList₁ c ℕ ⊗ PList₁ c ℕ
split = {!   !}

merge : PList₁ (` suc k) ℕ ⊗ PList₁ (` suc k) ℕ , 0ℂ ⊢ PList₁ (` k) ℕ
merge = {!   !}

msort/clocked : (k k' : ℕ) → PList₁ (` (k + k')) ℕ , 0ℂ ⊢ PList₁ (` k') ℕ
msort/clocked zero k' = idᴳ refl
msort/clocked (suc k) k' =
  letᴳ (+ℂ-identityˡ _) split $
  letᴳ (+ℂ-identityˡ _)
    (transport
      (cong (_⊸ _) lemma)
      (map₂ (msort/clocked k (suc k')) (msort/clocked k (suc k')))) $
  merge
    where
      lemma :
        (▷'[ 0ℂ ] PList₁ (` (k + suc k')) ℕ) ⊗ (▷'[ 0ℂ ] PList₁ (` (k + suc k')) ℕ)
        ≡ ▷'[ 0ℂ ] (PList₁ (` suc (k + k')) ℕ ⊗ PList₁ (` suc (k + k')) ℕ)
      lemma =
          (▷'[ 0ℂ ] PList₁ (` (k + suc k')) ℕ) ⊗ (▷'[ 0ℂ ] PList₁ (` (k + suc k')) ℕ)
        ≡⟨ cong₂ _⊗_ ▷'/0 ▷'/0 ⟩
          PList₁ (` (k + suc k')) ℕ ⊗ PList₁ (` (k + suc k')) ℕ
        ≡⟨ cong (λ n → PList₁ (` n) ℕ ⊗ PList₁ (` n) ℕ) (Nat.+-suc k k') ⟩
          PList₁ (` suc (k + k')) ℕ ⊗ PList₁ (` suc (k + k')) ℕ
        ≡⟨ sym ▷'/0 ⟩
          ▷'[ 0ℂ ] (PList₁ (` suc (k + k')) ℕ ⊗ PList₁ (` suc (k + k')) ℕ)
        ∎
