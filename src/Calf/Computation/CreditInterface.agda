open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma

module Calf.Computation.CreditInterface where

open import Calf.Value
open import Calf.Core.Cost
open import Calf.Computation
open import Calf.Computation.Credit
open import Calf.Computation.Debit
open import Calf.Computation.Sum
open import Calf.Computation.Tensor

record ▷-Laws : 𝒱₁ where
  field
    ▷ⁱ[_]_ : ℂ → 𝒞 → 𝒞
    ◁ⁱ[_]_ : ℂ → 𝒞 → 𝒞

    spendⁱ : (A : 𝒞) (c : ℂ) → ▷ⁱ[ c ] A ⊸ A

    ▷ⁱ⊣◁ⁱ : (A ⊸ ◁ⁱ[ c ] B) ≡ (▷ⁱ[ c ] A ⊸ B)
    ▷ⁱ-map : (A ⊸ B) → (▷ⁱ[ c ] A ⊸ ▷ⁱ[ c ] B)
    ▷ⁱ/0 : ▷ⁱ[ 0ℂ ] A ≡ A
    ▷ⁱ/+ : ▷ⁱ[ c₁ +ℂ c₂ ] A ≡ ▷ⁱ[ c₁ ] ▷ⁱ[ c₂ ] A

    ▷ⁱA⊗▷ⁱB≡▷ⁱ[A⊗B] : ∀ c₁ c₂ → ((▷ⁱ[ c₁ ] A) ⊗ (▷ⁱ[ c₂ ] B)) ≡ (▷ⁱ[ c₁ +ℂ c₂ ] (A ⊗ B))
    ▷ⁱA⊗B≡▷ⁱ[A⊗B] : ∀ c → ((▷ⁱ[ c ] A) ⊗ B) ≡ (▷ⁱ[ c ] (A ⊗ B))
    A⊗▷ⁱB≡▷ⁱ[A⊗B] : ∀ c → (A ⊗ (▷ⁱ[ c ] B)) ≡ (▷ⁱ[ c ] (A ⊗ B))
    ▷ⁱA+▷ⁱB≡▷ⁱ[A+B] : ∀ c → ((▷ⁱ[ c ] A) +ᶜ (▷ⁱ[ c ] B)) ≡ (▷ⁱ[ c ] (A +ᶜ B))

open ▷-Laws

std-▷ : ▷-Laws
std-▷ .▷ⁱ[_]_ = ▷[_]_
std-▷ .◁ⁱ[_]_ = ◁[_]_
std-▷ .spendⁱ = spend
std-▷ .▷ⁱ⊣◁ⁱ = ▷⊣◁
std-▷ .▷ⁱ-map = ▷-map
std-▷ .▷ⁱ/0 = ▷/0
std-▷ .▷ⁱ/+ = ▷/+
std-▷ .▷ⁱA⊗▷ⁱB≡▷ⁱ[A⊗B] = ▷A⊗▷B≡▷[A⊗B]
std-▷ .▷ⁱA⊗B≡▷ⁱ[A⊗B] = ▷A⊗B≡▷[A⊗B]
std-▷ .A⊗▷ⁱB≡▷ⁱ[A⊗B] = A⊗▷B≡▷[A⊗B]
std-▷ .▷ⁱA+▷ⁱB≡▷ⁱ[A+B] = ▷A+▷B≡▷[A+B]

alt-▷ : ▷-Laws
alt-▷ .▷ⁱ[_]_ c A = A
alt-▷ .◁ⁱ[_]_ c A = A
alt-▷ .spendⁱ A = CHARGE
alt-▷ .▷ⁱ⊣◁ⁱ = refl
alt-▷ .▷ⁱ-map f = f
alt-▷ .▷ⁱ/0 = refl
alt-▷ .▷ⁱ/+ = refl
alt-▷ .▷ⁱA⊗▷ⁱB≡▷ⁱ[A⊗B] c₁ c₂ = refl
alt-▷ .▷ⁱA⊗B≡▷ⁱ[A⊗B] c = refl
alt-▷ .A⊗▷ⁱB≡▷ⁱ[A⊗B] c = refl
alt-▷ .▷ⁱA+▷ⁱB≡▷ⁱ[A+B] c = refl
