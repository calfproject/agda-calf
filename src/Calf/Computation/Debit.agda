open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma

module Calf.Computation.Debit where

open import Calf.Core.Cost
open import Calf.Value
open import Calf.Computation
open import Calf.Computation.Lolli
open import Calf.Computation.Credit
open import Calf.Computation.Tensor

◁'[_]_ : val ℂ → 𝒞 → 𝒞
◁'[ c ] A = ▷'[ c ] ⊤ ⊸ᶜ A

pot-cost : ∀ {c} → (A ⊸ ◁'[ c ] B) ≡ (▷'[ c ] A ⊸ B)
pot-cost {A} {B} {c} =
    (A ⊸ (◁'[ c ] B))
  ≡⟨ refl ⟩
    (A ⊸ (▷'[ c ] ⊤ ⊸ᶜ B))
  ≡⟨ sym lolli-currying ⟩
    ((A ⊗ (▷'[ c ] ⊤)) ⊸ B)
  ≡⟨ cong (_⊸ B) pot-tensor ⟩
    (▷'[ c ] (A ⊗ ⊤) ⊸ B)
  ≡⟨ cong (λ C → (▷'[ c ] C) ⊸ B) ⊗-identityʳ ⟩
    ((▷'[ c ] A) ⊸ B)
  ∎

pot-cost-counit : ▷'[ c ] ◁'[ c ] A ⊸ A
pot-cost-counit = transport pot-cost idᶜ
