open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma

module Calf.Computation.Cost where

open import Calf.Core.Cost
open import Calf.Value
open import Calf.Computation
open import Calf.Computation.Lolli
open import Calf.Computation.Potential
open import Calf.Computation.Tensor

◁'[_]_ : val ℂ → 𝒞 → 𝒞
◁'[ c ] A = ▷'[ c ] ⊤ ⊸ᶜ A

pot-cost : ∀ {c} → (A ⊸ ◁'[ c ] B) ≡ (▷'[ c ] A ⊸ B)
pot-cost = {!   !}

pot-cost-counit : ▷'[ c ] ◁'[ c ] A ⊸ A
pot-cost-counit = transport pot-cost idᶜ
