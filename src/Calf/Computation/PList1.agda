open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Univalence using (ua)
open import Cubical.Data.Sigma

module Calf.Computation.PList1 where

open import Calf.Core.Cost
open import Calf.Value
open import Calf.Value.List
import Calf.Value.Closed as ●ᵛ
import Calf.Value.Open as ◯ᵛ
open import Calf.Computation
open import Calf.Computation.Free
open import Calf.Computation.Copower
open import Calf.Computation.Open as ◯ᶜ
open import Calf.Computation.Closed as ●ᶜ
open import Calf.Computation.Glue
open import Calf.Computation.Potential
open import Cubical.Data.Nat

_⊙_ : ℕ → val ℂ → val ℂ
zero ⊙ c = 0ℂ
suc n ⊙ c = c +ℂ (n ⊙ c)

opaque
  PList1 : val ℂ → 𝒱 → 𝒞
  PList1 c-linear X =
    Glueᶜ'
      (F (Listᵛ X))
      (F (Listᵛ X))
      (leftF (λ l → F _ .charge (length l ⊙ c-linear) (ret l)))

  pnil₁ : ∀ {c-lin} → cmp (PList1 c-lin X)
  pnil₁ .• = η• (ret [])
  pnil₁ .◦ = η◦ (ret [])
  pnil₁ {X} {c-lin} .•→◦ = {!   !}

  pcons₁ : ∀ {c-lin} → val X → ▷'[ c-lin ] (PList1 c-lin X) ⊸ PList1 c-lin X
  pcons₁ = {!   !}

pfoldr₁ : ∀ {c-lin}
  → cmp A
  → (val X → (▷'[ c-lin ] A ⊸ A))
  → PList1 c-lin X ⊸ A
pfoldr₁ = {!   !}
