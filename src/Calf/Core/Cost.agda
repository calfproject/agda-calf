module Calf.Core.Cost where

open import Calf.Value
open import Calf.Value.Nat
open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Nat.Literals public
import Cubical.Data.Nat.Properties as Nat
open import Data.Unit

module _ {A : Type} where
  open import Algebra.Definitions {A = A} _≡_ public

`_ = fromNat

opaque
  ℂ : 𝒱
  ℂ = ℕᵛ

  0ℂ : val ℂ
  0ℂ = 0

  _+ℂ_ : val ℂ → val ℂ → val ℂ
  _+ℂ_ = _+_

  +ℂ-identityˡ : LeftIdentity 0ℂ _+ℂ_
  +ℂ-identityˡ c = refl

  +ℂ-assoc : Associative _+ℂ_
  +ℂ-assoc c₁ c₂ c₃ = sym (Nat.+-assoc c₁ c₂ c₃)

  +ℂ-comm : Commutative _+ℂ_
  +ℂ-comm c₁ c₂ = Nat.+-comm c₁ c₂

  ℕ→ℂ : ℕ → val ℂ
  ℕ→ℂ n = ` n

instance
  fromNatℂ : HasFromNat (val ℂ)
  fromNatℂ = record { Constraint = λ _ → ⊤ ; fromNat = λ n → ℕ→ℂ n }

variable
  c c₁ c₂ : val ℂ
