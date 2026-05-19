module Calf.Computation where

open import Calf.Core.Cost
open import Calf.Value
open import Cubical.Foundations.Prelude

record 𝒞 : Type₁ where
  field
    U : 𝒱
  cmp = val U

  field
    charge : val ℂ → cmp → cmp
    charge/0 : ∀ {a} → charge 0ℂ a ≡ a
    charge/+ : ∀ {a c₁ c₂} → charge (c₁ +ℂ c₂) a ≡ charge c₁ (charge c₂ a)
open 𝒞 public

variable
  A B C : 𝒞

record _⊸_ (A B : 𝒞) : Type where
  field
    U : cmp A → cmp B
    charge : (c : val ℂ) (a : cmp A) → U (A .charge c a) ≡ B .charge c (U a)
open _⊸_ public

id⊸ : A ⊸ A
id⊸ .U a = a
id⊸ .charge c a = refl
