module Calf.Value.Nat where

open import Calf.Core.Directed
open import Calf.Value
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_; isSetℕ) public
open import Cubical.Data.Nat.Order using (_≤_; isProp≤) public

opaque
  unfolding 𝟚

  isDiscreteℕ : isDiscrete ℕ
  isDiscreteℕ = BEH⇒isDiscrete refl

ℕ₌ : 𝒱₌
ℕ₌ = ℕ , isSetℕ , isDiscreteℕ

ℕₚ : 𝒱ₚ
ℕₚ = ⟨ ℕ₌ ⟩ₚ
