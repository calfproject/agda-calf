module Calf.Value.Nat where

open import Calf.Core.Directed
open import Calf.Value
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_; isSetℕ) public
open import Cubical.Data.Nat.Order using (_≤_; isProp≤) public

opaque
  unfolding 𝟚

  isDiscreteℕ : isDiscrete ℕ
  isDiscreteℕ = ⊑-beh refl

isPreorderℕ : isPreorder ℕ
isPreorderℕ = isSet∧isDiscrete→isPreorder isSetℕ isDiscreteℕ

ℕₚ : 𝒱ₚ
ℕₚ = ℕ , isPreorderℕ
