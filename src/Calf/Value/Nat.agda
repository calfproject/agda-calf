module Calf.Value.Nat where

open import Calf.Core.Directed
open import Calf.Value
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_; isSetℕ) public
open import Cubical.Data.Nat.Order using (_≤_; isProp≤) public

isPreorderℕ : isPreorder ℕ
isPreorderℕ = isDiscrete→isPreorder

ℕₚ : 𝒱ₚ
ℕₚ = ℕ , isPreorderℕ
