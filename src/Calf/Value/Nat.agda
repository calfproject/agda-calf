module Calf.Value.Nat where

open import Calf.Value
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_; isSetℕ) public
open import Cubical.Data.Nat.Order using (_≤_; isProp≤) public

ℕₛ : 𝒱ₛ
ℕₛ = ℕ , isSetℕ

open import Cubical.Data.Bool
open import Cubical.Data.Nat.Order
open import Cubical.Relation.Nullary

_≤ᵇ_ : ℕ → ℕ → Bool
m ≤ᵇ n with ≤Dec m n
... | yes p = true
... | no ¬p = false
