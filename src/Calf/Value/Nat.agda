module Calf.Value.Nat where

open import Calf.Value
open import Cubical.Data.Nat.Base using (ℕ; zero; suc; _+_) public
open import Cubical.Data.Nat
open import Cubical.Foundations.Prelude

ℕᵛ : 𝒱
ℕᵛ .val = ℕ
ℕᵛ .is-set = isSetℕ

open import Cubical.Data.Nat.Order using (_≤_; isProp≤)

infix 4 _≤ᵛ_

_≤ᵛ_ : val ℕᵛ → val ℕᵛ → 𝒱
m ≤ᵛ n = fromProp ((m ≤ n) , isProp≤)
