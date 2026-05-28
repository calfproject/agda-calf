module Calf.Value.Nat where

open import Calf.Core.Directed
open import Calf.Value
open import Cubical.Data.Nat.Base using (ℕ; zero; suc; _+_) public
open import Cubical.Data.Nat
open import Cubical.Foundations.Prelude

ℕᵛ : 𝒱
ℕᵛ .fst = ℕ
ℕᵛ .snd = isSetℕ
