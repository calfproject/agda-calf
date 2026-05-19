module Calf.Value.Nat where

open import Calf.Value
open import Cubical.Data.Nat.Base using (ℕ; zero; suc; _+_) public

ℕᵛ : 𝒱
ℕᵛ .val = ℕ
ℕᵛ .isPreorder = {!   !}

instance
  ℕᵛ-isDiscrete : IsDiscrete ℕᵛ
  ℕᵛ-isDiscrete = {!   !}
