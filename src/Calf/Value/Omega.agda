module Calf.Value.Omega where

open import Calf.Value
open import Data.Nat
open import Data.Nat using (_+_) public

ω : 𝒱
ω .val = ℕ
ω .isPreorder = {!   !}
