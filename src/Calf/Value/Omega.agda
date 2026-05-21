module Calf.Value.Omega where

open import Calf.Value
open import Cubical.Data.Nat using (ℕ; zero; suc; HasFromNat)
open import Cubical.Foundations.Prelude
open import Data.Unit

data valω : Type where
  zero : valω
  suc : (n : valω) → valω
  rel : (𝕚 : 𝕀) (n : valω) → valω
  rel-𝕀0 : ∀ n → rel 𝕀0 n ≡ n
  rel-𝕀1 : ∀ n → rel 𝕀0 n ≡ suc n

ℕ→ω : ℕ → valω
ℕ→ω zero = zero
ℕ→ω (suc n) = suc (ℕ→ω n)

ω : 𝒱
ω .val = valω
ω .isPreorder = {!   !}

instance
  fromNatω : HasFromNat (val ω)
  fromNatω = record { Constraint = λ _ → ⊤ ; fromNat = λ n → ℕ→ω n }

open import Algebra.Definitions {A = valω} _≡_

infixl 6 _+_

_+_ : valω → valω → valω
zero + m = m
suc n + m = suc (n + m)
rel 𝕚 n + m = rel 𝕚 (n + m)
rel-𝕀0 n i + m = rel-𝕀0 (n + m) i
rel-𝕀1 n i + m = rel-𝕀1 (n + m) i

+-identityˡ : LeftIdentity zero _+_
+-identityˡ _ = refl

+-assoc : Associative _+_
+-assoc zero         _ _ = refl
+-assoc (suc m)      n o = cong suc (+-assoc m n o)
+-assoc (rel 𝕚 m)    n o = cong (rel 𝕚) (+-assoc m n o)
+-assoc (rel-𝕀0 m i) n o = cong (λ x → rel-𝕀0 x i) (+-assoc m n o)
+-assoc (rel-𝕀1 m i) n o = cong (λ x → rel-𝕀1 x i) (+-assoc m n o)
