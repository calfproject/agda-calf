module Calf.Value.Omega where

open import Calf.Core.Directed
open import Calf.Value
open import Cubical.Data.Nat using (ℕ; zero; suc; HasFromNat)
open import Cubical.Foundations.Prelude
open import Data.Unit

data valω : Type where
  zero : valω
  suc : (n : valω) → valω
  rel : (𝕚 : 𝟚) (n : valω) → valω
  rel-0𝟚 : ∀ n → rel 0𝟚 n ≡ n
  rel-1𝟚 : ∀ n → rel 1𝟚 n ≡ suc n

ℕ→ω : ℕ → valω
ℕ→ω zero = zero
ℕ→ω (suc n) = suc (ℕ→ω n)

ω : 𝒱
ω .val = valω
ω .is-set = {!   !}
ω .is-preorder = {!   !}

instance
  fromNatω : HasFromNat (val ω)
  fromNatω = record { Constraint = λ _ → ⊤ ; fromNat = λ n → ℕ→ω n }

open import Algebra.Definitions {A = valω} _≡_

infixl 6 _+_

_+_ : valω → valω → valω
zero + m = m
suc n + m = suc (n + m)
rel 𝕚 n + m = rel 𝕚 (n + m)
rel-0𝟚 n i + m = rel-0𝟚 (n + m) i
rel-1𝟚 n i + m = rel-1𝟚 (n + m) i

+-identityˡ : LeftIdentity zero _+_
+-identityˡ _ = refl

+-assoc : Associative _+_
+-assoc zero         _ _ = refl
+-assoc (suc m)      n o = cong suc (+-assoc m n o)
+-assoc (rel 𝕚 m)    n o = cong (rel 𝕚) (+-assoc m n o)
+-assoc (rel-0𝟚 m i) n o = cong (λ x → rel-0𝟚 x i) (+-assoc m n o)
+-assoc (rel-1𝟚 m i) n o = cong (λ x → rel-1𝟚 x i) (+-assoc m n o)
