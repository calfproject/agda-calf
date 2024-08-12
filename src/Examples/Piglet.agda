{-# OPTIONS --rewriting #-}

module Examples.Piglet where

open import Relation.Binary.PropositionalEquality
open import Data.Rational

open import Data.Interval
open import Calf.Data.Nat as Nat

open import Piglet

postulate
  convex : 𝕀 → tp⁻ → tp⁻ → tp⁻

_⊗[_]_ : tp⁻ → 𝕀 → tp⁻ → tp⁻
X ⊗[ p ] Y = convex p X Y

postulate
  ℚ⁻ : tp⁻

  ℚ/decode : val (U ℚ⁻) ≡ ℚ
  {-# REWRITE ℚ/decode #-}


die : cmp (F nat)
die = {!   !}

nat-to-real : ℕ → ℚ
nat-to-real = {! ...from stdlib...  !}

𝔼 : cmp (F nat) → cmp ℚ⁻
𝔼 e = bind ℚ⁻ e nat-to-real

_ : 𝔼 die ≡ {! 3.5  !}
_ = {!   !}

-- ℙ P = bind

-- _ : (bind ? die λ x → F (x Nat.> 1)) ≡ flip ? (F ⊤) (F ⊥)
