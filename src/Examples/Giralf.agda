{-# OPTIONS --rewriting #-}

module Examples.Giralf where

open import Algebra.Cost

costMonoid = ℕ-CostMonoid
open CostMonoid costMonoid
open import Data.Nat using (_*_)

open import Calf costMonoid
open import Calf.Giralf costMonoid
open import Calf.Data.Product
open import Calf.Data.List

module Examples (impl : Giralf) where
  open Giralf impl

  ex₁ : ⊤ ⨾ 500 ⊢ (413 ⋊ᵍ ⊤)
  ex₁ = charge 87 {! store 413 trivᵍ  !}

  ex₂ : ⊤ ⨾ 2 ⊢ listᵍ 1 unit
  ex₂ = cons triv (cons triv nil)

  double : ∀ {p X} → val (listᵍ (2 * p) X ⊸ listᵍ p X)
  double = foldrᵍ id nil (λ x → cons x (cons x id))


module ExamplesCompiled = Examples giralf

-- hit C-u C-u C-c C-d (for proof type) or C-c C-n (for proof term) in hole
norm-ex₁ = {! ExamplesCompiled.ex₁ .Square.square triv  !}
norm-ex₂ = {! ExamplesCompiled.ex₂ .Square.square triv  !}
norm-double = {! ExamplesCompiled.double .Square.square (1 ∷ 2 ∷ 3 ∷ [])  !}
