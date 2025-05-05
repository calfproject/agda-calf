{-# OPTIONS --rewriting #-}

module Examples.Giralf where

open import Algebra.Cost

costMonoid = ℕ-CostMonoid
open CostMonoid costMonoid

open import Calf.Giralf costMonoid

module Examples (impl : Giralf) where
  open Giralf impl

  ex₁ : ⊤ ⨾ 500 ⊢ (413 ⋊ᵍ ⊤)
  ex₁ = charge 87 {! store 413 trivᵍ  !}

  ex₂ : ⊤ ⨾ 2 ⊢ listᵍ (1 ⋊ᵍ ⊤)
  ex₂ = {! cons (store 1 trivᵍ) (cons (store 1 trivᵍ) nil)  !}


module ExamplesCompiled = Examples giralf
