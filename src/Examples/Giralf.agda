{-# OPTIONS --rewriting #-}

module Examples.Giralf where

open import Algebra.Cost

costMonoid = cm-rev ℕ-CostMonoid
open CostMonoid costMonoid
open import Data.Nat using (_*_)

open import Calf costMonoid
open import Calf.Giralf costMonoid
open import Calf.Data.Product
open import Calf.Data.Sum
open import Calf.Data.List
open import Data.List.Base as List
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)

open import Algebra.Solver.CommutativeMonoid comm-monoid using (prove; Expr; var; id; _⊕_)
import Data.Vec.Base as Vec

module Examples (impl : Giralf) where
  open Giralf impl
  open Perm-Split

  ex₁ : [] ⨾ 500 ⊢ (413 ⋊ᵍ ⊤ᵍ)
  ex₁ = charge 87 refl (store 413 refl trivᵍ)

  ex₂ : [] ⨾ 2 ⊢ listᵍ (1 ⋊ᵍ ⊤ᵍ)
  ex₂ = consᵍ all-left refl (store 1 refl trivᵍ) (consᵍ all-left refl (store 1 refl trivᵍ) nilᵍ)

  double : (p : ℂ) → val (listᵍ ((p + p + 1) ⋊ᵍ (Fᵍ X)) ⊸ listᵍ (p ⋊ᵍ (Fᵍ X)))
  double p =
    let helper a =
          let open SolverHelp in
          prove 1 (v₁ ⊕ v₁) ((id ⊕ v₁) ⊕ ((id ⊕ v₁) ⊕ id))
          Vec.[ a ]
    in
    foldrᵍ idᵍ nilᵍ (
      release (right _ all-left) refl
      idᵍ (
        bindᵍ (left _ all-right) (Eq.sym (+-identityˡ _)) idᵍ (λ x →
          charge 1 refl (
            consᵍ all-right (helper p)
              (store p refl (retᵍ x))
              (consᵍ all-right refl (store p refl (retᵍ x)) idᵍ)
          )
        )
      )
    )

  ex₃ : val (((413 ⋊ᵍ ⊤ᵍ) ⊎ᵍ (312 ⋊ᵍ ⊤ᵍ)) ⊸ ((150 ⋊ᵍ ⊤ᵍ) ⊎ᵍ (100 ⋊ᵍ ⊤ᵍ)))
  ex₃ = caseᵍ all-left refl idᵍ
          (release all-left refl idᵍ (charge 313 refl (inj₂ᵍ (store 100 refl idᵍ))))
          (release all-left refl idᵍ (charge 162 refl (inj₁ᵍ (store 150 refl idᵍ))))


module ExamplesCompiled = Examples giralf

-- hit C-u C-u C-c C-d (for proof type) or C-c C-n (for proof term) in hole
norm-ex₁ = {! ExamplesCompiled.ex₁ .Square.square triv  !}
norm-ex₂ = {! ExamplesCompiled.ex₂ .Square.square triv  !}
norm-double = {! ExamplesCompiled.double 5 .Square.square (1 ∷ 2 ∷ 3 ∷ [])  !}
norm-ex₃ = {! ExamplesCompiled.ex₃ .Square.square (inj₁ triv) !}
