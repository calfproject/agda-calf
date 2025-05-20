{-# OPTIONS --rewriting #-}

module Examples.Giralf where

open import Algebra.Cost
open import Relation.Binary using (IsPreorder)

open CostMonoid ℕ-CostMonoid
open import Data.Nat using (_*_)
open import Data.Nat.Properties using (+-comm)

open import Calf.Giralf ℂ zero _+_ (record { isMonoid = isMonoid ; comm = +-comm })
open import Calf.Data.Product
open import Calf.Data.Sum
open import Calf.Data.List
open import Data.List.Base as List
open import Data.Product
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)

open import Algebra.Solver.CommutativeMonoid comm-monoid using (prove; Expr; var; id; _⊕_)
import Data.Vec.Base as Vec

module Examples (impl : Giralf) where
  open Giralf impl
  open Perm-Split

  -- ex₁ : [] ⨾ 500 ⊢ (413 ⋊ᵍ ⊤ᵍ)
  -- ex₁ = charge 87 refl (store 413 refl trivᵍ)

  -- ex₂ : [] ⨾ 2 ⊢ listᵍ (1 ⋊ᵍ ⊤ᵍ)
  -- ex₂ = consᵍ all-left refl (store 1 refl (trivᵍ {0})) (consᵍ all-left refl (store 1 refl (trivᵍ {0})) (nilᵍ {0}))

  -- double : (p : ℂ) → val (listᵍ ((p + p + 2) ⋊ᵍ (Fᵍ X)) ⊸ listᵍ (p ⋊ᵍ (Fᵍ X)))
  -- double p =
  --   let helper a =
  --         let open SolverHelp in let open Vec in
  --         prove 2 ((v₁ ⊕ v₁) ⊕ v₂) ((v₂ ⊕ v₁) ⊕ (id ⊕ v₁))
  --         (a ∷ 1 ∷ [])
  --   in
  --   foldrᵍ (idᵍ {0}) (nilᵍ {0}) (
  --     release (right _ all-left) refl
  --     (idᵍ {0}) (
  --       bindᵍ (left _ all-right) (Eq.sym (+-identityˡ _)) (idᵍ {0}) (λ x →
  --         charge 1 refl (
  --           consᵍ all-right (helper p)
  --             (store p refl (retᵍ {1} x))
  --             (consᵍ all-right refl (store p refl (retᵍ {0} x)) (idᵍ {0}))
  --         )
  --       )
  --     )
  --   )

  -- ex₃ : val (((413 ⋊ᵍ ⊤ᵍ) ⊎ᵍ (312 ⋊ᵍ ⊤ᵍ)) ⊸ ((150 ⋊ᵍ ⊤ᵍ) ⊎ᵍ (100 ⋊ᵍ ⊤ᵍ)))
  -- ex₃ = caseᵍ all-left refl (idᵍ {0})
  --         (release all-left refl (idᵍ {0}) (charge 313 refl (inj₂ᵍ (store 100 refl (idᵍ)))))
  --         (release all-left refl (idᵍ {0}) (charge 162 refl (inj₁ᵍ (store 150 refl (idᵍ)))))

  linear : [ listᵍ (1 , 0) ⊤ᵍ ] ⨾ 0 ⊢ ⊤ᵍ
  linear = {!   !}

  quadratic : [ listᵍ (0 , 1) ⊤ᵍ ] ⨾ 0 ⊢ ⊤ᵍ
  quadratic =
    foldrᵍ {Δ' = [ listᵍ (0 , 1) ⊤ᵍ ]} {q' = 0}
      ({! to   !} , IsPreorder.refl (costMonoid .CostMonoid.isPreorder))
      (idᵍ {Δ = [ listᵍ (0 , 1) ⊤ᵍ ]} {q = 0} {!   !})
      (trivᵍ {Δ = []} {q = 0} {!   !})
      (checkᵍ {!   !} (idᵍ {!   !}) linear)


module ExamplesCompiled = Examples giralf

-- hit C-u C-u C-c C-d (for proof type) or C-c C-n (for proof term) in hole
norm-ex₁ = {! ExamplesCompiled.ex₁ .Square.square triv  !}
norm-ex₂ = {! ExamplesCompiled.ex₂ .Square.square triv  !}
norm-double = {! ExamplesCompiled.double 5 .Square.square (((ret 1) ∷ (ret 2) ∷ (ret 3) ∷ []) , triv) !}
norm-ex₃ = {! ExamplesCompiled.ex₃ .Square.square ((inj₁ triv) , triv) !}
