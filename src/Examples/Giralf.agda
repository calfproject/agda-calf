{-# OPTIONS --rewriting #-}

module Examples.Giralf where

open import Algebra.Cost
open import Relation.Binary using (IsPreorder)

open CostMonoid ℕ-CostMonoid
open import Data.Nat using (_*_; ℕ)
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
  open import Data.Fin as Fin using (Fin)

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

  helper₁ : ∀ {Δq} → _≡⊔ᵐ_ {n = 1} _≡ᶜ⋎_ Δq  Vec.[ Δq ]
  helper₁ = {!   !}
  -- (to Fin.zero greedy base , IsPreorder.refl (costMonoid .CostMonoid.isPreorder))

  helper₂ : _≡⊔ᵐ_ {n = 0} _≡ᶜ⋎_ ([] , 0) Vec.[]
  helper₂ = base , {!   !}

  postulate
    hello₁ : ∀ {Δ} → _≡⊔_ {n = 1} _≡ᶜ⋎_ Δ Vec.[ Δ ]
    hello₄ : ∀ {A Δ} → _≡⊔_ {n = 2} _≡ᶜ⋎_ (A ∷ Δ) (Δ Vec.∷ [ A ] Vec.∷ Vec.[])



  import Data.Nat.GeneralisedArithmetic as GA

  linear : ∀ {p} → [ listᵍ (ℕ.suc p , 0) ⊤ᵍ ] ⨾ 0 ⊢ listᵍ (p , 0) ⊤ᵍ
  linear {p} = foldrᵍ {B = linearB} helper₁ (idᵍ helper₁)
    (nilᵍ helper₂)
    λ {n} → charge 1 (hello₁ , {!   !}) (consᵍ (hello₄ , {!   !}) (idᵍ helper₁) (idᵍ helper₁))
    where
      linearB : ℕ → 𝓒
      linearB n = listᵍ (GA.fold (p , 0) shift n) ⊤ᵍ
      -- (GA.fold (p , 0) shift n) is equivalent to (p , 0), but avoids Eq.subst


  quadratic : [ listᵍ (0 , 1) ⊤ᵍ ] ⨾ 0 ⊢ listᵍ (0 , 0) ⊤ᵍ
  quadratic =
    foldrᵍ {B = quadraticB} helper₁ (idᵍ helper₁)
      (nilᵍ helper₂)
      λ {n} → consᵍ (hello₄ , {!   !}) (idᵍ helper₁) {! linear {n}  !}
    where
      quadraticB : ℕ → 𝓒
      quadraticB n = listᵍ (n , 0) ⊤ᵍ
      -- really (n , 0) arises from the horrific ((GA.fold (0 , 1) shift n) .proj₁ , 0)


module ExamplesCompiled = Examples giralf

-- hit C-u C-u C-c C-d (for proof type) or C-c C-n (for proof term) in hole
-- norm-ex₁ = {! ExamplesCompiled.ex₁ .Square.square triv  !}
-- norm-ex₂ = {! ExamplesCompiled.ex₂ .Square.square triv  !}
-- norm-double = {! ExamplesCompiled.double 5 .Square.square (((ret 1) ∷ (ret 2) ∷ (ret 3) ∷ []) , triv) !}
-- norm-ex₃ = {! ExamplesCompiled.ex₃ .Square.square ((inj₁ triv) , triv) !}
