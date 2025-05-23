{-# OPTIONS --rewriting #-}

module Examples.Giralf where

open import Algebra.Cost

costMonoid = cm-rev ℕ-CostMonoid
open CostMonoid costMonoid
open import Data.Nat using (_*_; ℕ)
open import Data.Nat.Properties using (+-comm)

isCommutativeMonoid : IsCommutativeMonoid ℂ _+_ zero
isCommutativeMonoid .IsCommutativeMonoid.isMonoid = isMonoid
isCommutativeMonoid .IsCommutativeMonoid.comm x y = +-comm y x

open import Calf costMonoid
open import Calf.Giralf ℂ zero _+_ isCommutativeMonoid
open import Calf.Data.Product
open import Calf.Data.Sum
open import Calf.Data.List
open import Data.List.Base as List
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; module ≡-Reasoning)

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


  import Data.Nat.GeneralisedArithmetic as GA

  linear : ∀ {p q} → [ listᵍ (ℕ.suc p , q) ⊤ᵍ ] ⨾ 0 ⊢ listᵍ (p , q) ⊤ᵍ
  linear {p} {q} = foldrᵍ (idᵍ {0})
    (λ n → listᵍ (GA.fold (p , q) shift n) ⊤ᵍ)
    nilᵍ
    λ {n} → charge 1 (lemma n) (consᵍ (right _ all-left) (Eq.sym (+-identityˡ _)) (idᵍ {0}) (idᵍ {0}))
    where
      help : ∀ n →
        (GA.fold (ℕ.suc p , q) shift n) ≡
        let r , s = (GA.fold (p , q) shift n) in (r + 1 , s)
      help ℕ.zero = refl
      help (ℕ.suc n) =
        let helper a b =
              let open SolverHelp in let open Vec in
              prove 3 ((v₁ ⊕ v₂) ⊕ v₃) ((v₁ ⊕ v₃) ⊕ v₂)
              (a ∷ 1 ∷ b ∷ [])
        in
        let r , s = (GA.fold (p , q) shift n) in
        let open ≡-Reasoning in
        begin
          shift (GA.fold (ℕ.suc p , q) shift n)
        ≡⟨ Eq.cong shift (help n) ⟩
          shift (r + 1 , s)
        ≡⟨⟩
          (r + 1 + s , s)
        ≡⟨ Eq.cong (_, s) (helper _ _) ⟩
          (r + s + 1 , s)
        ≡⟨⟩
          let r , s = shift (GA.fold (p , q) shift n) in (r + 1 , s)
        ∎

      lemma : ∀ n → (GA.fold (ℕ.suc p , q) shift n) .proj₁ ≡ (GA.fold (p , q) shift n .proj₁) + 1
      lemma n = Eq.cong (λ x → x .proj₁) (help n)


  quadratic : [ listᵍ (0 , 1) ⊤ᵍ ] ⨾ 0 ⊢ listᵍ (0 , 0) ⊤ᵍ
  quadratic = foldrᵍ (idᵍ {0})
    (λ n → listᵍ (n , 0) ⊤ᵍ)
    nilᵍ
    λ {n} → consᵍ (right _ all-left) (lemma n) (idᵍ {0}) (linear {n} {0})
    where
      help : ∀ n → (GA.fold (0 , 1) shift n) ≡ (n , 1)
      help ℕ.zero = refl
      help (ℕ.suc n) = Eq.cong shift (help n)

      lemma : ∀ n → (GA.fold (0 , 1) shift n) .proj₁ ≡ (0 + 0) + n
      lemma n =
        let open ≡-Reasoning in
        begin
          (GA.fold (0 , 1) shift n) .proj₁
        ≡⟨ Eq.cong (λ x → x .proj₁) (help n) ⟩
          (n , 1) .proj₁
        ≡⟨ Eq.sym (+-identityˡ _) ⟩
          (0 + 0) + n
        ∎


module ExamplesCompiled = Examples giralf

-- hit C-u C-u C-c C-d (for proof type) or C-c C-n (for proof term) in hole
norm-ex₁ = {! ExamplesCompiled.ex₁ .Square.square triv  !}
norm-ex₂ = {! ExamplesCompiled.ex₂ .Square.square triv  !}
norm-double = {! ExamplesCompiled.double 5 .Square.square (((ret 1) ∷ (ret 2) ∷ (ret 3) ∷ []) , triv) !}
norm-ex₃ = {! ExamplesCompiled.ex₃ .Square.square ((inj₁ triv) , triv) !}
