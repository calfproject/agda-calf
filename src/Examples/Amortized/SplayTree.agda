{-# OPTIONS --rewriting #-}

module Examples.Amortized.SplayTree where

open import Algebra.Cost

costMonoid = ℕ-CostMonoid
open CostMonoid costMonoid renaming (_+_ to _⊕_)

open import Calf costMonoid 
open import Calf.Data.Nat 
open import Calf.Data.Product
open import Calf.Data.List
open import Calf.Data.IsBounded costMonoid

open import Data.Nat as Nat using (ℕ; _<_; _≤?_; _<?_; zero)
open import Data.Nat.Properties as Nat using (module ≤-Reasoning)
open import Data.Fin using (Fin; fromℕ<)
open import Relation.Nullary using (Dec; yes; no)

open import Relation.Binary 
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; module ≡-Reasoning)

open import Tactic.MonoidSolver using (solve; solve-macro)

record BST : Set where
  field 
    T : tp⁺
    splay : cmp (Π T (λ _ → Π nat (λ _ → F (nat ×⁺ T))))

ListTree : BST
ListTree .BST.T = list nat
ListTree .BST.splay l i with i <? length l 
... | yes p = let finIdx = fromℕ< p in ret (lookup l finIdx , l)
... | no _ = ret (0 , l)

variable
  n n' n₁ n₂ n₃ : val nat

data Tree : ℕ -> Set where
  leaf : Tree 0
  node : Tree n₁ → val nat → Tree n₂ → Tree (n₁ + 1 + n₂)

tree : tp⁺
tree = Σ⁺ nat (λ n → meta⁺ (Tree n))

data Splayed : ℕ → Set where
  valid : (t : Tree n) → Splayed n 
  zig :   (a : Tree n₁) (x : val nat) (b : Tree n₂) (y : val nat) (c : Tree n₃) → Splayed ((n₁ + 1 + n₂) + 1 + n₃)
  zag :   (a : Tree n₁) (y : val nat) (b : Tree n₂) (x : val nat) (c : Tree n₃) → Splayed (n₁ + 1 + (n₂ + 1 + n₃))

splayed : val nat → tp⁺
splayed n = meta⁺ (Splayed n)

splay : {n : ℕ} → Tree n → (i : val nat) → i < n → cmp (F (splayed n))
splay (node {n₁} {n₂} l z r) i i<n with <-cmp i n₁ 
... | tri< i<n₁ _ _ = bind (F (splayed _)) (splay l i i<n₁) λ
    { (valid (node a x b)) → ret (zig a x b z r)
    ; (zig {n₁₁} {n₁₂} {n₁₃} a x b y c) → 
        let
          arithmetic : n₁₁ + 1 + (n₁₂ + 1 + (n₁₃ + 1 + n₂)) ≡ n₁₁ + 1 + n₁₂ + 1 + n₁₃ + 1 + n₂
          arithmetic = solve Nat.+-0-monoid
        in
          ret (Eq.subst Splayed arithmetic (valid (node a x (node b y (node c z r))))) 
    ; (zag {n₁₁} {n₁₂} {n₁₃} a y b x c) → 
        let
          arithmetic : n₁₁ + 1 + n₁₂ + 1 + (n₁₃ + 1 + n₂) ≡ n₁₁ + 1 + (n₁₂ + 1 + n₁₃) + 1 + n₂
          arithmetic = solve Nat.+-0-monoid
        in
          ret (valid (Eq.subst Tree arithmetic (node (node a y b) x (node c z r)))) 
    } 
... | tri≈ _ i=n₁ _ = ret (valid (node l z r)) 
... | tri> _ _ i≥n₁+1 = 
  let
    arithmetic : i ∸ (n₁ + 1) Nat.< n₂
    arithmetic = let open Nat.≤-Reasoning in 
      Nat.+-cancelˡ-< (n₁ + 1) (i ∸ (n₁ + 1)) n₂ (
        begin-strict
          (n₁ + 1) + (i ∸ (n₁ + 1))
        ≡⟨ Nat.m+[n∸m]≡n (Eq.subst (i Nat.≥_) (Nat.+-comm 1 n₁) i≥n₁+1) ⟩ 
          i
        <⟨ i<n ⟩
          n₁ + 1 + n₂
        ∎
      )
  in
  bind ((F (splayed _))) (splay r (i ∸ (n₁ + 1)) arithmetic) λ 
    { (valid leaf) → Relation.Nullary.contradiction arithmetic Nat.n≮0
    ; (valid (node a x b)) → ret (zag l z a x b)
    ; (zig {n₁₁} {n₁₂} {n₁₃} a x b y c) → 
        let
          arithmetic : n₁ + 1 + n₁₁ + 1 + (n₁₂ + 1 + n₁₃) ≡ n₁ + 1 + (n₁₁ + 1 + n₁₂ + 1 + n₁₃)
          arithmetic = solve Nat.+-0-monoid
        in
        ret (valid (Eq.subst Tree arithmetic (node (node l z a) x (node b y c))))
    ; (zag {n₁₁} {n₁₂} {n₁₃} a y b x c) → 
      let
        arithmetic : n₁ + 1 + n₁₁ + 1 + n₁₂ + 1 + n₁₃ ≡ n₁ + 1 + (n₁₁ + 1 + (n₁₂ + 1 + n₁₃))
        arithmetic = solve Nat.+-0-monoid
      in
      ret (valid (Eq.subst Tree arithmetic (node (node (node l z a) y b) x c))) 
    }

opaque
  SplayTree : BST
  SplayTree .BST.T = tree
  SplayTree .BST.splay (n , t) i with <-cmp i n
  ... | tri< i<n _ _ = bind (F _) (splay t i i<n) λ 
      { (valid (node l z r)) → ret (z , (n , node l z r))
      ; (zig a x b y c) → ret (y , (n , node (node a x b) y c))
      ; (zag a y b x c) → ret (y , (n , node a y (node b x c)))
      }
  ... | tri≈ _ _ _ = ret (0 , (0 , leaf))
  ... | tri> _ _ _ = ret (0 , (0 , leaf))

open BST

record BSTHom (BST BST' : BST) : Set where
  field
    ϕ : cmp (Π (BST .T) λ _ → F (BST' .T))
    ϕ/splay : (t : val (BST .T)) (i : val nat) → 
      bind (F _) (BST .splay t i) (λ { (_ , t') → ϕ t'})
    ≤⁻[ F (BST' .T) ]
      bind (F _) (ϕ t) (λ t' → bind (F _) (BST' .splay t' i) (λ { (_ , t'') → ret t''}))
      

open BSTHom

opaque
  unfolding SplayTree

  inord : {n : ℕ} → Tree n → val (list nat)
  inord leaf = []
  inord (node l z r) = (inord l) ++ (z ∷ []) ++ (inord r)

  ST⇒LT : BSTHom SplayTree ListTree
  ST⇒LT .ϕ (n , t) = ret (inord t)
  ST⇒LT .ϕ/splay = {!   !}