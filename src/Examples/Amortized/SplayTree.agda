{-# OPTIONS --rewriting #-}

module Examples.Amortized.SplayTree where

open import Algebra.Cost

costMonoid = ℕ-CostMonoid
open CostMonoid costMonoid

open import Calf costMonoid 
open import Calf.Data.Nat renaming (_+_ to _⊕_)
open import Calf.Data.Product
open import Calf.Data.List
open import Calf.Data.IsBounded costMonoid

open import Data.Nat using (ℕ; _<_; _≤?_; _<?_; zero)
open import Data.Nat.Properties as Nat using (module ≤-Reasoning)
open import Data.Fin using (Fin; fromℕ<)
open import Relation.Nullary using (Dec; yes; no)

open import Relation.Binary 
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; module ≡-Reasoning)


record BST : Set where
  field 
    T : tp⁺
    splay : cmp (Π T (λ _ → Π nat (λ _ → F (nat ×⁺ T))))

ListBST : BST
ListBST .BST.T = list nat
ListBST .BST.splay l i with i <? length l 
... | yes p = 
  let finIdx = fromℕ< p in
  ret (lookup l finIdx , l)
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

n+1≤m⇒n≤m : (n : val nat) (m : val nat) → suc n Data.Nat.≤ m → n Data.Nat.≤ m
n+1≤m⇒n≤m n m p = let open Nat.≤-Reasoning in
  begin
    n
  <⟨ s≤s (≤-reflexive refl) ⟩ 
    suc n
  ≤⟨ p ⟩
    m
  ∎

open import Tactic.MonoidSolver using (solve; solve-macro)

splay : {n : ℕ} → Tree n → (i : val nat) → i < n → cmp (F (splayed n))
splay (node {n₁} {n₂} l z r) i p with <-cmp i n₁ 
... | tri< i+1≤n₁ i≢n₁ b = 
  bind (F (splayed _)) 
  (splay l i (Nat.≤∧≢⇒< (n+1≤m⇒n≤m i n₁ i+1≤n₁) i≢n₁)) λ
    { (valid (node a x b)) → ret (zig a x b z r)
    ; (zig {n₁₁} {n₁₂} {n₁₃} a x b y c) → 
        let
          arithmetic : n₁₁ + 1 + (n₁₂ + 1 + (n₁₃ + 1 + n₂)) ≡ n₁₁ + 1 + n₁₂ + 1 + n₁₃ + 1 + n₂
          arithmetic = let open Eq.≡-Reasoning in
            begin
              n₁₁ + 1 + (n₁₂ + 1 + (n₁₃ + 1 + n₂))
            ≡⟨ {!  !} ⟩
              (n₁₁ + 1) + (n₁₂ + 1 + (n₁₃ + 1 + n₂))
            ≡⟨ {!   !} ⟩
              {!   !}
            ∎
        in
          ret {!   !}
    ; (zag a y b x c) → {!   !} } 
... | tri≈ _ i=n₁ _ = {!   !} 
... | tri> _ _ i>n₁ = {!   !}  
-- real work goes here 

SplayTree : BST
SplayTree .BST.T = tree
SplayTree .BST.splay (n , t) i = 
  bind (F _) (splay t i {!   !}) 
    λ { (valid t) → {!   !}
     ;  (zig a x b y c) → ret (x , n , node (node a x b) y c)
     ;  (zag a y b x c) → {!   !} }