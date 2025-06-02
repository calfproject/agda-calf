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
  zag :   (a : Tree n₁) (y : val nat) (b : Tree n₂) (y : val nat) (c : Tree n₃) → Splayed (n₁ + 1 + (n₂ + 1 + n₃))

splayed : tp⁺
splayed = Σ⁺ nat (λ n → meta⁺ (Splayed n))  

SplayTree : BST
SplayTree .BST.T = tree
SplayTree .BST.splay (n , leaf) i = ret (0 , (n , leaf))
SplayTree .BST.splay (n , node {n₁} {n₂} l z r) i with Nat.<-cmp i n₁
... | foo = {!   !}


