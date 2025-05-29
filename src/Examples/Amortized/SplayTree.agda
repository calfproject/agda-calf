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

record BST : Set where
  field 
    T : tp⁺
    splay : cmp (Π T (λ _ → Π nat (λ _ → F (nat ×⁺ T))))

ListBST : BST
ListBST .BST.T = list nat
ListBST .BST.splay l n with Calf.Data.List.lookup l n
... | elem = ret (elem , l)

