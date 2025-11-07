{-# OPTIONS --rewriting #-}

module Examples.Amortized.SplayTree where

-- BST signature and list-based specification 
import Examples.Amortized.SplayTree.Base

-- Splay tree implementation 
import Examples.Amortized.SplayTree.SplayTree

-- Proof of access lemma
import Examples.Amortized.SplayTree.Access

-- Lax homomorphism
import Examples.Amortized.SplayTree.LaxHomomorphism 

-- Balance theorem
import Examples.Amortized.SplayTree.Balance

-- Example rotations of splay tree
import Examples.Amortized.SplayTree.Example
