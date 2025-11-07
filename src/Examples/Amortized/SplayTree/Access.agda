{-# OPTIONS --rewriting #-}

module Examples.Amortized.SplayTree.Access where

open import Algebra.Cost

costMonoid = ℕ-CostMonoid
open CostMonoid costMonoid renaming (_+_ to _⊕_)

open import Calf costMonoid 
open import Calf.Data.Nat 
open import Calf.Data.Bool as Bool using (bool; true; false)
open import Calf.Data.Product
open import Calf.Data.List hiding (find)
open import Calf.Data.IsBounded costMonoid

open import Data.Nat as Nat using (ℕ; _<_; _≤?_; _<?_; zero)
open import Data.Nat.Properties as Nat using (module ≤-Reasoning; _≟_)
open import Data.Bool.Properties as Bool
open import Data.Nat.Base using (⌊_/2⌋) 
open import Data.List.Base using (deduplicate)
open import Data.List.Properties as List
open import Data.Fin using (Fin; fromℕ<)
open import Relation.Nullary using (Dec; yes; no)

open import Relation.Binary 
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≢_; refl; module ≡-Reasoning)

open import Data.Nat.Logarithm
open import Data.Nat.PredExp2
open import Data.Empty using (⊥; ⊥-elim)

open import Examples.Amortized.SplayTree.SplayTree
open import Examples.Amortized.SplayTree.Arithmetic
open import Examples.Amortized.SplayTree.AccessPrepare

rank/eq : (a b c : Tree) (k p : val nat) 
    → rank (node a k (node b p c)) ≡ rank (node (node a k b) p c)
rank/eq a b c k p = 
    Eq.cong (λ e → ⌊log₂ e ⌋) 
      (arithmetic₁₀ (tree-size a) 1 (tree-size b) 1 (tree-size c))

splay'/amortized : (l : Tree) (r : Tree) (anc : List Context) (k : val nat) → 
   bind (F _) (splay' l r anc k) (λ ((l' , r') , _) → φ (node l' k r')) 
  ≤⁻[ F _ ] 
   step (F _) (1 + 3 * (rank (reconstruct (node l k r) anc) ∸ rank (node l k r))) (φ (reconstruct (node l k r) anc))
-- done
splay'/amortized a b [] k = step-monoˡ-≤⁻ {c' = 1 + 3 * (rank (reconstruct (node a k b) []) ∸ rank (node a k b))} (φ (node a k b)) z≤n 

-- zig
splay'/amortized a b (Left p c ∷ []) k = 
  let
    rank-x  = rank (node a k b)
    rank-y  = rank (node (node a k b) p c)

    rank-x' = rank (node a k (node b p c))
    rank-y' = rank (node b p c)

    rank/ordering : rank-x' ≡ rank-y 
    rank/ordering = rank/eq a b c k p  

    rank/containment1 : rank-y' Nat.≤ rank-y
    rank/containment1 = 
      let open Nat.≤-Reasoning in 
      begin
        rank (node b p c)
      ≡⟨⟩
        ⌊log₂ (tree-size b + 1 + tree-size c) ⌋
      ≤⟨ ⌊log₂⌋-mono-≤ (Nat.m≤n+m (tree-size b + 1 + tree-size c) (tree-size a + 1)) ⟩
        ⌊log₂ ((tree-size a + 1) + ((tree-size b + 1) + tree-size c)) ⌋
      ≡⟨ Eq.cong (λ e → ⌊log₂ e ⌋) (arithmetic₁₂ (tree-size a) 1 (tree-size b) 1 (tree-size c)) ⟩
        ⌊log₂ (((tree-size a + 1) + tree-size b) + 1 + tree-size c) ⌋
      ≡⟨⟩
        rank (node (node a k b) p c)
      ∎

    rank/containment2 : rank-x Nat.≤ rank-y
    rank/containment2 = 
      let open Nat.≤-Reasoning in 
      begin 
        rank (node a k b)
      ≡⟨⟩
        ⌊log₂ (tree-size a + 1 + tree-size b) ⌋
      ≤⟨ ⌊log₂⌋-mono-≤ (Nat.m≤m+n (tree-size a + 1 + tree-size b) (1 + tree-size c)) ⟩
        ⌊log₂ ((tree-size a + 1 + tree-size b) + (1 + tree-size c)) ⌋
      ≡⟨ Eq.cong (λ e → ⌊log₂ e ⌋) (+-assoc (tree-size a + 1 + tree-size b) 1 (tree-size c)) ⟨
        ⌊log₂ (((tree-size a + 1) + tree-size b) + 1 + tree-size c) ⌋
      ≡⟨⟩
        rank (node (node a k b) p c)
      ∎
  in
  let open ≤⁻-Reasoning (F (list nat)) in 
  begin
    bind (F _) (splay' a b (Left p c ∷ []) k) (λ ((l' , r') , t≡t') → φ (node l' k r'))
  ≡⟨⟩ 
    bind (F _) (splay' a b (Left p c ∷ []) k) (λ ((l' , r') , t≡t') → (step (F _) (sum-of-ranks (node l' k r'))) (ret (inord (node l' k r'))))
  ≡⟨ Eq.cong (λ e → bind (F _) (splay' a b (Left p c ∷ []) k) e) (funext (λ ((l' , r') , t≡t') → 
      Eq.cong (step (F _) (sum-of-ranks (node l' k r'))) (Eq.cong (λ e → ret e) t≡t'))) ⟨
    bind (F _) (splay' a b (Left p c ∷ []) k) (λ ((l' , r') , t≡t') → (step (F _) (sum-of-ranks (node l' k r'))) (ret (inord (node (node a k b) p c))))
  ≡⟨⟩  
    step (F _) (1 + sum-of-ranks a + rank-x' + (sum-of-ranks b + rank-y' + sum-of-ranks c))
      (ret (inord (node (node a k b) p c)))
  ≡⟨ Eq.cong (λ e → step (F _) e (ret (inord (node (node a k b) p c)))) 
      (arithmetic₆ 1 (sum-of-ranks a) rank-x' (sum-of-ranks b) rank-y' (sum-of-ranks c)) ⟩
    step (F _) ((1 + sum-of-ranks a + sum-of-ranks b + sum-of-ranks c) + (rank-x' + rank-y'))
      (ret (inord (node (node a k b) p c)))
  ≲⟨ step-monoˡ-≤⁻ (ret (inord (node (node a k b) p c))) 
      (+-monoʳ-≤ (1 + sum-of-ranks a + sum-of-ranks b + sum-of-ranks c) 
        (+-mono-≤ (Nat.≤-reflexive rank/ordering) rank/containment1)) ⟩
    step (F _) ((1 + sum-of-ranks a + sum-of-ranks b + sum-of-ranks c) + (rank-y + rank-y))
      (ret (inord (node (node a k b) p c)))
  ≡⟨ Eq.cong (λ e → step (F _) ((1 + sum-of-ranks a + sum-of-ranks b + sum-of-ranks c) + e) (ret (inord (node (node a k b) p c)))) 
      (arithmetic-manual rank-y rank-x rank/containment2) ⟩ 
    step (F _) ((1 + sum-of-ranks a + sum-of-ranks b + sum-of-ranks c) +
      ((rank-y + rank-x) + (rank-y ∸ rank-x)))
        (ret (inord (node (node a k b) p c)))
  ≲⟨ step-monoˡ-≤⁻ (ret (inord (node (node a k b) p c))) 
      (+-monoʳ-≤ (1 + sum-of-ranks a + sum-of-ranks b + sum-of-ranks c) 
        (+-mono-≤ Nat.≤-refl (Nat.m≤n*m (rank-y ∸ rank-x) 3)) ) ⟩
    step (F _) ((1 + sum-of-ranks a + sum-of-ranks b + sum-of-ranks c) + 
      ((rank-y + rank-x) + 3 * (rank-y ∸ rank-x)))
        (ret (inord (node (node a k b) p c)))
  ≡⟨ Eq.cong (λ e → step (F _) e (ret (inord (node (node a k b) p c)))) 
      (arithmetic₅ 1 (sum-of-ranks a) (sum-of-ranks b) (sum-of-ranks c) rank-y rank-x (3 * (rank-y ∸ rank-x))) ⟩
    step (F _) (1 + 3 * (rank-y ∸ rank-x) + ((sum-of-ranks a + rank-x + sum-of-ranks b) + rank-y + sum-of-ranks c))
      (ret (inord (node (node a k b) p c))) 
  ≡⟨⟩
    step (F _) (1 + 3 * (rank-y ∸ rank-x)) (φ (node (node a k b) p c))
  ∎

-- zag
splay'/amortized b c (Right a p ∷ []) k = 
  let
    rank-x  = rank (node b k c)
    rank-y  = rank (node a p (node b k c))

    rank-x' = rank (node (node a p b) k c)
    rank-y' = rank (node a p b)

    rank/ordering : rank-x' ≡ rank-y
    rank/ordering = Eq.sym (rank/eq a b c p k)

    rank/containment1 : rank-y' Nat.≤ rank-y 
    rank/containment1 = 
      let open Nat.≤-Reasoning in 
      begin
        rank (node a p b)
      ≡⟨⟩
        ⌊log₂ (tree-size a + 1 + tree-size b) ⌋
      ≤⟨ ⌊log₂⌋-mono-≤ (Nat.m≤m+n (tree-size a + 1 + tree-size b) (1 + tree-size c)) ⟩
        ⌊log₂ ((tree-size a + 1 + tree-size b) + (1 + tree-size c)) ⌋
      ≡⟨ Eq.cong (λ e → ⌊log₂ e ⌋) (arithmetic₈ (tree-size a) 1 (tree-size b) 1 (tree-size c)) ⟩
        ⌊log₂ ((tree-size a + 1 + (tree-size b + 1 + tree-size c))) ⌋
      ≡⟨⟩
        rank (node a p (node b k c))
      ∎

    rank/containment2 : rank-x Nat.≤ rank-y
    rank/containment2 = 
      let open Nat.≤-Reasoning in 
      begin
        rank (node b k c)
      ≡⟨⟩
        ⌊log₂ (tree-size b + 1 + tree-size c) ⌋
      ≤⟨ ⌊log₂⌋-mono-≤ (Nat.m≤n+m (tree-size b + 1 + tree-size c) (tree-size a + 1)) ⟩
        ⌊log₂ ((tree-size a + 1) + (tree-size b + 1 + tree-size c)) ⌋
      ≡⟨ Eq.cong (λ e → ⌊log₂ e ⌋) (arithmetic₉ (tree-size a) 1 (tree-size b) 1 (tree-size c)) ⟩
        ⌊log₂ (tree-size a + 1 + (tree-size b + 1 + tree-size c)) ⌋
      ≡⟨⟩
        rank (node a p (node b k c))
      ∎
  in
  let open ≤⁻-Reasoning (F (list nat)) in 
  begin
    bind (F _) (splay' b c (Right a p ∷ []) k) (λ ((l' , r') , t≡t') → φ (node l' k r')) 
  ≡⟨⟩ 
    bind (F _) (splay' b c (Right a p ∷ []) k) (λ ((l' , r') , t≡t') → (step (F _) (sum-of-ranks (node l' k r'))) (ret (inord (node l' k r')))) 
  ≡⟨ Eq.cong (λ e → bind (F _) (splay' b c (Right a p ∷ []) k) e) (funext (λ ((l' , r') , t≡t') → 
       Eq.cong (step (F _) (sum-of-ranks (node l' k r'))) (Eq.cong (λ e → ret e) t≡t') )) ⟨  
    bind (F _) (splay' b c (Right a p ∷ []) k) (λ ((l' , r') , t≡t') → (step (F _) (sum-of-ranks (node l' k r'))) (ret (inord (node a p (node b k c)))))
  ≡⟨⟩ 
    step (F _) (1 + (sum-of-ranks a + rank-y' + sum-of-ranks b + rank-x' + sum-of-ranks c)) 
      (ret (inord (node a p (node b k c))))
  ≡⟨ Eq.cong (λ e → step (F _) e (ret (inord (node a p (node b k c)))))
      (arithmetic₁₁ 1 (sum-of-ranks a) rank-y' (sum-of-ranks b) rank-x' (sum-of-ranks c)) ⟩ 
    step (F _) ((1 + sum-of-ranks a + sum-of-ranks b + sum-of-ranks c) + (rank-y' + rank-x')) 
      (ret (inord (node a p (node b k c))))
  ≲⟨ step-monoˡ-≤⁻ (ret (inord (node a p (node b k c)))) 
      (+-monoʳ-≤ (1 + sum-of-ranks a + sum-of-ranks b + sum-of-ranks c) 
        (+-mono-≤ rank/containment1 (Nat.≤-reflexive rank/ordering))) ⟩ 
    step (F _) ((1 + sum-of-ranks a + sum-of-ranks b + sum-of-ranks c) + ((rank-y + rank-y)))
      (ret (inord (node a p (node b k c))))
  ≡⟨ Eq.cong (λ e → step (F _) e (ret (inord (node a p (node b k c))))) 
      (Eq.cong (λ e → 1 + sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + e) 
        (arithmetic-manual rank-y rank-x rank/containment2)) ⟩
    step (F _) ((1 + sum-of-ranks a + sum-of-ranks b + sum-of-ranks c) + ((rank-y + rank-x) + (rank-y ∸ rank-x)))
      (ret (inord (node a p (node b k c))))
  ≲⟨ step-monoˡ-≤⁻ (ret (inord (node a p (node b k c)))) 
      (+-monoʳ-≤ (1 + sum-of-ranks a + sum-of-ranks b + sum-of-ranks c) 
        (+-mono-≤ Nat.≤-refl (Nat.m≤n*m (rank-y ∸ rank-x) 3)) ) ⟩ 
    step (F _) ((1 + sum-of-ranks a + sum-of-ranks b + sum-of-ranks c) + ((rank-y + rank-x) + 3 * (rank-y ∸ rank-x)))
      (ret (inord (node a p (node b k c))))
  ≡⟨ Eq.cong (λ e → step (F _) e (ret (inord (node a p (node b k c))))) 
      (arithmetic₇ 1 (sum-of-ranks a) (sum-of-ranks b) (sum-of-ranks c) rank-y rank-x (3 * (rank-y ∸ rank-x))) ⟩ 
    step (F _) ((1 + 3 * (rank-y ∸ rank-x)) + (sum-of-ranks a + rank-y + (sum-of-ranks b + rank-x + sum-of-ranks c)))
      (ret (inord (node a p (node b k c))))
  ≡⟨⟩ 
    step (F _) (1 + 3 * (rank-y ∸ rank-x)) (φ (node a p (node b k c))) 
  ∎

-- zig-zig
splay'/amortized a b (Left p c ∷ Left g d ∷ anc) k with Nat.<-cmp (rank (node a k b)) (rank (node a k (node b p (node c g d))))
... | tri< rank-x<rank-x' _ _  = 
  let
    rank-x  : val nat
    rank-x  = rank (node a k b)
    rank-y  : val nat
    rank-y  = rank (node (node a k b) p c)
    rank-z  : val nat
    rank-z  = rank (node (node (node a k b) p c) g d)
    rank-x' : val nat
    rank-x' = rank (node a k (node b p (node c g d)))
    rank-y' : val nat
    rank-y' = rank (node b p (node c g d))
    rank-z' : val nat
    rank-z' = rank (node c g d)
  in 
  let open ≤⁻-Reasoning (F (list nat)) in 
  begin
    step (F _) 1 (
      bind (F _) (splay' a (node b p (node c g d)) anc k) (λ ((l' , r') , _) → 
        φ (node l' k r')))
  ≲⟨ step-monoʳ-≤⁻ 1 (splay'/amortized a (node b p (node c g d)) anc k) ⟩
    step (F _) 1 (
      step (F _) (1 + 3 * (rank (reconstruct (node a k (node b p (node c g d))) anc) ∸ rank-x'))
        (φ (reconstruct (node a k (node b p (node c g d))) anc)))
  ≡⟨⟩
    step (F _) (1 + 1 + 3 * (rank (reconstruct (node a k (node b p (node c g d))) anc) ∸ rank-x'))
      (φ (reconstruct (node a k (node b p (node c g d))) anc)) 
  ≡⟨ Eq.cong (λ e → step (F _) e (φ (reconstruct (node a k (node b p (node c g d))) anc))) 
      (Eq.cong (λ e → 1 + 1 + 3 * (e ∸ rank-x')) 
        (rank/recon (node a k (node b p (node c g d))) (node (node (node a k b) p c) g d) anc size/lemma)) ⟩
    step (F _) (1 + 1 + 3 * (rank (reconstruct (node (node (node a k b) p c) g d) anc) ∸ rank-x'))
      (φ (reconstruct (node a k (node b p (node c g d))) anc)) 
  ≡⟨⟩
    step (F _) (1 + 1 + 3 * (rank (reconstruct (node (node (node a k b) p c) g d) anc) ∸ rank-x'))
      (step (F _) (sum-of-ranks (reconstruct (node a k (node b p (node c g d))) anc)) 
        (ret (inord (reconstruct (node a k (node b p (node c g d))) anc))))
  ≡⟨⟩
    step (F _) (1 + 1 + 3 * (rank (reconstruct (node (node (node a k b) p c) g d) anc) ∸ rank-x') + 
      sum-of-ranks (reconstruct (node a k (node b p (node c g d))) anc))
        (ret (inord (reconstruct (node a k (node b p (node c g d))) anc)))
  ≲⟨ step-monoˡ-≤⁻ (ret (inord (reconstruct (node a k (node b p (node c g d))) anc))) 
      (+-monoʳ-≤ (1 + 1 + 3 * (rank (reconstruct (node (node (node a k b) p c) g d) anc) ∸ rank-x')) 
        phi/lemma) ⟩
    step (F _) (1 + 1 + 3 * (rank (reconstruct (node (node (node a k b) p c) g d) anc) ∸ rank-x') +
      (((3 * (rank-x' ∸ rank-x)) ∸ 1) + sum-of-ranks (reconstruct (node (node (node a k b) p c) g d) anc)))
        (ret (inord (reconstruct (node a k (node b p (node c g d))) anc)))
  ≡⟨ Eq.cong (λ e → step (F _) e (ret (inord (reconstruct (node a k (node b p (node c g d))) anc)))) 
      (arithmetic2 1 (3 * (rank (reconstruct (node (node (node a k b) p c) g d) anc) ∸ rank-x')) 
        ((3 * (rank-x' ∸ rank-x))) (sum-of-ranks (reconstruct (node (node (node a k b) p c) g d) anc)) 
          size-arith1) ⟩
    step (F _) ((1 ∸ 1) + 1 + ((3 * (rank (reconstruct (node (node (node a k b) p c) g d) anc) ∸ rank-x')) +
      (3 * (rank-x' ∸ rank-x))) + sum-of-ranks (reconstruct (node (node (node a k b) p c) g d) anc))
        (ret (inord (reconstruct (node a k (node b p (node c g d))) anc)))
  ≡⟨ Eq.cong (λ e → step (F _) (e + 1 + ((3 * (rank (reconstruct (node (node (node a k b) p c) g d) anc) ∸ rank-x')) +
      (3 * (rank-x' ∸ rank-x))) + sum-of-ranks (reconstruct (node (node (node a k b) p c) g d) anc))
        (ret (inord (reconstruct (node a k (node b p (node c g d))) anc)))) (Nat.n∸n≡0 1) ⟩
     step (F _) (1 + ((3 * (rank (reconstruct (node (node (node a k b) p c) g d) anc) ∸ rank-x')) +
      (3 * (rank-x' ∸ rank-x))) + sum-of-ranks (reconstruct (node (node (node a k b) p c) g d) anc))
        (ret (inord (reconstruct (node a k (node b p (node c g d))) anc)))
  ≡⟨ Eq.cong (λ e → step (F _) (1 + e + sum-of-ranks (reconstruct (node (node (node a k b) p c) g d) anc))
      (ret (inord (reconstruct (node a k (node b p (node c g d))) anc)))) 
        (arithmetic3 (rank (reconstruct (node (node (node a k b) p c) g d) anc)) rank-x' rank-x
          (size-arith2 (node a k (node b p (node c g d))) (node (node (node a k b) p c) g d) anc size/lemma) 
            (Nat.<⇒≤ rank-x<rank-x')) ⟩
    step (F _) (1 + (3 * (rank (reconstruct (node (node (node a k b) p c) g d) anc) ∸ rank-x)) +  
      sum-of-ranks (reconstruct (node (node (node a k b) p c) g d) anc))
        (ret (inord (reconstruct (node a k (node b p (node c g d))) anc)))
  ≡⟨⟩
    step (F _) (1 + 3 * (rank (reconstruct (node (node (node a k b) p c) g d) anc) ∸ rank-x))
      (step (F _) (sum-of-ranks (reconstruct (node (node (node a k b) p c) g d) anc))
        (ret (inord (reconstruct (node a k (node b p (node c g d))) anc))))
  ≡⟨ Eq.cong (λ e → step (F _) (1 + 3 * (rank (reconstruct (node (node (node a k b) p c) g d) anc) ∸ rank-x)) e) 
      (Eq.cong (λ e → step (F _) (sum-of-ranks (reconstruct (node (node (node a k b) p c) g d) anc)) e) 
        (Eq.cong ret (inord/reconstruct 
          (node (node (node a k b) p c) g d)
          (node a k (node b p (node c g d)))
          anc 
          (zig/zig/inord/arith a b c d k p g)))) ⟨
    step (F _) (1 + 3 * (rank (reconstruct (node (node (node a k b) p c) g d) anc) ∸ rank-x))
      (step (F _) (sum-of-ranks (reconstruct (node (node (node a k b) p c) g d) anc))
        (ret (inord (reconstruct (node (node (node a k b) p c) g d) anc))))
  ≡⟨⟩
    step (F _) (1 + 3 * (rank (reconstruct (node (node (node a k b) p c) g d) anc) ∸ rank-x)) 
      (φ (reconstruct (node (node (node a k b) p c) g d) anc))
  ∎
  where
    size/lemma : tree-size (node a k (node b p (node c g d))) ≡ tree-size (node (node (node a k b) p c) g d)
    size/lemma = 
      let open ≡-Reasoning in
      begin
        tree-size a + 1 + (tree-size b + 1 + (tree-size c + 1 + tree-size d))
      ≡⟨ Eq.cong (λ e → tree-size a + 1 + e) (Nat.+-assoc (tree-size b) 1 (tree-size c + 1 + tree-size d)) ⟩
        tree-size a + 1 + (tree-size b + (1 + (tree-size c + 1 + tree-size d)))
      ≡⟨ Nat.+-assoc (tree-size a + 1) (tree-size b) (1 + (tree-size c + 1 + tree-size d)) ⟨
        tree-size a + 1 + tree-size b + (1 + (tree-size c + 1 + tree-size d))
      ≡⟨ Nat.+-assoc (tree-size a + 1 + tree-size b) 1 (tree-size c + 1 + tree-size d) ⟨
        tree-size a + 1 + tree-size b + 1 + (tree-size c + 1 + tree-size d)
      ≡⟨ Eq.cong (λ e → tree-size a + 1 + tree-size b + 1 + e) (Nat.+-assoc (tree-size c) 1 (tree-size d)) ⟩
        tree-size a + 1 + tree-size b + 1 + (tree-size c + (1 + tree-size d))
      ≡⟨ Nat.+-assoc (tree-size a + 1 + tree-size b + 1) (tree-size c) (1 + tree-size d) ⟨
        tree-size a + 1 + tree-size b + 1 + tree-size c + (1 + tree-size d)
      ≡⟨ Nat.+-assoc (tree-size a + 1 + tree-size b + 1 + tree-size c) 1 (tree-size d) ⟨
        tree-size a + 1 + tree-size b + 1 + tree-size c + 1 + tree-size d
      ∎
    size-arith1 : 1 Nat.≤ 3 * (rank (node a k (node b p (node c g d))) ∸ rank (node a k b))
    size-arith1 = 
      let open Nat.≤-Reasoning in
      begin
        1
      ≤⟨ s≤s z≤n ⟩
        3
      ≤⟨ Nat.m≤m*n 3 (rank (node a k (node b p (node c g d))) ∸ rank (node a k b)) 
          {{ >-nonZero (Nat.m<n⇒0<n∸m rank-x<rank-x') }}  ⟩
        3 * (rank (node a k (node b p (node c g d))) ∸ rank (node a k b))
      ∎
    size-arith2 : (t₁ t₂ : Tree) (anc : List Context) → tree-size t₁ ≡ tree-size t₂ → 
      rank t₁ Nat.≤ rank (reconstruct t₂ anc)
    size-arith2 t₁ t₂ [] t₁≡t₂ = Nat.≤-reflexive (Eq.cong (λ e → ⌊log₂ e ⌋) t₁≡t₂)
    size-arith2 t₁ t₂ (Left k t ∷ anc) t₁≡t₂ = 
      let open Nat.≤-Reasoning in
      begin
        rank t₁
      ≡⟨⟩
        ⌊log₂ (tree-size t₁) ⌋
      ≤⟨ ⌊log₂⌋-mono-≤ (Nat.m≤m+n (tree-size t₁) (1 + tree-size t)) ⟩
        ⌊log₂ ((tree-size t₁) + (1 + tree-size t)) ⌋
      ≡⟨ Eq.cong (λ e → ⌊log₂ (e + (1 + tree-size t)) ⌋) t₁≡t₂ ⟩
        ⌊log₂ ((tree-size t₂) + (1 + tree-size t)) ⌋
      ≡⟨ Eq.cong (λ e → ⌊log₂ e ⌋) (Nat.+-assoc (tree-size t₂) 1 (tree-size t)) ⟨
        ⌊log₂ (tree-size t₂ + 1 + tree-size t) ⌋
      ≡⟨⟩
        rank (node t₂ k t)
      ≤⟨ size-arith2 (node t₂ k t) (node t₂ k t) anc refl ⟩
        rank (reconstruct (node t₂ k t) anc)
      ∎
    size-arith2 t₁ t₂ (Right t k ∷ anc) t₁≡t₂ = 
      let open Nat.≤-Reasoning in
      begin
        rank t₁
      ≡⟨⟩
        ⌊log₂ (tree-size t₁) ⌋
      ≤⟨ ⌊log₂⌋-mono-≤ (Nat.m≤n+m (tree-size t₁) (tree-size t + 1)) ⟩
        ⌊log₂ (tree-size t + 1 + tree-size t₁) ⌋
      ≡⟨ Eq.cong (λ e → ⌊log₂ ((tree-size t + 1) + e) ⌋) t₁≡t₂ ⟩
        ⌊log₂ (tree-size t + 1 + tree-size t₂) ⌋
      ≡⟨⟩
        rank (node t k t₂)
      ≤⟨ size-arith2 (node t k t₂) (node t k t₂) anc refl ⟩
        rank (reconstruct (node t k t₂) anc)
      ∎
    arithmetic2 : (a b c d : val nat) → a Nat.≤ c → a + a + b + ((c ∸ a) + d) ≡ (a ∸ a) + a + (b + c) + d
    arithmetic2 a b c d a≤c = arithmetic-manual₂ a b c d a≤c
    arithmetic3 : (a b c : val nat) → b Nat.≤ a → c Nat.≤ b → (3 * (a ∸ b)) + (3 * (b ∸ c)) ≡ (3 * (a ∸ c))
    arithmetic3 a b c b≤a c≤b = arithmetic-manual₃ a b c b≤a c≤b
    rank/lemma : 
        sum-of-ranks (node a k (node b p (node c g d)))
      Nat.≤
        ((3 * (rank (node a k (node b p (node c g d))) ∸ rank (node a k b))) ∸ 1) + 
        sum-of-ranks (node (node (node a k b) p c) g d)
    rank/lemma = 
      let open Nat.≤-Reasoning in
      begin
        sum-of-ranks a + rank (node a k (node b p (node c g d))) + (sum-of-ranks b + rank (node b p (node c g d)) +
        (sum-of-ranks c + rank (node c g d) + sum-of-ranks d))
      ≡⟨ rank-arithmetic1 (sum-of-ranks a) (sum-of-ranks b) (sum-of-ranks c) (sum-of-ranks d) (rank (node a k (node b p (node c g d)))) (rank (node b p (node c g d))) (rank (node c g d)) ⟩
        (sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) +
        (rank (node a k (node b p (node c g d)))) +
        (rank (node b p (node c g d))) +
        (rank (node c g d))
      ≤⟨ +-mono-≤ (+-mono-≤ (+-monoʳ-≤ (sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) Nat.≤-refl) rank-y'≤rank-x') rank-z'≤rank-x' ⟩
        (sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) +
        (rank (node a k (node b p (node c g d)))) +
        (rank (node a k (node b p (node c g d)))) +
        (rank (node a k (node b p (node c g d)))) 
      ≡⟨ Nat.+-identityʳ ((sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) +
          (rank (node a k (node b p (node c g d)))) + (rank (node a k (node b p (node c g d)))) +
            (rank (node a k (node b p (node c g d))))) ⟨
        (sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) +
        (rank (node a k (node b p (node c g d)))) +
        (rank (node a k (node b p (node c g d)))) +
        (rank (node a k (node b p (node c g d)))) + 0
      ≡⟨ Eq.cong (λ e → (sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) + (rank (node a k (node b p (node c g d)))) + (rank (node a k (node b p (node c g d)))) +
          (rank (node a k (node b p (node c g d)))) + e) (Eq.trans (Eq.sym (Nat.*-zeroˡ 3)) (Eq.cong (λ e → 3 * e) (Eq.sym (Nat.n∸n≡0 (rank (node a k b)))))) ⟩
        (sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) +
        (rank (node a k (node b p (node c g d)))) +
        (rank (node a k (node b p (node c g d)))) +
        (rank (node a k (node b p (node c g d)))) + 
        (3 * (rank (node a k b) ∸ rank (node a k b)))
      ≡⟨ rank≡ (sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) (rank (node a k (node b p (node c g d)))) (rank (node a k b)) rank-x<rank-x' 1≤rank-z ⟩
        (sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) +
        (1 + rank (node a k b)) +
        (rank (node a k b)) +
        (rank (node a k b)) + 
        ((3 * (rank (node a k (node b p (node c g d))) ∸ rank (node a k b))) ∸ 1)
      ≤⟨ +-monoˡ-≤ ((3 * (rank (node a k (node b p (node c g d))) ∸ rank (node a k b))) ∸ 1) (+-monoˡ-≤ (rank (node a k b)) 
          (+-mono-≤ (+-monoʳ-≤ (sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) (Nat.≤-trans rank-x<rank-x' (Nat.≤-reflexive rank-x'≡rank-z))) 
            rank-x≤rank-y)) ⟩
        (sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) +
        (rank (node (node (node a k b) p c) g d)) +
        (rank (node (node a k b) p c)) +
        (rank (node a k b)) + 
        ((3 * (rank (node a k (node b p (node c g d))) ∸ rank (node a k b))) ∸ 1)
      ≡⟨ rank-arithmetic2 (sum-of-ranks a) (sum-of-ranks b) (sum-of-ranks c) (sum-of-ranks d) (rank (node (node (node a k b) p c) g d)) (rank (node (node a k b) p c)) 
          (rank (node a k b)) ((3 * (rank (node a k (node b p (node c g d))) ∸ rank (node a k b))) ∸ 1) ⟩ 
        ((3 * (rank (node a k (node b p (node c g d))) ∸ rank (node a k b))) ∸ 1) + 
        (sum-of-ranks a + rank (node a k b) + sum-of-ranks b + rank (node (node a k b) p c) + sum-of-ranks c + 
        rank (node (node (node a k b) p c) g d) + sum-of-ranks d)
      ∎
      where
        rank-arithmetic1 : (a b c d e f g : val nat) → a + e + (b + f + (c + g + d)) ≡ (a + b + c + d) + e + f + g
        rank-arithmetic1 = arithmetic₁₃
        rank-arithmetic2 : (a b c d e f g h : val nat) → (a + b + c + d) + e + f + g + h ≡ h + (a + g + b + f + c + e + d)
        rank-arithmetic2 = arithmetic₁₄
        rank-y'≤rank-x' : rank (node b p (node c g d)) Nat.≤ rank (node a k (node b p (node c g d)))
        rank-y'≤rank-x' = ⌊log₂⌋-mono-≤ (Nat.m≤n+m (tree-size b + 1 + (tree-size c + 1 + tree-size d)) (tree-size a + 1))
        rank-z'≤rank-x' : rank (node c g d) Nat.≤ rank (node a k (node b p (node c g d)))
        rank-z'≤rank-x' = Nat.≤-trans (⌊log₂⌋-mono-≤ (Nat.m≤n+m (tree-size c + 1 + tree-size d) (tree-size b + 1))) rank-y'≤rank-x'
        rank-x'≡rank-z : rank (node a k (node b p (node c g d))) ≡ rank (node (node (node a k b) p c) g d)
        rank-x'≡rank-z = Eq.cong (λ e → ⌊log₂ e ⌋) size/lemma
        rank-x≤rank-y : rank (node a k b) Nat.≤ rank (node (node a k b) p c)
        rank-x≤rank-y = Nat.≤-trans (⌊log₂⌋-mono-≤ (Nat.m≤m+n (tree-size a + 1 + tree-size b) (1 + tree-size c))) 
          (Nat.≤-reflexive (Eq.cong (λ e → ⌊log₂ e ⌋) (Eq.sym (+-assoc (tree-size a + 1 + tree-size b) 1 (tree-size c)))))
        1≤rank-z : 1 Nat.≤ rank (node a k (node b p (node c g d)))
        1≤rank-z = 
          let open Nat.≤-Reasoning in
          begin
            1
          ≡⟨⟩
            ⌊log₂ 2 ⌋
          ≤⟨ ⌊log₂⌋-mono-≤ (Nat.m≤m+n 2 (tree-size a + tree-size b + tree-size c + tree-size d + 1)) ⟩
            ⌊log₂ ((1 + 1) + (tree-size a + tree-size b + tree-size c + tree-size d + 1)) ⌋
          ≡⟨ Eq.cong (λ e → ⌊log₂ e ⌋) (arithmetic (tree-size a) (tree-size b) (tree-size c) (tree-size d) 1) ⟩
            ⌊log₂ (tree-size a + 1 + (tree-size b + 1 + (tree-size c + 1 + tree-size d))) ⌋
          ≡⟨⟩
            rank (node a k (node b p (node c g d)))
          ∎
          where
            arithmetic : (a b c d e : val nat) → (e + e) + (a + b + c + d + e) ≡ a + e + (b + e + (c + e + d))
            arithmetic = arithmetic₁₅ 
        rank≡ : (a b c : val nat) → c < b → 1 Nat.≤ b → 
          a + b + b + b + (3 * (c ∸ c)) ≡ a + (1 + c) + c + c + ((3 * (b ∸ c)) ∸ 1)
        rank≡ a b c c<b 1≤b = arithmetic-manual₅ a b c c<b 1≤b
    phi/lemma : 
        sum-of-ranks (reconstruct (node a k (node b p (node c g d))) anc)
      Nat.≤
        ((3 * (rank (node a k (node b p (node c g d))) ∸ rank (node a k b))) ∸ 1) + 
        sum-of-ranks (reconstruct (node (node (node a k b) p c) g d) anc)
    phi/lemma = sum-ranks+x/lemma (node a k (node b p (node c g d))) (node (node (node a k b) p c) g d) anc 
      ((3 * (rank (node a k (node b p (node c g d))) ∸ rank (node a k b))) ∸ 1) size/lemma rank/lemma
... | tri≈ _ rank-x≡rank-x'' _ = 
  let
    rank-x   : val nat
    rank-x   = rank (node a k b)
    rank-y   : val nat
    rank-y   = rank (node (node a k b) p c)
    rank-z   : val nat
    rank-z   = rank (node (node (node a k b) p c) g d)
    rank-x'  : val nat
    rank-x'  = rank (node a k b)
    rank-y'  : val nat
    rank-y'  = rank (node (node a k b) p (node c g d))
    rank-z'  : val nat
    rank-z'  = rank (node c g d)
    rank-x'' : val nat
    rank-x'' = rank (node a k (node b p (node c g d)))
    rank-y'' : val nat
    rank-y'' = rank (node b p (node c g d))
    rank-z'' : val nat
    rank-z'' = rank (node c g d)
  in 
  let open ≤⁻-Reasoning (F (list nat)) in
  begin
    step (F _) 1 (
      bind (F _) (splay' a (node b p (node c g d)) anc k) (λ ((l' , r') , _) → 
        φ (node l' k r')))
  ≲⟨ step-monoʳ-≤⁻ 1 (splay'/amortized a (node b p (node c g d)) anc k) ⟩
    step (F _) 1 (
      step (F _) (1 + 3 * (rank (reconstruct (node a k (node b p (node c g d))) anc) ∸ rank-x''))
        (φ (reconstruct (node a k (node b p (node c g d))) anc)))
  ≡⟨⟩
    step (F _) (1 + 1 + 3 * (rank (reconstruct (node a k (node b p (node c g d))) anc) ∸ rank-x''))
      (φ (reconstruct (node a k (node b p (node c g d))) anc)) 
  ≡⟨ Eq.cong (λ e → step (F _) e (φ (reconstruct (node a k (node b p (node c g d))) anc))) 
      (Eq.cong (λ e → 1 + 1 + 3 * (e ∸ rank-x'')) 
        (rank/recon (node a k (node b p (node c g d))) (node (node (node a k b) p c) g d) anc size/lemma)) ⟩
    step (F _) (1 + 1 + 3 * (rank (reconstruct (node (node (node a k b) p c) g d) anc) ∸ rank-x''))
      (φ (reconstruct (node a k (node b p (node c g d))) anc)) 
  ≡⟨ Eq.cong (λ e → step (F _) e (φ (reconstruct (node a k (node b p (node c g d))) anc))) 
      (Eq.cong (λ e → 1 + 1 + 3 * (rank (reconstruct (node (node (node a k b) p c) g d) anc) ∸ e)) rank-x≡rank-x'') ⟨
    step (F _) (1 + 1 + 3 * (rank (reconstruct (node (node (node a k b) p c) g d) anc) ∸ rank-x))
      (φ (reconstruct (node a k (node b p (node c g d))) anc)) 
  ≡⟨⟩
    step (F _) (1 + 1 + 3 * (rank (reconstruct (node (node (node a k b) p c) g d) anc) ∸ rank-x))
      (step (F _) (sum-of-ranks (reconstruct (node a k (node b p (node c g d))) anc)) 
        (ret (inord (reconstruct (node a k (node b p (node c g d))) anc))))
  ≡⟨ Eq.cong (λ e → step (F _) e (ret (inord (reconstruct (node a k (node b p (node c g d))) anc)))) 
      (arithmetic1 1  
        (3 * (rank (reconstruct (node (node (node a k b) p c) g d) anc) ∸ rank-x)) 
          (sum-of-ranks (reconstruct (node a k (node b p (node c g d))) anc))) ⟩
    step (F _) (1 + 3 * (rank (reconstruct (node (node (node a k b) p c) g d) anc) ∸ rank-x) + 
      (sum-of-ranks (reconstruct (node a k (node b p (node c g d))) anc) + 1))
        (ret (inord (reconstruct (node a k (node b p (node c g d))) anc)))
  ≲⟨ step-monoˡ-≤⁻ (ret (inord (reconstruct (node a k (node b p (node c g d))) anc))) 
      (+-monoʳ-≤ (1 + 3 * (rank (reconstruct (node (node (node a k b) p c) g d) anc) ∸ rank-x)) phi/lemma) ⟩
    step (F _) (1 + 3 * (rank (reconstruct (node (node (node a k b) p c) g d) anc) ∸ rank-x) + 
      sum-of-ranks (reconstruct (node (node (node a k b) p c) g d) anc))
        (ret (inord (reconstruct (node a k (node b p (node c g d))) anc)))
  ≡⟨⟩
    step (F _) (1 + 3 * (rank (reconstruct (node (node (node a k b) p c) g d) anc) ∸ rank-x))
      (step (F _) (sum-of-ranks (reconstruct (node (node (node a k b) p c) g d) anc))
        (ret (inord (reconstruct (node a k (node b p (node c g d))) anc))))
  ≡⟨ Eq.cong (λ e → step (F _) (1 + 3 * (rank (reconstruct (node (node (node a k b) p c) g d) anc) ∸ rank-x)) e) 
      (Eq.cong (λ e → step (F _) (sum-of-ranks (reconstruct (node (node (node a k b) p c) g d) anc)) e) 
        (Eq.cong ret (inord/reconstruct 
          (node (node (node a k b) p c) g d)
          (node a k (node b p (node c g d)))
          anc 
          (zig/zig/inord/arith a b c d k p g)))) ⟨
    step (F _) (1 + 3 * (rank (reconstruct (node (node (node a k b) p c) g d) anc) ∸ rank-x))
      (step (F _) (sum-of-ranks (reconstruct (node (node (node a k b) p c) g d) anc))
        (ret (inord (reconstruct (node (node (node a k b) p c) g d) anc))))
  ≡⟨⟩
    step (F _) (1 + 3 * (rank (reconstruct (node (node (node a k b) p c) g d) anc) ∸ rank-x)) 
      (φ (reconstruct (node (node (node a k b) p c) g d) anc))
  ∎
  where
    arithmetic1 : (a b c : val nat) → a + a + b + c ≡ (a + b) + (c + a)
    arithmetic1 = arithmetic₅₃
    size/lemma : tree-size (node a k (node b p (node c g d))) ≡ tree-size (node (node (node a k b) p c) g d)
    size/lemma = 
      let open ≡-Reasoning in
      begin
        tree-size a + 1 + (tree-size b + 1 + (tree-size c + 1 + tree-size d))
      ≡⟨ Eq.cong (λ e → tree-size a + 1 + e) (Nat.+-assoc (tree-size b) 1 (tree-size c + 1 + tree-size d)) ⟩
        tree-size a + 1 + (tree-size b + (1 + (tree-size c + 1 + tree-size d)))
      ≡⟨ Nat.+-assoc (tree-size a + 1) (tree-size b) (1 + (tree-size c + 1 + tree-size d)) ⟨
        tree-size a + 1 + tree-size b + (1 + (tree-size c + 1 + tree-size d))
      ≡⟨ Nat.+-assoc (tree-size a + 1 + tree-size b) 1 (tree-size c + 1 + tree-size d) ⟨
        tree-size a + 1 + tree-size b + 1 + (tree-size c + 1 + tree-size d)
      ≡⟨ Eq.cong (λ e → tree-size a + 1 + tree-size b + 1 + e) (Nat.+-assoc (tree-size c) 1 (tree-size d)) ⟩
        tree-size a + 1 + tree-size b + 1 + (tree-size c + (1 + tree-size d))
      ≡⟨ Nat.+-assoc (tree-size a + 1 + tree-size b + 1) (tree-size c) (1 + tree-size d) ⟨
        tree-size a + 1 + tree-size b + 1 + tree-size c + (1 + tree-size d)
      ≡⟨ Nat.+-assoc (tree-size a + 1 + tree-size b + 1 + tree-size c) 1 (tree-size d) ⟨
        tree-size a + 1 + tree-size b + 1 + tree-size c + 1 + tree-size d
      ∎
    rank/lemma : 
        sum-of-ranks (node a k (node b p (node c g d))) + 1
      Nat.≤
        sum-of-ranks (node (node (node a k b) p c) g d)
    rank/lemma = 
      let open Nat.≤-Reasoning in
      begin
        sum-of-ranks a + rank (node a k (node b p (node c g d))) + (sum-of-ranks b + rank (node b p (node c g d)) +
        (sum-of-ranks c + rank (node c g d) + sum-of-ranks d)) + 1
      ≡⟨ rank-arithmetic1 (sum-of-ranks a) (sum-of-ranks b) (sum-of-ranks c) (sum-of-ranks d) (rank (node a k (node b p (node c g d)))) 
          (rank (node b p (node c g d))) (rank (node c g d)) 1 ⟩ 
        (sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) + 
        (rank (node a k (node b p (node c g d)))) +
        (rank (node b p (node c g d))) +
        (rank (node c g d) + 1)
      ≤⟨ +-mono-≤ (+-mono-≤ (+-monoʳ-≤ (sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) 
          (Nat.≤-reflexive (Eq.sym (rank-x≡rank-x'')))) rank-y''≤rank-y) rank-z''<rank-z ⟩
        (sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) +
        (rank (node a k b)) +
        (rank (node (node a k b) p c)) +
        (rank (node (node (node a k b) p c) g d))
      ≡⟨ rank-arithmetic2 (sum-of-ranks a) (sum-of-ranks b) (sum-of-ranks c) (sum-of-ranks d) (rank (node a k b)) (rank (node (node a k b) p c)) 
          (rank (node (node (node a k b) p c) g d)) ⟩
        sum-of-ranks a + rank (node a k b) + sum-of-ranks b + rank (node (node a k b) p c) + sum-of-ranks c + 
        rank (node (node (node a k b) p c) g d) + sum-of-ranks d
      ∎
      where
        rank-arithmetic1 : (a b c d e f g h : val nat) → a + e + (b + f + (c + g + d)) + h ≡ (a + b + c + d) + e + f + (g + h)
        rank-arithmetic1 = arithmetic₁₆
        rank-arithmetic2 : (a b c d e f g : val nat) → (a + b + c + d) + e + f + g ≡ a + e + b + f + c + g + d
        rank-arithmetic2 = arithmetic₁₇
        rank-y''≤rank-y : rank (node b p (node c g d)) Nat.≤ rank (node (node a k b) p c)
        rank-y''≤rank-y = 
          let open Nat.≤-Reasoning in
          begin
            rank (node b p (node c g d))
          ≤⟨ ⌊log₂⌋-mono-≤ (Nat.m≤n+m (tree-size b + 1 + (tree-size c + 1 + tree-size d)) (tree-size a + 1)) ⟩
            rank (node a k (node b p (node c g d)))
          ≡⟨ rank-x≡rank-x'' ⟨ 
            rank (node a k b)
          ≡⟨ Nat.≤-antisym rank-y≤rank-x rank-x≤rank-y ⟨
            rank (node (node a k b) p c)
          ∎
          where
            rank-y≤rank-x : rank (node (node a k b) p c) Nat.≤ rank (node a k b)
            rank-y≤rank-x = 
              let open Nat.≤-Reasoning in
              begin
                rank (node (node a k b) p c)
              ≤⟨ Nat.≤-trans (⌊log₂⌋-mono-≤ (Nat.m≤m+n (((tree-size a + 1 + tree-size b) + 1 + tree-size c)) (1 + tree-size d))) 
                  (Nat.≤-reflexive (Eq.cong (λ e → ⌊log₂ e ⌋) (Eq.sym (Nat.+-assoc ((tree-size a + 1 + tree-size b) + 1 + tree-size c) 1 (tree-size d))))) ⟩
                rank (node (node (node a k b) p c) g d)
              ≡⟨ Eq.cong (λ e → ⌊log₂ e ⌋) size/lemma ⟨
                rank (node a k (node b p (node c g d)))  
              ≡⟨ rank-x≡rank-x'' ⟨
                rank (node a k b)
              ∎
            rank-x≤rank-y : rank (node a k b) Nat.≤ rank (node (node a k b) p c)
            rank-x≤rank-y = Nat.≤-trans (⌊log₂⌋-mono-≤ (Nat.m≤m+n (tree-size a + 1 + tree-size b) (1 + tree-size c))) 
              (Nat.≤-reflexive (Eq.cong (λ e → ⌊log₂ e ⌋) (Eq.sym (Nat.+-assoc (tree-size a + 1 + tree-size b) 1 (tree-size c)))))
        rank-z''<rank-z : rank (node c g d) + 1 Nat.≤ rank (node (node (node a k b) p c) g d)
        rank-z''<rank-z = 
          let open Nat.≤-Reasoning in
          begin
            rank (node c g d) + 1
          ≡⟨ Nat.+-comm (rank (node c g d)) 1 ⟩ 
            suc (rank (node c g d))
          ≤⟨ Nat.≤∧≢⇒< rank-z''≤rank-y' rank-z''≢rank-y' ⟩
            rank (node (node a k b) p (node c g d))
          ≡⟨ rank-y'≡rank-z ⟩
            rank (node (node (node a k b) p c) g d)
          ∎
          where
            rank-y'≡rank-z   : rank (node (node a k b) p (node c g d)) ≡ rank (node (node (node a k b) p c) g d)
            rank-y'≡rank-z   = 
              let open ≡-Reasoning in 
              begin
                rank (node (node a k b) p (node c g d))
              ≡⟨⟩
                ⌊log₂ (tree-size a + 1 + tree-size b + 1 + (tree-size c + 1 + tree-size d)) ⌋
              ≡⟨ Eq.cong (λ e → ⌊log₂ (tree-size a + 1 + tree-size b + 1 + e) ⌋) (Nat.+-assoc (tree-size c) 1 (tree-size d)) ⟩
                ⌊log₂ (tree-size a + 1 + tree-size b + 1 + (tree-size c + (1 + tree-size d))) ⌋
              ≡⟨ Eq.cong (λ e → ⌊log₂ e ⌋) (Nat.+-assoc (tree-size a + 1 + tree-size b + 1) (tree-size c) (1 + tree-size d)) ⟨
                ⌊log₂ (tree-size a + 1 + tree-size b + 1 + tree-size c + (1 + tree-size d)) ⌋
              ≡⟨ Eq.cong (λ e → ⌊log₂ e ⌋) (Nat.+-assoc (tree-size a + 1 + tree-size b + 1 + tree-size c) 1 (tree-size d)) ⟨
                ⌊log₂ (tree-size a + 1 + tree-size b + 1 + tree-size c + 1 + tree-size d) ⌋
              ≡⟨⟩
                rank (node (node (node a k b) p c) g d)
              ∎ 
            rank-z''≤rank-y' : rank (node c g d) Nat.≤ rank (node (node a k b) p (node c g d))
            rank-z''≤rank-y' = ⌊log₂⌋-mono-≤ 
              (Nat.m≤n+m (tree-size c + 1 + tree-size d) (tree-size a + 1 + tree-size b + 1))
            rank-z''≢rank-y' : rank (node c g d) ≢ rank (node (node a k b) p (node c g d))
            rank-z''≢rank-y' rank-z''≡rank-y' = Nat.<⇒≢ rank-z''<rank-y' rank-z''≡rank-y'
              where
                rank-z''<rank-y' : rank (node c g d) < rank (node (node a k b) p (node c g d))
                rank-z''<rank-y' = 
                  let open Nat.≤-Reasoning in
                  begin
                    suc (rank (node c g d))
                  ≡⟨ Nat.+-comm 1 (rank (node c g d)) ⟩
                    rank (node c g d) + 1
                  ≡⟨ Eq.cong (λ e → e + 1) (Eq.trans rank-z''≡rank-y' (Eq.trans rank-y'≡rank-z 
                      (Eq.trans (Eq.cong (λ e → ⌊log₂ e ⌋) (Eq.sym size/lemma)) (Eq.sym rank-x≡rank-x'')))) ⟩
                    rank (node a k b) + 1
                  ≤⟨ rank-rule (node a k b) {{node-size-nonzero {a} {k} {b}}} p (node c g d) {{node-size-nonzero {c} {g} {d}}} 
                      (Eq.trans rank-x≡rank-x'' (Eq.trans (Eq.cong (λ e → ⌊log₂ e ⌋) size/lemma) (Eq.trans (Eq.sym (rank-y'≡rank-z)) 
                        (Eq.sym (rank-z''≡rank-y'))))) ⟩  
                    rank (node (node a k b) p (node c g d))
                  ∎ 
    phi/lemma : 
        sum-of-ranks (reconstruct (node a k (node b p (node c g d))) anc) + 1
      Nat.≤
        sum-of-ranks (reconstruct (node (node (node a k b) p c) g d) anc)
    phi/lemma = sum-ranks+1/lemma (node a k (node b p (node c g d))) (node (node (node a k b) p c) g d) anc size/lemma rank/lemma
... | tri> _ _ rank-x>rank-x'  = ⊥-elim (Nat.≤⇒≯ rank-x≤rank-x' rank-x>rank-x')
  where
    rank-x≤rank-x' : rank (node a k b) Nat.≤ rank (node a k (node b p (node c g d)))
    rank-x≤rank-x' = 
      let open Nat.≤-Reasoning in
      begin
        ⌊log₂ (tree-size a + 1 + tree-size b) ⌋
      ≤⟨ ⌊log₂⌋-mono-≤ (Nat.m≤m+n (tree-size a + 1 + tree-size b) (tree-size c + 1 + tree-size d + 1)) ⟩
        ⌊log₂ ((tree-size a + 1 + tree-size b) + (tree-size c + 1 + tree-size d + 1)) ⌋
      ≡⟨ Eq.cong (λ e → ⌊log₂ e ⌋) (arithmetic (tree-size a) (tree-size b) (tree-size c) (tree-size d) 1) ⟩ 
        ⌊log₂ (tree-size a + 1 + (tree-size b + 1 + (tree-size c + 1 + tree-size d))) ⌋ 
      ∎
      where
        arithmetic : (a b c d e : val nat) → (a + e + b) + (c + e + d + e) ≡ a + e + (b + e + (c + e + d))
        arithmetic = arithmetic₁₈

-- zag-zig
splay'/amortized b c (Left p d ∷ Right a g ∷ anc) k with Nat.<-cmp (rank (node b k c)) (rank (node (node a g b) k (node c p d)))
... | tri< rank-x<rank-x' _ _ = 
  let 
    rank-x  : val nat
    rank-x  = rank (node b k c)
    rank-y  : val nat
    rank-y  = rank (node (node b k c) p d)
    rank-z  : val nat
    rank-z  = rank (node a g (node (node b k c) p d))
    rank-x' : val nat
    rank-x' = rank (node (node a g b) k (node c p d))
    rank-y' : val nat
    rank-y' = rank (node c p d)
    rank-z' : val nat
    rank-z' = rank (node a g b)
  in
  let open ≤⁻-Reasoning (F (list nat)) in
  begin
    step (F _) 1 (
      bind (F _) (splay' (node a g b) (node c p d) anc k) (λ ((l' , r') , _) → 
        φ (node l' k r')))
  ≲⟨ step-monoʳ-≤⁻ 1 (splay'/amortized (node a g b) (node c p d) anc k) ⟩
    step (F _) 1 (
      step (F _) (1 + 3 * (rank (reconstruct (node (node a g b) k (node c p d)) anc) ∸ rank-x')) 
        (φ (reconstruct (node (node a g b) k (node c p d)) anc)))
  ≡⟨⟩
    step (F _) (1 + 1 + 3 * (rank (reconstruct (node (node a g b) k (node c p d)) anc) ∸ rank-x')) 
      (φ (reconstruct (node (node a g b) k (node c p d)) anc))
  ≡⟨ Eq.cong (λ e → step (F _) e (φ (reconstruct (node (node a g b) k (node c p d)) anc))) 
      (Eq.cong (λ e → 1 + 1 + 3 * (e ∸ rank-x')) 
        (rank/recon (node (node a g b) k (node c p d)) (node a g (node (node b k c) p d)) anc size/lemma)) ⟩
    step (F _) (1 + 1 + 3 * (rank (reconstruct (node a g (node (node b k c) p d)) anc) ∸ rank-x')) 
      (φ (reconstruct (node (node a g b) k (node c p d)) anc))
  ≡⟨⟩
    step (F _) (1 + 1 + 3 * (rank (reconstruct (node a g (node (node b k c) p d)) anc) ∸ rank-x')) 
      (step (F _) (sum-of-ranks (reconstruct (node (node a g b) k (node c p d)) anc)) 
        (ret (inord (reconstruct (node (node a g b) k (node c p d)) anc))))
  ≡⟨⟩
    step (F _) (1 + 1 + 3 * (rank (reconstruct (node a g (node (node b k c) p d)) anc) ∸ rank-x') + 
      sum-of-ranks (reconstruct (node (node a g b) k (node c p d)) anc)) 
        (ret (inord (reconstruct (node (node a g b) k (node c p d)) anc)))
  ≲⟨ step-monoˡ-≤⁻ (ret (inord (reconstruct (node (node a g b) k (node c p d)) anc))) 
      (+-monoʳ-≤ (1 + 1 + 3 * (rank (reconstruct (node a g (node (node b k c) p d)) anc) ∸ rank-x')) 
        phi/lemma) ⟩
    step (F _) (1 + 1 + 3 * (rank (reconstruct (node a g (node (node b k c) p d)) anc) ∸ rank-x') + 
      (((3 * (rank-x' ∸ rank-x)) ∸ 1) + sum-of-ranks (reconstruct (node a g (node (node b k c) p d)) anc))) 
        (ret (inord (reconstruct (node (node a g b) k (node c p d)) anc)))
  ≡⟨ Eq.cong (λ e → step (F _) e (ret (inord (reconstruct (node (node a g b) k (node c p d)) anc)))) 
      (artihmetic2 1 (3 * (rank (reconstruct (node a g (node (node b k c) p d)) anc) ∸ rank-x')) 
        (3 * (rank-x' ∸ rank-x)) (sum-of-ranks (reconstruct (node a g (node (node b k c) p d)) anc)) 
          size-arith1) ⟩
    step (F _) ((1 ∸ 1) + 1 + ((3 * (rank (reconstruct (node a g (node (node b k c) p d)) anc) ∸ rank-x')) + 
      (3 * (rank-x' ∸ rank-x))) + sum-of-ranks (reconstruct (node a g (node (node b k c) p d)) anc)) 
        (ret (inord (reconstruct (node (node a g b) k (node c p d)) anc)))
  ≡⟨ Eq.cong (λ e → step (F _) (e + 1 + ((3 * (rank (reconstruct (node a g (node (node b k c) p d))  anc) ∸ rank-x')) +
      (3 * (rank-x' ∸ rank-x))) + sum-of-ranks (reconstruct (node a g (node (node b k c) p d)) anc))
        (ret (inord (reconstruct (node (node a g b) k (node c p d)) anc)))) (Nat.n∸n≡0 1) ⟩
    step (F _) (1 + ((3 * (rank (reconstruct (node a g (node (node b k c) p d)) anc) ∸ rank-x')) +
      (3 * (rank-x' ∸ rank-x))) + sum-of-ranks (reconstruct (node a g (node (node b k c) p d)) anc))
        (ret (inord (reconstruct (node (node a g b) k (node c p d)) anc)))
  ≡⟨ Eq.cong (λ e → step (F _) (1 + e + sum-of-ranks (reconstruct (node a g (node (node b k c) p d)) anc))
      (ret (inord (reconstruct (node (node a g b) k (node c p d)) anc)))) 
        (arithmetic3 (rank (reconstruct (node a g (node (node b k c) p d)) anc)) rank-x' rank-x
          (size-arith2 (node (node a g b) k (node c p d)) (node a g (node (node b k c) p d)) anc size/lemma) 
            (Nat.<⇒≤ rank-x<rank-x')) ⟩
    step (F _) (1 + (3 * (rank (reconstruct (node a g (node (node b k c) p d)) anc) ∸ rank-x)) +  
      sum-of-ranks (reconstruct (node a g (node (node b k c) p d)) anc))
        (ret (inord (reconstruct (node (node a g b) k (node c p d)) anc)))
  ≡⟨⟩
    step (F _) (1 + 3 * (rank (reconstruct (node a g (node (node b k c) p d)) anc) ∸ rank-x))
      (step (F _) (sum-of-ranks (reconstruct (node a g (node (node b k c) p d)) anc))
        (ret (inord (reconstruct (node (node a g b) k (node c p d)) anc))))
  ≡⟨ Eq.cong (λ e → step (F _) (1 + 3 * (rank (reconstruct (node a g (node (node b k c) p d)) anc) ∸ rank-x)) e) 
      (Eq.cong (λ e → step (F _) (sum-of-ranks (reconstruct (node a g (node (node b k c) p d)) anc)) e) 
        (Eq.cong ret (inord/reconstruct 
          (node a g (node (node b k c) p d)) 
          (node (node a g b) k (node c p d)) 
          anc 
          (zag/zig/inord/arith a b c d k p g)))) ⟨ 
    step (F _) (1 + 3 * (rank (reconstruct (node a g (node (node b k c) p d)) anc) ∸ rank-x))
      (step (F _) (sum-of-ranks (reconstruct (node a g (node (node b k c) p d)) anc))
        (ret (inord (reconstruct (node a g (node (node b k c) p d)) anc))))
  ≡⟨⟩
    step (F _) (1 + 3 * (rank (reconstruct (node a g (node (node b k c) p d)) anc) ∸ rank-x)) 
      (φ (reconstruct (node a g (node (node b k c) p d)) anc))
  ∎
  where
    arithmetic1 : (a b c d e : val nat) → a + e + b + e + (c + e + d) ≡ a + e + (b + e + c + e + d)
    arithmetic1 = arithmetic₃₆
    artihmetic2 : (a b c d : val nat) → a Nat.≤ c → a + a + b + ((c ∸ a) + d) ≡ (a ∸ a) + a + (b + c) + d
    artihmetic2 a b c d a≤c = arithmetic-manual₂ a b c d a≤c
    arithmetic3 : (a b c : val nat) → b Nat.≤ a → c Nat.≤ b → (3 * (a ∸ b)) + (3 * (b ∸ c)) ≡ (3 * (a ∸ c))
    arithmetic3 a b c b≤a c≤b = arithmetic-manual₃ a b c b≤a c≤b  
    size-arith1 : 1 Nat.≤ 3 * (rank (node (node a g b) k (node c p d)) ∸ rank (node b k c))
    size-arith1 = 
      let open Nat.≤-Reasoning in
      begin
        1
      ≤⟨ s≤s z≤n ⟩
        3
      ≤⟨ Nat.m≤m*n 3 (rank (node (node a g b) k (node c p d)) ∸ rank (node b k c)) 
          {{ >-nonZero (Nat.m<n⇒0<n∸m rank-x<rank-x') }}  ⟩
        3 * (rank (node (node a g b) k (node c p d)) ∸ rank (node b k c))
      ∎ 
    size-arith2 : (t₁ t₂ : Tree) (anc : List Context) → tree-size t₁ ≡ tree-size t₂ → 
      rank t₁ Nat.≤ rank (reconstruct t₂ anc)
    size-arith2 t₁ t₂ [] t₁≡t₂ = Nat.≤-reflexive (Eq.cong (λ e → ⌊log₂ e ⌋) t₁≡t₂)
    size-arith2 t₁ t₂ (Left k t ∷ anc) t₁≡t₂ = 
      let open Nat.≤-Reasoning in
      begin
        rank t₁
      ≡⟨⟩
        ⌊log₂ (tree-size t₁) ⌋
      ≤⟨ ⌊log₂⌋-mono-≤ (Nat.m≤m+n (tree-size t₁) (1 + tree-size t)) ⟩
        ⌊log₂ ((tree-size t₁) + (1 + tree-size t)) ⌋
      ≡⟨ Eq.cong (λ e → ⌊log₂ (e + (1 + tree-size t)) ⌋) t₁≡t₂ ⟩
        ⌊log₂ ((tree-size t₂) + (1 + tree-size t)) ⌋
      ≡⟨ Eq.cong (λ e → ⌊log₂ e ⌋) (Nat.+-assoc (tree-size t₂) 1 (tree-size t)) ⟨
        ⌊log₂ (tree-size t₂ + 1 + tree-size t) ⌋
      ≡⟨⟩
        rank (node t₂ k t)
      ≤⟨ size-arith2 (node t₂ k t) (node t₂ k t) anc refl ⟩
        rank (reconstruct (node t₂ k t) anc)
      ∎
    size-arith2 t₁ t₂ (Right t k ∷ anc) t₁≡t₂ = 
      let open Nat.≤-Reasoning in
      begin
        rank t₁
      ≡⟨⟩
        ⌊log₂ (tree-size t₁) ⌋
      ≤⟨ ⌊log₂⌋-mono-≤ (Nat.m≤n+m (tree-size t₁) (tree-size t + 1)) ⟩
        ⌊log₂ (tree-size t + 1 + tree-size t₁) ⌋
      ≡⟨ Eq.cong (λ e → ⌊log₂ ((tree-size t + 1) + e) ⌋) t₁≡t₂ ⟩
        ⌊log₂ (tree-size t + 1 + tree-size t₂) ⌋
      ≡⟨⟩
        rank (node t k t₂)
      ≤⟨ size-arith2 (node t k t₂) (node t k t₂) anc refl ⟩
        rank (reconstruct (node t k t₂) anc)
      ∎
    rank-x'-z : rank (node (node a g b) k (node c p d)) ≡ rank (node a g (node (node b k c) p d))
    rank-x'-z = let open ≡-Reasoning in
      begin
        rank (node (node a g b) k (node c p d))
      ≡⟨⟩
        ⌊log₂ ((tree-size a + 1 + tree-size b) + 1 + (tree-size c + 1 + tree-size d)) ⌋
      ≡⟨ Eq.cong (λ e → ⌊log₂ e ⌋) (arithmetic (tree-size a) (tree-size b) (tree-size c) (tree-size d) 1) ⟩
        ⌊log₂ (tree-size a + 1 + ((tree-size b + 1 + tree-size c) + 1 + tree-size d)) ⌋
      ≡⟨⟩
        rank (node a g (node (node b k c) p d))
      ∎
      where
        arithmetic : (a b c d e : val nat) → (a + e + b) + e + (c + e + d) ≡ a + e + ((b + e + c) + e + d)
        arithmetic = arithmetic₃₉
    size/lemma : tree-size (node (node a g b) k (node c p d)) ≡ tree-size (node a g (node (node b k c) p d))
    size/lemma = arithmetic1 (tree-size a) (tree-size b) (tree-size c) (tree-size d) 1
    rank/lemma : 
        sum-of-ranks (node (node a g b) k (node c p d))
      Nat.≤ 
        ((3 * (rank (node (node a g b) k (node c p d)) ∸ rank (node b k c))) ∸ 1) + 
        sum-of-ranks (node a g (node (node b k c) p d))
    rank/lemma = 
      let open Nat.≤-Reasoning in
      begin
        sum-of-ranks (node (node a g b) k (node c p d))
      ≡⟨⟩
        (sum-of-ranks a + rank (node a g b) + sum-of-ranks b) + 
        rank (node (node a g b) k (node c p d)) + 
        (sum-of-ranks c + rank (node c p d) + sum-of-ranks d)
      ≡⟨ rank-arithmetic1 (sum-of-ranks a) (rank (node a g b)) (sum-of-ranks b) 
          (rank (node (node a g b) k (node c p d))) (sum-of-ranks c) (rank (node c p d)) (sum-of-ranks d) ⟩
        (sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) +
        (rank (node c p d)) +
        (rank (node (node a g b) k (node c p d))) +
        (rank (node a g b))
      ≤⟨ +-mono-≤ (+-mono-≤ (+-monoʳ-≤ (sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) 
          rank-y'≤rank-y) rank-x'≤rank-z) rank-z'≤rank-z ⟩
        (sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) +
        (rank (node (node b k c) p d)) +
        (rank (node a g (node (node b k c) p d))) +
        (rank (node a g (node (node b k c) p d)))
      ≡⟨ Nat.+-identityʳ ((sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) +
          (rank (node (node b k c) p d)) + (rank (node a g (node (node b k c) p d))) +
            (rank (node a g (node (node b k c) p d)))) ⟨
        (sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) +
        (rank (node (node b k c) p d)) +
        (rank (node a g (node (node b k c) p d))) +
        (rank (node a g (node (node b k c) p d))) + 0
      ≡⟨ Eq.cong (λ e → (sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) +
          (rank (node (node b k c) p d)) + (rank (node a g (node (node b k c) p d))) +
            (rank (node a g (node (node b k c) p d))) + e) 
              (Eq.trans (Eq.sym (Nat.*-zeroˡ 2)) (Eq.cong (λ e → 2 * e) (Eq.sym (Nat.n∸n≡0 (rank (node b k c)))))) ⟩
        (sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) +
        (rank (node (node b k c) p d)) +
        (rank (node a g (node (node b k c) p d))) +
        (rank (node a g (node (node b k c) p d))) + 
        (2 * (rank (node b k c) ∸ rank (node b k c)))
      ≤⟨ rank≤ (sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) 
          (rank (node (node b k c) p d)) (rank (node a g (node (node b k c) p d))) (rank (node b k c))
            rank-x<rank-z 1≤rank-z ⟩
        (sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) +
        (1 + rank (node b k c)) +
        (rank (node (node b k c) p d)) +
        (rank (node b k c)) + 
        ((3 * ((rank (node a g (node (node b k c) p d))) ∸ (rank (node b k c)))) ∸ 1)
      ≤⟨ +-monoˡ-≤ ((3 * ((rank (node a g (node (node b k c) p d))) ∸ (rank (node b k c)))) ∸ 1) 
          (+-monoˡ-≤ (rank (node b k c)) (+-monoˡ-≤ (rank (node (node b k c) p d))
            (+-monoʳ-≤ (sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) 
              (Nat.≤-trans rank-x<rank-x' rank-x'≤rank-z)))) ⟩
        (sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) +
        (rank (node a g (node (node b k c) p d))) +
        (rank (node (node b k c) p d)) +
        (rank (node b k c)) + 
        ((3 * ((rank (node a g (node (node b k c) p d))) ∸ (rank (node b k c)))) ∸ 1)
      ≡⟨ Eq.cong (λ e → (sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) +
          (rank (node a g (node (node b k c) p d))) + (rank (node (node b k c) p d)) + 
            (rank (node b k c)) + e) (Eq.cong (λ e → ((3 * (e ∸ (rank (node b k c)))) ∸ 1)) 
              rank-x'-z) ⟨
        (sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) +
        (rank (node a g (node (node b k c) p d))) +
        (rank (node (node b k c) p d)) +
        (rank (node b k c)) + 
        ((3 * ((rank (node (node a g b) k (node c p d))) ∸ (rank (node b k c)))) ∸ 1)
      ≡⟨ rank-arithmetic2 (sum-of-ranks a) (sum-of-ranks b) (sum-of-ranks c) (sum-of-ranks d) 
          (rank (node a g (node (node b k c) p d))) (rank (node (node b k c) p d)) (rank (node b k c)) 
            ((3 * ((rank (node (node a g b) k (node c p d))) ∸ (rank (node b k c)))) ∸ 1) ⟩
        ((3 * ((rank (node (node a g b) k (node c p d))) ∸ (rank (node b k c)))) ∸ 1) + 
        (sum-of-ranks a + rank (node a g (node (node b k c) p d)) + (sum-of-ranks b + rank (node b k c) + 
        sum-of-ranks c + rank (node (node b k c) p d) + sum-of-ranks d))
      ≡⟨⟩
        ((3 * ((rank (node (node a g b) k (node c p d))) ∸ (rank (node b k c)))) ∸ 1) + 
        sum-of-ranks (node a g (node (node b k c) p d))
      ∎
      where 
        rank-arithmetic1 : (a b c d e f g : val nat) → (a + b + c) + d + (e + f + g) ≡ (a + c + e + g) + f + d + b
        rank-arithmetic1 = arithmetic₃₇
        rank-arithmetic2 : (a b c d e f g h : val nat) → (a + b + c + d) + e + f + g + h ≡ h + (a + e + (b + g + c + f + d))
        rank-arithmetic2 = arithmetic₃₈
        rank-z'≤rank-z : rank (node a g b) Nat.≤ rank (node a g (node (node b k c) p d))
        rank-z'≤rank-z = let open Nat.≤-Reasoning in
          begin
            rank (node a g b)
          ≡⟨⟩
            ⌊log₂ (tree-size a + 1 + tree-size b) ⌋ 
          ≤⟨ ⌊log₂⌋-mono-≤ (Nat.m≤m+n (tree-size a + 1 + tree-size b) (tree-size c + 1 + tree-size d + 1)) ⟩
            ⌊log₂ ((tree-size a + 1 + tree-size b) + (tree-size c + 1 + tree-size d + 1)) ⌋
          ≡⟨ Eq.cong (λ e → ⌊log₂ e ⌋) (arithmetic (tree-size a) (tree-size b) (tree-size c) (tree-size d) 1) ⟩
            ⌊log₂ (tree-size a + 1 + ((tree-size b + 1 + tree-size c) + 1 + tree-size d)) ⌋
          ≡⟨⟩
            rank (node a g (node (node b k c) p d))
          ∎
          where
            arithmetic : (a b c d e : val nat) → ((a + e + b) + (c + e + d + e)) ≡ a + e + ((b + e + c) + e + d)
            arithmetic = arithmetic₄₀
        rank-x'≤rank-z : rank (node (node a g b) k (node c p d)) Nat.≤ rank (node a g (node (node b k c) p d))
        rank-x'≤rank-z = Nat.≤-reflexive rank-x'-z
        rank-y'≤rank-y : rank (node c p d) Nat.≤ rank (node (node b k c) p d)
        rank-y'≤rank-y = let open Nat.≤-Reasoning in
          begin
            rank (node c p d)
          ≡⟨⟩
            ⌊log₂ (tree-size c + 1 + tree-size d) ⌋
          ≤⟨ ⌊log₂⌋-mono-≤ (Nat.m≤m+n (tree-size c + 1 + tree-size d) (tree-size b + 1)) ⟩
            ⌊log₂ ((tree-size c + 1 + tree-size d) + (tree-size b + 1)) ⌋
          ≡⟨ Eq.cong (λ e → ⌊log₂ e ⌋) (arithmetic (tree-size b) (tree-size c) (tree-size d) 1) ⟩
            ⌊log₂ ((tree-size b + 1 + tree-size c) + 1 + tree-size d) ⌋
          ≡⟨⟩
            rank (node (node b k c) p d)
          ∎
          where
            arithmetic : (b c d e : val nat) → (c + e + d) + (b + e) ≡ ((b + e + c) + e + d)
            arithmetic = arithmetic₄₁
        rank-x<rank-z : rank (node b k c) < rank (node a g (node (node b k c) p d))
        rank-x<rank-z = let open Nat.≤-Reasoning in
          begin
            suc (rank (node b k c))
          ≤⟨ rank-x<rank-x' ⟩
            rank (node (node a g b) k (node c p d))
          ≡⟨ rank-x'-z ⟩
            rank (node a g (node (node b k c) p d))
          ∎
        1≤rank-z : 1 Nat.≤ rank (node a g (node (node b k c) p d))
        1≤rank-z = let open Nat.≤-Reasoning in
          begin
            1
          ≡⟨⟩
            ⌊log₂ 2 ⌋
          ≤⟨ ⌊log₂⌋-mono-≤ (Nat.m≤m+n 2 (tree-size a + tree-size b + tree-size c + tree-size d + 1)) ⟩
            ⌊log₂ ((1 + 1) + (tree-size a + tree-size b + tree-size c + tree-size d + 1)) ⌋
          ≡⟨ Eq.cong (λ e → ⌊log₂ e ⌋) (arithmetic (tree-size a) (tree-size b) (tree-size c) (tree-size d) 1) ⟩
            ⌊log₂ (tree-size a + 1 + ((tree-size b + 1 + tree-size c) + 1 + tree-size d)) ⌋
          ≡⟨⟩
            rank (node a g (node (node b k c) p d))
          ∎
          where 
            arithmetic : (a b c d e : val nat) → (e + e) + (a + b + c + d + e) ≡ a + e + ((b + e + c) + e + d)
            arithmetic = arithmetic₄₂
        rank≤ : (a b c d : val nat) → d < c → 1 Nat.≤ c → 
          a + b + c + c + (2 * (d ∸ d)) Nat.≤ a + (1 + d) + b + d + ((3 * (c ∸ d)) ∸ 1)
        rank≤ a b c d d<c 1≤c = arithmetic-manual₄ a b c d d<c 1≤c
    phi/lemma : 
        sum-of-ranks (reconstruct (node (node a g b) k (node c p d)) anc)
      Nat.≤ 
        ((3 * (rank (node (node a g b) k (node c p d)) ∸ rank (node b k c))) ∸ 1) +
        sum-of-ranks (reconstruct (node a g (node (node b k c) p d)) anc)
    phi/lemma = sum-ranks+x/lemma (node (node a g b) k (node c p d)) (node a g (node (node b k c) p d)) 
      anc ((3 * (rank (node (node a g b) k (node c p d)) ∸ rank (node b k c)) ∸ 1)) size/lemma rank/lemma
... | tri≈ _ rank-x≡rank-x' _ = 
  let 
    rank-x  : val nat
    rank-x  = rank (node b k c)
    rank-y  : val nat
    rank-y  = rank (node (node b k c) p d)
    rank-z  : val nat
    rank-z  = rank (node a g (node (node b k c) p d))
    rank-x' : val nat
    rank-x' = rank (node (node a g b) k (node c p d))
    rank-y' : val nat
    rank-y' = rank (node c p d)
    rank-z' : val nat
    rank-z' = rank (node a g b)
  in
  let open ≤⁻-Reasoning (F (list nat)) in 
    begin
      step (F _) 1 (
        bind (F _) (splay' (node a g b) (node c p d) anc k) (λ ((l' , r') , _) → 
          φ (node l' k r')))
    ≲⟨ step-monoʳ-≤⁻ 1 (splay'/amortized (node a g b) (node c p d) anc k) ⟩
      step (F _) 1 (
        step (F _) (1 + 3 * (rank (reconstruct (node (node a g b) k (node c p d)) anc) ∸ rank-x'))
          (φ (reconstruct (node (node a g b) k (node c p d)) anc)))
    ≡⟨⟩
      step (F _) (1 + 1 + 3 * (rank (reconstruct (node (node a g b) k (node c p d)) anc) ∸ rank-x'))
        (φ (reconstruct (node (node a g b) k (node c p d)) anc))
    ≡⟨ Eq.cong (λ e → step (F _) e (φ (reconstruct (node (node a g b) k (node c p d)) anc))) 
        (Eq.cong (λ e → 1 + 1 + 3 * (e ∸ rank-x')) 
          (rank/recon (node (node a g b) k (node c p d)) (node a g (node (node b k c) p d)) anc size/lemma)) ⟩
      step (F _) (1 + 1 + 3 * (rank (reconstruct (node a g (node (node b k c) p d)) anc) ∸ rank-x'))
        (φ (reconstruct (node (node a g b) k (node c p d)) anc))
    ≡⟨ Eq.cong (λ e → step (F _) e (φ (reconstruct (node (node a g b) k (node c p d)) anc))) 
        (Eq.cong (λ e → 1 + 1 + 3 * (rank (reconstruct (node a g (node (node b k c) p d)) anc) ∸ e)) rank-x≡rank-x') ⟨
      step (F _) (1 + 1 + 3 * (rank (reconstruct (node a g (node (node b k c) p d)) anc) ∸ rank-x))
        (φ (reconstruct (node (node a g b) k (node c p d)) anc))
    ≡⟨⟩
      step (F _) (1 + 1 + 3 * (rank (reconstruct (node a g (node (node b k c) p d)) anc) ∸ rank-x))
        (step (F _) (sum-of-ranks (reconstruct (node (node a g b) k (node c p d)) anc)) 
          (ret (inord (reconstruct (node (node a g b) k (node c p d)) anc))))
    ≡⟨⟩
      step (F _) (1 + 1 + 3 * (rank (reconstruct (node a g (node (node b k c) p d)) anc) ∸ rank-x) + 
        sum-of-ranks (reconstruct (node (node a g b) k (node c p d)) anc))
          (ret (inord (reconstruct (node (node a g b) k (node c p d)) anc)))
    ≡⟨ Eq.cong (λ e → step (F _) e (ret (inord (reconstruct (node (node a g b) k (node c p d)) anc)))) 
        (arithmetic2 1 1 
          (3 * (rank (reconstruct (node a g (node (node b k c) p d)) anc) ∸ rank-x)) 
          (sum-of-ranks (reconstruct (node (node a g b) k (node c p d)) anc))) ⟩
      step (F _) (1 + 3 * (rank (reconstruct (node a g (node (node b k c) p d)) anc) ∸ rank-x) + 
        (sum-of-ranks (reconstruct (node (node a g b) k (node c p d)) anc) + 1))
          (ret (inord (reconstruct (node (node a g b) k (node c p d)) anc)))
    ≲⟨ step-monoˡ-≤⁻ (ret (inord (reconstruct (node (node a g b) k (node c p d)) anc))) 
        (+-monoʳ-≤ (1 + 3 * (rank (reconstruct (node a g (node (node b k c) p d)) anc) ∸ rank-x)) phi/lemma) ⟩
      step (F _) (1 + 3 * (rank (reconstruct (node a g (node (node b k c) p d)) anc) ∸ rank-x) + 
        sum-of-ranks (reconstruct (node a g (node (node b k c) p d)) anc))
          (ret (inord (reconstruct (node (node a g b) k (node c p d)) anc)))
    ≡⟨⟩
      step (F _) (1 + 3 * (rank (reconstruct (node a g (node (node b k c) p d)) anc) ∸ rank-x))
        (step (F _) (sum-of-ranks (reconstruct (node a g (node (node b k c) p d)) anc))
          (ret (inord (reconstruct (node (node a g b) k (node c p d)) anc))))
    ≡⟨ Eq.cong (λ e → step (F _) (1 + 3 * (rank (reconstruct (node a g (node (node b k c) p d)) anc) ∸ rank-x)) e) 
      (Eq.cong (λ e → step (F _) (sum-of-ranks (reconstruct (node a g (node (node b k c) p d)) anc)) e) 
        (Eq.cong ret (inord/reconstruct 
          (node a g (node (node b k c) p d))
          (node (node a g b) k (node c p d))
          anc 
          (zag/zig/inord/arith a b c d k p g)))) ⟨
      step (F _) (1 + 3 * (rank (reconstruct (node a g (node (node b k c) p d)) anc) ∸ rank-x))
        (step (F _) (sum-of-ranks (reconstruct (node a g (node (node b k c) p d)) anc))
          (ret (inord (reconstruct (node a g (node (node b k c) p d)) anc))))
    ≡⟨⟩
      step (F _) (1 + 3 * (rank (reconstruct (node a g (node (node b k c) p d)) anc) ∸ rank-x)) 
        (φ (reconstruct (node a g (node (node b k c) p d)) anc))
    ∎
    where
      arithmetic1 : (a b c d e : val nat) → a + e + b + e + (c + e + d) ≡ a + e + (b + e + c + e + d)
      arithmetic1 = arithmetic₃₆
      arithmetic2 : (a b c d : val nat) → a + b + c + d ≡ (a + c) + (d + b)
      arithmetic2 = arithmetic₂₇
      size/lemma : tree-size (node (node a g b) k (node c p d)) ≡ tree-size (node a g (node (node b k c) p d))
      size/lemma = arithmetic1 (tree-size a) (tree-size b) (tree-size c) (tree-size d) 1
      rank/lemma : 
          sum-of-ranks (node (node a g b) k (node c p d)) + 1
        Nat.≤
          sum-of-ranks (node a g (node (node b k c) p d))
      rank/lemma with Nat.<-cmp (rank (node c p d)) (rank (node (node a g b) k (node c p d)))
      ... | tri< rank-y'<rank-x' _ _ = 
        let open Nat.≤-Reasoning in
        begin
          sum-of-ranks (node (node a g b) k (node c p d)) + 1
        ≡⟨⟩
          ((sum-of-ranks a + rank (node a g b) + sum-of-ranks b) + 
          (rank (node (node a g b) k (node c p d))) + 
          (sum-of-ranks c + rank (node c p d) + sum-of-ranks d)) + 1
        ≡⟨ rank-arithmetic1 (sum-of-ranks a) (rank (node a g b)) (sum-of-ranks b) 
              (rank (node (node a g b) k (node c p d))) (sum-of-ranks c) (rank (node c p d)) (sum-of-ranks d) 1 ⟩
          (sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) +
          (rank (node c p d) + 1) +
          (rank (node (node a g b) k (node c p d))) + 
          (rank (node a g b))
        ≤⟨ +-monoˡ-≤ (rank (node a g b)) (+-monoˡ-≤ (rank (node (node a g b) k (node c p d))) 
            (+-monoʳ-≤ (sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) rank-y'-y)) ⟩
          (sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) +
          (rank (node (node b k c) p d)) +
          (rank (node (node a g b) k (node c p d))) +
          (rank (node a g b))
        ≡⟨ Eq.cong (λ e → (sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) + 
            (rank (node (node b k c) p d)) + e + (rank (node a g b))) rank-x'-z ⟩
          (sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) +
          (rank (node (node b k c) p d)) +
          (rank (node a g (node (node b k c) p d))) +
          (rank (node a g b))
        ≤⟨ +-monoʳ-≤ ((sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) + 
            (rank (node (node b k c) p d)) + (rank (node a g (node (node b k c) p d)))) rank-z'-x ⟩
          (sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) +
          (rank (node (node b k c) p d)) +
          (rank (node a g (node (node b k c) p d))) +
          (rank (node b k c))
        ≡⟨ rank-arithmetic2 (sum-of-ranks a) (sum-of-ranks b) (sum-of-ranks c) (sum-of-ranks d) 
            (rank (node (node b k c) p d)) (rank (node a g (node (node b k c) p d))) (rank (node b k c)) ⟩
          (sum-of-ranks a + rank (node a g (node (node b k c) p d)) + (sum-of-ranks b + rank (node b k c) + 
          sum-of-ranks c + rank (node (node b k c) p d) + sum-of-ranks d))
        ≡⟨⟩
          sum-of-ranks (node a g (node (node b k c) p d))
        ∎
        where
          rank-arithmetic1 : (a b c d e f g h : val nat) → ((a + b + c) + d + (e + f + g)) + h ≡ (a + c + e + g) + (f + h) + d + b
          rank-arithmetic1 = arithmetic₄₃
          rank-arithmetic2 : (a b c d e f g : val nat) → (a + b + c + d) + e + f + g ≡ (a + f + (b + g + c + e + d))
          rank-arithmetic2 = arithmetic₄₄
          rank-x'-z : rank (node (node a g b) k (node c p d)) ≡ rank (node a g (node (node b k c) p d))
          rank-x'-z = let open ≡-Reasoning in
            begin
              rank (node (node a g b) k (node c p d))
            ≡⟨⟩
              ⌊log₂ ((tree-size a + 1 + tree-size b) + 1 + (tree-size c + 1 + tree-size d)) ⌋
            ≡⟨ Eq.cong (λ e → ⌊log₂ e ⌋) (arithmetic (tree-size a) (tree-size b) (tree-size c) (tree-size d) 1) ⟩
              ⌊log₂ (tree-size a + 1 + ((tree-size b + 1 + tree-size c) + 1 + tree-size d)) ⌋
            ≡⟨⟩
              rank (node a g (node (node b k c) p d))
            ∎
            where
              arithmetic : (a b c d e : val nat) → ((a + e + b) + e + (c + e + d)) ≡ a + e + ((b + e + c) + e + d)
              arithmetic = arithmetic₄₅
          rank-y'-y : rank (node c p d) + 1 Nat.≤ rank (node (node b k c) p d)
          rank-y'-y = 
            let open Nat.≤-Reasoning in 
            begin
              rank (node c p d) + 1
            ≡⟨ Nat.+-comm (rank (node c p d)) 1 ⟩
              suc (rank (node c p d))
            ≤⟨ rank-y'<rank-x' ⟩
              rank (node (node a g b) k (node c p d))
            ≡⟨ rank-x'-z ⟩
              rank (node a g (node (node b k c) p d))
            ≡⟨ Nat.≤-antisym rank-z-y rank-y-z ⟩
              rank (node (node b k c) p d)
            ∎
            where 
              rank-z-y : rank (node a g (node (node b k c) p d)) Nat.≤ rank (node (node b k c) p d)
              rank-z-y = let open Nat.≤-Reasoning in
                begin
                  rank (node a g (node (node b k c) p d))
                ≡⟨ Eq.trans (Eq.sym (rank-x'-z)) (Eq.sym (rank-x≡rank-x')) ⟩
                  rank (node b k c)
                ≡⟨⟩
                  ⌊log₂ (tree-size b + 1 + tree-size c) ⌋
                ≤⟨ ⌊log₂⌋-mono-≤ (Nat.m≤n+m (tree-size b + 1 + tree-size c) (1 + tree-size d)) ⟩
                  ⌊log₂ ((1 + tree-size d) + (tree-size b + 1 + tree-size c)) ⌋
                ≡⟨ Eq.cong (λ e → ⌊log₂ e ⌋) (Nat.+-comm (1 + tree-size d) (tree-size b + 1 + tree-size c)) ⟩
                  ⌊log₂ ((tree-size b + 1 + tree-size c) + (1 + tree-size d)) ⌋
                ≡⟨ Eq.cong (λ e → ⌊log₂ e ⌋) (Nat.+-assoc (tree-size b + 1 + tree-size c) 1 (tree-size d)) ⟨
                  rank (node (node b k c) p d)
                ∎
              rank-y-z : rank (node (node b k c) p d) Nat.≤ rank (node a g (node (node b k c) p d))
              rank-y-z = let open Nat.≤-Reasoning in
                begin
                  rank (node (node b k c) p d)
                ≡⟨⟩ 
                  ⌊log₂ ((tree-size b + 1 + tree-size c) + 1 + tree-size d) ⌋
                ≤⟨ ⌊log₂⌋-mono-≤ (Nat.m≤n+m ((tree-size b + 1 + tree-size c) + 1 + tree-size d) (tree-size a + 1)) ⟩
                  ⌊log₂ (tree-size a + 1 + ((tree-size b + 1 + tree-size c) + 1 + tree-size d)) ⌋
                ≡⟨⟩
                  rank (node a g (node (node b k c) p d))
                ∎
          rank-z'-x : rank (node a g b) Nat.≤ rank (node b k c)
          rank-z'-x = let open Nat.≤-Reasoning in
            begin
              rank (node a g b)
            ≡⟨⟩
              ⌊log₂ (tree-size a + 1 + tree-size b) ⌋
            ≤⟨ ⌊log₂⌋-mono-≤ (Nat.m≤m+n (tree-size a + 1 + tree-size b) (1 + (tree-size c + 1 + tree-size d))) ⟩
              ⌊log₂ ((tree-size a + 1 + tree-size b) + (1 + (tree-size c + 1 + tree-size d))) ⌋
            ≡⟨ Eq.cong (λ e → ⌊log₂ e ⌋) (Nat.+-assoc (tree-size a + 1 + tree-size b) 1 (tree-size c + 1 + tree-size d)) ⟨
              ⌊log₂ ((tree-size a + 1 + tree-size b) + 1 + (tree-size c + 1 + tree-size d)) ⌋
            ≡⟨⟩
              rank (node (node a g b) k (node c p d))
            ≡⟨ rank-x≡rank-x' ⟨  
              rank (node b k c)
            ∎
      ... | tri≈ _ rank-y'≡rank-x' _ = 
        let open Nat.≤-Reasoning in
        begin
          sum-of-ranks (node (node a g b) k (node c p d)) + 1
        ≡⟨⟩ 
          ((sum-of-ranks a + rank (node a g b) + sum-of-ranks b) + 
          (rank (node (node a g b) k (node c p d))) + 
          (sum-of-ranks c + rank (node c p d) + sum-of-ranks d)) + 1
        ≡⟨ rank-arithmetic1 (sum-of-ranks a) (sum-of-ranks b) (sum-of-ranks c) (sum-of-ranks d) 
            (rank (node c p d)) (rank (node (node a g b) k (node c p d))) (rank (node a g b)) 1 ⟩ 
          (sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) +
          (rank (node c p d)) +
          (rank (node (node a g b) k (node c p d))) +
          (rank (node a g b) + 1)
        ≡⟨ Eq.cong (λ e → (sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) + e +
            (rank (node (node a g b) k (node c p d))) + (rank (node a g b) + 1)) rank-y'-y ⟩
          (sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) +
          (rank (node (node b k c) p d)) +
          (rank (node (node a g b) k (node c p d))) +
          (rank (node a g b) + 1)
        ≡⟨ Eq.cong (λ e → (sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) + 
            (rank (node (node b k c) p d)) + e + (rank (node a g b) + 1)) rank-x'-z ⟩ 
          (sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) +
          (rank (node (node b k c) p d)) +
          (rank (node a g (node (node b k c) p d))) +
          (rank (node a g b) + 1)
        ≤⟨ +-monoʳ-≤ ((sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) + 
            (rank (node (node b k c) p d)) + (rank (node a g (node (node b k c) p d)))) rank-z'-x ⟩
          (sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) +
          (rank (node (node b k c) p d)) +
          (rank (node a g (node (node b k c) p d))) +
          (rank (node b k c))
        ≡⟨ rank-arithmetic2 (sum-of-ranks a) (sum-of-ranks b) (sum-of-ranks c) (sum-of-ranks d) 
            (rank (node (node b k c) p d)) (rank (node a g (node (node b k c) p d))) (rank (node b k c)) ⟩ 
          (sum-of-ranks a + rank (node a g (node (node b k c) p d)) + (sum-of-ranks b + rank (node b k c) + 
          sum-of-ranks c + rank (node (node b k c) p d) + sum-of-ranks d))
        ≡⟨⟩
          sum-of-ranks (node a g (node (node b k c) p d))
        ∎
        where
          rank-arithmetic1 : (a b c d e f g h : val nat) → ((a + g + b) + f + (c + e + d)) + h ≡ (a + b + c + d) + e + f + (g + h)
          rank-arithmetic1 = arithmetic₄₆
          rank-arithmetic2 : (a b c d e f g : val nat) → (a + b + c + d) + e + f + g ≡ (a + f + (b + g + c + e + d))
          rank-arithmetic2 = arithmetic₄₄
          rank-x'-z : rank (node (node a g b) k (node c p d)) ≡ rank (node a g (node (node b k c) p d))
          rank-x'-z = let open ≡-Reasoning in
            begin
              rank (node (node a g b) k (node c p d))
            ≡⟨⟩
              ⌊log₂ ((tree-size a + 1 + tree-size b) + 1 + (tree-size c + 1 + tree-size d)) ⌋
            ≡⟨ Eq.cong (λ e → ⌊log₂ e ⌋) (arithmetic (tree-size a) (tree-size b) (tree-size c) (tree-size d) 1) ⟩
              ⌊log₂ (tree-size a + 1 + ((tree-size b + 1 + tree-size c) + 1 + tree-size d)) ⌋
            ≡⟨⟩
              rank (node a g (node (node b k c) p d))
            ∎
            where
              arithmetic : (a b c d e : val nat) → ((a + e + b) + e + (c + e + d)) ≡ a + e + ((b + e + c) + e + d)
              arithmetic = arithmetic₄₅
          rank-y'-y : rank (node c p d) ≡ rank (node (node b k c) p d)
          rank-y'-y = 
            let open ≡-Reasoning in 
            begin
              rank (node c p d)
            ≡⟨ rank-y'≡rank-x' ⟩
              rank (node (node a g b) k (node c p d))
            ≡⟨ rank-x'-z ⟩
              rank (node a g (node (node b k c) p d))
            ≡⟨ Nat.≤-antisym rank-z-y rank-y-z ⟩
              rank (node (node b k c) p d)
            ∎
            where
              rank-z-y : rank (node a g (node (node b k c) p d)) Nat.≤ rank (node (node b k c) p d)
              rank-z-y = let open Nat.≤-Reasoning in
                begin
                  rank (node a g (node (node b k c) p d))
                ≡⟨ Eq.trans (Eq.sym (rank-x'-z)) (Eq.sym (rank-x≡rank-x')) ⟩
                  rank (node b k c)
                ≡⟨⟩
                  ⌊log₂ (tree-size b + 1 + tree-size c) ⌋
                ≤⟨ ⌊log₂⌋-mono-≤ (Nat.m≤m+n (tree-size b + 1 + tree-size c) (1 + tree-size d)) ⟩
                  ⌊log₂ ((tree-size b + 1 + tree-size c) + (1 + tree-size d)) ⌋
                ≡⟨ Eq.cong (λ e → ⌊log₂ e ⌋) (Nat.+-assoc (tree-size b + 1 + tree-size c) 1 (tree-size d)) ⟨ 
                  ⌊log₂ ((tree-size b + 1 + tree-size c) + 1 + tree-size d) ⌋
                ≡⟨⟩
                  rank (node (node b k c) p d)
                ∎
              rank-y-z : rank (node (node b k c) p d) Nat.≤ rank (node a g (node (node b k c) p d))
              rank-y-z = let open Nat.≤-Reasoning in
                begin
                  rank (node (node b k c) p d)
                ≡⟨⟩
                  ⌊log₂ ((tree-size b + 1 + tree-size c) + 1 + tree-size d) ⌋
                ≤⟨ ⌊log₂⌋-mono-≤ (Nat.m≤n+m ((tree-size b + 1 + tree-size c) + 1 + tree-size d) (tree-size a + 1)) ⟩
                  ⌊log₂ (tree-size a + 1 + ((tree-size b + 1 + tree-size c) + 1 + tree-size d)) ⌋
                ≡⟨⟩
                  rank (node a g (node (node b k c) p d))
                ∎
          rank-z'-x : rank (node a g b) + 1 Nat.≤ rank (node b k c)
          rank-z'-x = 
            let open Nat.≤-Reasoning in
            begin
              rank (node a g b) + 1
            ≡⟨ Nat.+-comm (rank (node a g b)) 1 ⟩
              suc (rank (node a g b))
            ≤⟨ Nat.≤∧≢⇒< rank-z'≤rank-x' rank-z'≢rank-x' ⟩
              rank (node (node a g b) k (node c p d))
            ≡⟨ rank-x≡rank-x' ⟨
              rank (node b k c)
            ∎
            where
              rank-z'≤rank-x' : rank (node a g b) Nat.≤ rank (node (node a g b) k (node c p d))
              rank-z'≤rank-x' = let open Nat.≤-Reasoning in
                begin
                  rank (node a g b)
                ≡⟨⟩
                  ⌊log₂ (tree-size a + 1 + tree-size b) ⌋
                ≤⟨ ⌊log₂⌋-mono-≤ (Nat.m≤m+n (tree-size a + 1 + tree-size b) (1 + (tree-size c + 1 + tree-size d))) ⟩
                  ⌊log₂ ((tree-size a + 1 + tree-size b) + (1 + (tree-size c + 1 + tree-size d))) ⌋
                ≡⟨ Eq.cong (λ e → ⌊log₂ e ⌋) (Nat.+-assoc (tree-size a + 1 + tree-size b) 1 (tree-size c + 1 + tree-size d)) ⟨
                  ⌊log₂ ((tree-size a + 1 + tree-size b) + 1 + (tree-size c + 1 + tree-size d)) ⌋
                ≡⟨⟩
                  rank (node (node a g b) k (node c p d))
                ∎
              rank-z'≢rank-x' : rank (node a g b) ≢ rank (node (node a g b) k (node c p d))
              rank-z'≢rank-x' rank-z'≡rank-x' = Nat.<⇒≢ rank-z<rank-x' rank-z'≡rank-x'
                where
                  rank-z<rank-x' : rank (node a g b) < rank (node (node a g b) k (node c p d))
                  rank-z<rank-x' = let open Nat.≤-Reasoning in
                    begin
                      suc (rank (node a g b))
                    ≡⟨ Nat.+-comm 1 (rank (node a g b)) ⟩
                      rank (node a g b) + 1
                    ≤⟨ rank-rule (node a g b) {{node-size-nonzero {a} {g} {b}}} k 
                        (node c p d) {{node-size-nonzero {c} {p} {d}}} (Eq.trans rank-z'≡rank-x' (Eq.sym rank-y'≡rank-x')) ⟩
                      rank (node (node a g b) k (node c p d))
                    ∎
      ... | tri> _ _ rank-y'>rank-x' = ⊥-elim (Nat.≤⇒≯ rank-y'≤rank-x' rank-y'>rank-x')
        where
          rank-y'≤rank-x' : rank (node c p d) Nat.≤ rank (node (node a g b) k (node c p d))
          rank-y'≤rank-x' = 
            let open Nat.≤-Reasoning in
            begin
              rank (node c p d)
            ≡⟨⟩
              ⌊log₂ (tree-size c + 1 + tree-size d) ⌋
            ≤⟨ ⌊log₂⌋-mono-≤ (Nat.m≤n+m (tree-size c + 1 + tree-size d) (tree-size a + 1 + tree-size b + 1)) ⟩
              ⌊log₂ ((tree-size a + 1 + tree-size b + 1) + (tree-size c + 1 + tree-size d)) ⌋
            ≡⟨⟩
              rank (node (node a g b) k (node c p d))
            ∎
      phi/lemma : 
          sum-of-ranks (reconstruct (node (node a g b) k (node c p d)) anc) + 1 
        Nat.≤
          sum-of-ranks (reconstruct (node a g (node (node b k c) p d)) anc)
      phi/lemma = sum-ranks+1/lemma 
        (node (node a g b) k (node c p d)) (node a g (node (node b k c) p d)) anc size/lemma rank/lemma
... | tri> _ _ rank-x>rank-x' = ⊥-elim (Nat.≤⇒≯ rank-x≤rank-x' rank-x>rank-x')
  where
    rank-x≤rank-x' : rank (node b k c) Nat.≤ rank (node (node a g b) p (node c p d))
    rank-x≤rank-x' = 
      let open Nat.≤-Reasoning in 
      begin
        rank (node b k c)
      ≡⟨⟩
        ⌊log₂ (tree-size b + 1 + tree-size c) ⌋
      ≤⟨ ⌊log₂⌋-mono-≤ (Nat.m≤m+n (tree-size b + 1 + tree-size c) (tree-size a + 1 + tree-size d + 1)) ⟩ 
        ⌊log₂ (tree-size b + 1 + tree-size c) + (tree-size a + 1 + tree-size d + 1) ⌋
      ≡⟨ Eq.cong (λ e → ⌊log₂ e ⌋) (arithmetic (tree-size a) (tree-size b) (tree-size c) (tree-size d) 1) ⟩
        ⌊log₂ ((tree-size a + 1 + tree-size b) + 1 + (tree-size c + 1 + tree-size d)) ⌋
      ≡⟨⟩
        rank (node (node a g b) k (node c p d))
      ∎
      where
        arithmetic : (a b c d e : val nat) → (b + e + c) + (a + e + d + e) ≡ ((a + e + b) + e + (c + e + d))
        arithmetic = arithmetic₄₈

-- zig-zag
splay'/amortized b c (Right a p ∷ Left g d ∷ anc) k with Nat.<-cmp (rank (node b k c)) (rank (node (node a p b) k (node c g d)))
... | tri< rank-x<rank-x' _ _ = 
  let
    rank-x  : val nat
    rank-x  = rank (node b k c)
    rank-y  : val nat
    rank-y  = rank (node a p (node b k c))
    rank-z  : val nat
    rank-z  = rank (node (node a p (node b k c)) g d)
    rank-x' : val nat
    rank-x' = rank (node (node a p b) k (node c g d))
    rank-y' : val nat
    rank-y' = rank (node a p b)
    rank-z' : val nat
    rank-z' = rank (node c g d)
  in 
  let open ≤⁻-Reasoning (F (list nat)) in
  begin
    step (F _) 1 (
      bind (F _) (splay' (node a p b) (node c g d) anc k) (λ ((l' , r') , _) → 
        φ (node l' k r')))
  ≲⟨ step-monoʳ-≤⁻ 1 (splay'/amortized (node a p b) (node c g d) anc k) ⟩
    step (F _) 1 (
      step (F _) (1 + 3 * (rank (reconstruct (node (node a p b) k (node c g d)) anc) ∸ rank-x'))
        (φ (reconstruct (node (node a p b) k (node c g d)) anc)))
  ≡⟨⟩
    step (F _) (1 + 1 + 3 * (rank (reconstruct (node (node a p b) k (node c g d)) anc) ∸ rank-x'))
      (φ (reconstruct (node (node a p b) k (node c g d)) anc)) 
  ≡⟨ Eq.cong (λ e → step (F _) e (φ (reconstruct (node (node a p b) k (node c g d)) anc))) 
      (Eq.cong (λ e → 1 + 1 + 3 * (e ∸ rank-x')) 
        (rank/recon (node (node a p b) k (node c g d)) (node (node a p (node b k c)) g d) anc size/lemma)) ⟩
    step (F _) (1 + 1 + 3 * (rank (reconstruct (node (node a p (node b k c)) g d) anc) ∸ rank-x'))
      (φ (reconstruct (node (node a p b) k (node c g d)) anc)) 
  ≡⟨⟩
    step (F _) (1 + 1 + 3 * (rank (reconstruct (node (node a p (node b k c)) g d) anc) ∸ rank-x'))
      (step (F _) (sum-of-ranks (reconstruct (node (node a p b) k (node c g d)) anc)) 
        (ret (inord (reconstruct (node (node a p b) k (node c g d)) anc))))
  ≡⟨⟩
    step (F _) (1 + 1 + 3 * (rank (reconstruct (node (node a p (node b k c)) g d) anc) ∸ rank-x') + 
      sum-of-ranks (reconstruct (node (node a p b) k (node c g d)) anc))
        (ret (inord (reconstruct (node (node a p b) k (node c g d)) anc)))
  ≲⟨ step-monoˡ-≤⁻ (ret (inord (reconstruct (node (node a p b) k (node c g d)) anc))) 
      (+-monoʳ-≤ (1 + 1 + 3 * (rank (reconstruct (node (node a p (node b k c)) g d) anc) ∸ rank-x')) 
        phi/lemma) ⟩
    step (F _) (1 + 1 + 3 * (rank (reconstruct (node (node a p (node b k c)) g d) anc) ∸ rank-x') +
      (((3 * (rank-x' ∸ rank-x)) ∸ 1) + sum-of-ranks (reconstruct (node (node a p (node b k c)) g d) anc)))
        (ret (inord (reconstruct (node (node a p b) k (node c g d)) anc)))
  ≡⟨ Eq.cong (λ e → step (F _) e (ret (inord (reconstruct (node (node a p b) k (node c g d)) anc)))) 
      (arithmetic2 1 (3 * (rank (reconstruct (node (node a p (node b k c)) g d) anc) ∸ rank-x')) 
        ((3 * (rank-x' ∸ rank-x))) (sum-of-ranks (reconstruct (node (node a p (node b k c)) g d) anc)) 
          size-arith1) ⟩
    step (F _) ((1 ∸ 1) + 1 + ((3 * (rank (reconstruct (node (node a p (node b k c)) g d) anc) ∸ rank-x')) +
      (3 * (rank-x' ∸ rank-x))) + sum-of-ranks (reconstruct (node (node a p (node b k c)) g d) anc))
        (ret (inord (reconstruct (node (node a p b) k (node c g d)) anc)))
  ≡⟨ Eq.cong (λ e → step (F _) (e + 1 + ((3 * (rank (reconstruct (node (node a p (node b k c)) g d) anc) ∸ rank-x')) +
      (3 * (rank-x' ∸ rank-x))) + sum-of-ranks (reconstruct (node (node a p (node b k c)) g d) anc))
        (ret (inord (reconstruct (node (node a p b) k (node c g d)) anc)))) (Nat.n∸n≡0 1) ⟩
     step (F _) (1 + ((3 * (rank (reconstruct (node (node a p (node b k c)) g d) anc) ∸ rank-x')) +
      (3 * (rank-x' ∸ rank-x))) + sum-of-ranks (reconstruct (node (node a p (node b k c)) g d) anc))
        (ret (inord (reconstruct (node (node a p b) k (node c g d)) anc)))
  ≡⟨ Eq.cong (λ e → step (F _) (1 + e + sum-of-ranks (reconstruct (node (node a p (node b k c)) g d) anc))
      (ret (inord (reconstruct (node (node a p b) k (node c g d)) anc)))) 
        (arithmetic3 (rank (reconstruct (node (node a p (node b k c)) g d) anc)) rank-x' rank-x
          (size-arith2 (node (node a p b) k (node c g d)) (node (node a p (node b k c)) g d) anc size/lemma) 
            (Nat.<⇒≤ rank-x<rank-x')) ⟩
    step (F _) (1 + (3 * (rank (reconstruct (node (node a p (node b k c)) g d) anc) ∸ rank-x)) +  
      sum-of-ranks (reconstruct (node (node a p (node b k c)) g d) anc))
        (ret (inord (reconstruct (node (node a p b) k (node c g d)) anc)))
  ≡⟨⟩
    step (F _) (1 + 3 * (rank (reconstruct (node (node a p (node b k c)) g d) anc) ∸ rank-x))
      (step (F _) (sum-of-ranks (reconstruct (node (node a p (node b k c)) g d) anc))
        (ret (inord (reconstruct (node (node a p b) k (node c g d)) anc))))
  ≡⟨ Eq.cong (λ e → step (F _) (1 + 3 * (rank (reconstruct (node (node a p (node b k c)) g d) anc) ∸ rank-x)) e) 
      (Eq.cong (λ e → step (F _) (sum-of-ranks (reconstruct (node (node a p (node b k c)) g d) anc)) e) 
        (Eq.cong ret (inord/reconstruct 
          (node (node a p (node b k c)) g d)
          (node (node a p b) k (node c g d))
          anc 
          (zig/zag/inord/arith a b c d k p g)))) ⟨
    step (F _) (1 + 3 * (rank (reconstruct (node (node a p (node b k c)) g d) anc) ∸ rank-x))
      (step (F _) (sum-of-ranks (reconstruct (node (node a p (node b k c)) g d) anc))
        (ret (inord (reconstruct (node (node a p (node b k c)) g d) anc))))
  ≡⟨⟩
    step (F _) (1 + 3 * (rank (reconstruct (node (node a p (node b k c)) g d) anc) ∸ rank-x)) 
      (φ (reconstruct (node (node a p (node b k c)) g d) anc))
  ∎
  where
    arithmetic1 : (a b c d e f g : val nat) → a + b + c + d + (e + f + g) ≡ a + b + (c + d + e) + f + g
    arithmetic1 = arithmetic₁₉
    size/lemma : tree-size (node (node a p b) k (node c g d)) ≡ tree-size (node (node a p (node b k c)) g d)
    size/lemma = arithmetic1 (tree-size a) 1 (tree-size b) 1 (tree-size c) 1 (tree-size d)
    size-arith1 : 1 Nat.≤ 3 * (rank (node (node a p b) k (node c g d)) ∸ rank (node b k c))
    size-arith1 = 
      let open Nat.≤-Reasoning in
      begin
        1
      ≤⟨ s≤s z≤n ⟩
        3
      ≤⟨ Nat.m≤m*n 3 (rank (node (node a p b) k (node c g d)) ∸ rank (node b k c)) 
          {{ >-nonZero (Nat.m<n⇒0<n∸m rank-x<rank-x') }}  ⟩
        3 * (rank (node (node a p b) k (node c g d)) ∸ rank (node b k c))
      ∎
    rank-x'-z : rank (node (node a p b) k (node c g d)) ≡ rank (node (node a p (node b k c)) g d)
    rank-x'-z = 
      let open ≡-Reasoning in
      begin
        rank (node (node a p b) k (node c g d))
      ≡⟨⟩
        ⌊log₂ ((tree-size a + 1 + tree-size b) + 1 + (tree-size c + 1 + tree-size d)) ⌋
      ≡⟨ Eq.cong (λ e → ⌊log₂ e ⌋) (arithmetic (tree-size a) 1 (tree-size b) 1 (tree-size c) 1 (tree-size d)) ⟩
        ⌊log₂ ((tree-size a + 1 + (tree-size b + 1 + tree-size c)) + 1 + tree-size d) ⌋
      ≡⟨⟩
        rank (node (node a p (node b k c)) g d)
      ∎
      where
        arithmetic : (a b c d e f g : val nat) → (a + b + c) + d + (e + f + g) ≡ (a + b + (c + d + e)) + f + g
        arithmetic = arithmetic₂₀
    size-arith2 : (t₁ t₂ : Tree) (anc : List Context) → tree-size t₁ ≡ tree-size t₂ → 
      rank t₁ Nat.≤ rank (reconstruct t₂ anc)
    size-arith2 t₁ t₂ [] t₁≡t₂ = Nat.≤-reflexive (Eq.cong (λ e → ⌊log₂ e ⌋) t₁≡t₂)
    size-arith2 t₁ t₂ (Left k t ∷ anc) t₁≡t₂ = 
      let open Nat.≤-Reasoning in
      begin
        rank t₁
      ≡⟨⟩
        ⌊log₂ (tree-size t₁) ⌋
      ≤⟨ ⌊log₂⌋-mono-≤ (Nat.m≤m+n (tree-size t₁) (1 + tree-size t)) ⟩
        ⌊log₂ ((tree-size t₁) + (1 + tree-size t)) ⌋
      ≡⟨ Eq.cong (λ e → ⌊log₂ (e + (1 + tree-size t)) ⌋) t₁≡t₂ ⟩
        ⌊log₂ ((tree-size t₂) + (1 + tree-size t)) ⌋
      ≡⟨ Eq.cong (λ e → ⌊log₂ e ⌋) (Nat.+-assoc (tree-size t₂) 1 (tree-size t)) ⟨
        ⌊log₂ (tree-size t₂ + 1 + tree-size t) ⌋
      ≡⟨⟩
        rank (node t₂ k t)
      ≤⟨ size-arith2 (node t₂ k t) (node t₂ k t) anc refl ⟩
        rank (reconstruct (node t₂ k t) anc)
      ∎
    size-arith2 t₁ t₂ (Right t k ∷ anc) t₁≡t₂ = 
      let open Nat.≤-Reasoning in
      begin
        rank t₁
      ≡⟨⟩
        ⌊log₂ (tree-size t₁) ⌋
      ≤⟨ ⌊log₂⌋-mono-≤ (Nat.m≤n+m (tree-size t₁) (tree-size t + 1)) ⟩
        ⌊log₂ (tree-size t + 1 + tree-size t₁) ⌋
      ≡⟨ Eq.cong (λ e → ⌊log₂ ((tree-size t + 1) + e) ⌋) t₁≡t₂ ⟩
        ⌊log₂ (tree-size t + 1 + tree-size t₂) ⌋
      ≡⟨⟩
        rank (node t k t₂)
      ≤⟨ size-arith2 (node t k t₂) (node t k t₂) anc refl ⟩
        rank (reconstruct (node t k t₂) anc)
      ∎
    arithmetic2 : (a b c d : val nat) → a Nat.≤ c → a + a + b + ((c ∸ a) + d) ≡ (a ∸ a) + a + (b + c) + d
    arithmetic2 a b c d a≤c = arithmetic-manual₂ a b c d a≤c
    arithmetic3 : (a b c : val nat) → b Nat.≤ a → c Nat.≤ b → (3 * (a ∸ b)) + (3 * (b ∸ c)) ≡ (3 * (a ∸ c))
    arithmetic3 a b c b≤a c≤b = 
      let open ≡-Reasoning in
      begin
        (3 * (a ∸ b)) + (3 * (b ∸ c))
      ≡⟨ Nat.*-distribˡ-+ 3 (a ∸ b) (b ∸ c) ⟨
        3 * ((a ∸ b) + (b ∸ c))
      ≡⟨ Eq.cong (λ e → 3 * e) (Nat.+-∸-assoc (a ∸ b) c≤b) ⟨  
        3 * (((a ∸ b) + b) ∸ c) 
      ≡⟨ Eq.cong (λ e → 3 * (e ∸ c)) (Nat.+-∸-comm b b≤a) ⟨
        3 * (((a + b) ∸ b) ∸ c)
      ≡⟨ Eq.cong (λ e → 3 * (e ∸ c)) (Nat.+-∸-assoc a {b} {b} Nat.≤-refl) ⟩ 
        3 * ((a + (b ∸ b)) ∸ c)
      ≡⟨ Eq.cong (λ e → 3 * ((a + e) ∸ c)) (Nat.n∸n≡0 b) ⟩
        3 * ((a + 0) ∸ c)
      ≡⟨ Eq.cong (λ e → 3 * (e ∸ c)) (Nat.+-comm a 0) ⟩
        3 * (a ∸ c) 
      ∎
    rank/lemma : 
        sum-of-ranks (node (node a p b) k (node c g d))
      Nat.≤
        ((3 * (rank (node (node a p b) k (node c g d)) ∸ rank (node b k c))) ∸ 1) + 
        sum-of-ranks (node (node a p (node b k c)) g d) 
    rank/lemma = 
      let open Nat.≤-Reasoning in
      begin
        sum-of-ranks (node (node a p b) k (node c g d))
      ≡⟨⟩
        (sum-of-ranks a + rank (node a p b) + sum-of-ranks b) + 
        rank (node (node a p b) k (node c g d)) + 
        (sum-of-ranks c + rank (node c g d) + sum-of-ranks d)
      ≡⟨ rank-arithmetic1 (sum-of-ranks a) (rank (node a p b)) (sum-of-ranks b) 
          (rank (node (node a p b) k (node c g d))) (sum-of-ranks c) (rank (node c g d)) (sum-of-ranks d) ⟩ 
        (sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) +
        (rank (node a p b)) +
        (rank (node (node a p b) k (node c g d))) +
        (rank (node c g d))
      ≤⟨ +-mono-≤ (+-mono-≤ (+-monoʳ-≤ (sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) 
          rank-y'≤rank-y) rank-x'≤rank-z) rank-z'≤rank-z ⟩
        (sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) +
        (rank (node a p (node b k c))) +
        (rank (node (node a p (node b k c)) g d)) +
        (rank (node (node a p (node b k c)) g d))
      ≡⟨ Nat.+-identityʳ ((sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) +
          (rank (node a p (node b k c))) + (rank (node (node a p (node b k c)) g d)) +
            (rank (node (node a p (node b k c)) g d))) ⟨ 
        (sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) +
        (rank (node a p (node b k c))) +
        (rank (node (node a p (node b k c)) g d)) +
        (rank (node (node a p (node b k c)) g d)) + 0
      ≡⟨ Eq.cong (λ e → (sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) +
          (rank (node a p (node b k c))) + (rank (node (node a p (node b k c)) g d)) +
            (rank (node (node a p (node b k c)) g d)) + e) 
              (Eq.trans (Eq.sym (Nat.*-zeroˡ 2)) (Eq.cong (λ e → 2 * e) (Eq.sym (Nat.n∸n≡0 (rank (node b k c)))))) ⟩
        (sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) +
        (rank (node a p (node b k c))) +
        (rank (node (node a p (node b k c)) g d)) +
        (rank (node (node a p (node b k c)) g d)) +
        (2 * (rank (node b k c) ∸ rank (node b k c)))
      ≤⟨ rank≤ (sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) 
          (rank (node a p (node b k c))) (rank (node (node a p (node b k c)) g d)) (rank (node b k c))
            rank-x<rank-z 1≤rank-z ⟩
        (sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) +
        (1 + rank (node b k c)) + 
        (rank (node a p (node b k c))) + 
        (rank (node b k c)) + 
        ((3 * ((rank (node (node a p (node b k c)) g d)) ∸ (rank (node b k c)))) ∸ 1)
      ≤⟨ +-monoˡ-≤ ((3 * ((rank (node (node a p (node b k c)) g d)) ∸ (rank (node b k c)))) ∸ 1) 
          (+-monoˡ-≤ (rank (node b k c)) (+-monoˡ-≤ (rank (node a p (node b k c))) 
            (+-monoʳ-≤ (sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) 
              (Nat.≤-trans rank-x<rank-x' rank-x'≤rank-z)))) ⟩
        (sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) +
        (rank (node (node a p (node b k c)) g d)) + 
        (rank (node a p (node b k c))) + 
        (rank (node b k c)) + 
        ((3 * ((rank (node (node a p (node b k c)) g d)) ∸ (rank (node b k c)))) ∸ 1)
      ≡⟨ Eq.cong (λ e → (sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) +
          (rank (node (node a p (node b k c)) g d)) + (rank (node a p (node b k c))) + 
            (rank (node b k c)) + e) (Eq.cong (λ e → ((3 * (e ∸ (rank (node b k c)))) ∸ 1)) 
              rank-x'-z) ⟨
        (sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) +
        (rank (node (node a p (node b k c)) g d)) + 
        (rank (node a p (node b k c))) + 
        (rank (node b k c)) + 
        ((3 * ((rank (node (node a p b) k (node c g d))) ∸ (rank (node b k c)))) ∸ 1)
      ≡⟨ rank-arithmetic2 (sum-of-ranks a) (rank (node a p (node b k c))) (sum-of-ranks b) (rank (node b k c)) 
          (sum-of-ranks c) (rank (node (node a p (node b k c)) g d)) (sum-of-ranks d) 
            ((3 * ((rank (node (node a p b) k (node c g d))) ∸ (rank (node b k c)))) ∸ 1) ⟩
        ((3 * ((rank (node (node a p b) k (node c g d))) ∸ (rank (node b k c)))) ∸ 1) + 
        (sum-of-ranks a + rank (node a p (node b k c)) + (sum-of-ranks b + rank (node b k c) + 
        sum-of-ranks c) + rank (node (node a p (node b k c)) g d) + sum-of-ranks d)
      ≡⟨⟩
        ((3 * ((rank (node (node a p b) k (node c g d))) ∸ (rank (node b k c)))) ∸ 1) + 
        sum-of-ranks (node (node a p (node b k c)) g d) 
      ∎
      where
        rank-arithmetic1 : (a b c d e f g : val nat) → (a + b + c) + d + (e + f + g) ≡ (a + c + e + g) + b + d + f
        rank-arithmetic1 = arithmetic₂₁
        rank-arithmetic2 : (a b c d e f g h : val nat) → (a + c + e + g) + f + b + d + h ≡ h + (a + b + (c + d + e) + f + g)
        rank-arithmetic2 = arithmetic₂₂
        1≤rank-z : 1 Nat.≤ rank (node (node a p (node b k c)) g d)
        1≤rank-z = 
          let open Nat.≤-Reasoning in
          begin
            1
          ≡⟨⟩
            ⌊log₂ 2 ⌋
          ≤⟨ ⌊log₂⌋-mono-≤ (Nat.m≤m+n 2 (tree-size a + tree-size b + tree-size c + tree-size d + 1)) ⟩
            ⌊log₂ ((1 + 1) + (tree-size a + tree-size b + tree-size c + tree-size d + 1)) ⌋
          ≡⟨ Eq.cong (λ e → ⌊log₂ e ⌋) (arithmetic (tree-size a) (tree-size b) (tree-size c) (tree-size d) 1) ⟩
            ⌊log₂ ((tree-size a + 1 + (tree-size b + 1 + tree-size c)) + 1 + tree-size d) ⌋
          ≡⟨⟩
            rank (node (node a p (node b k c)) g d)
          ∎
          where
            arithmetic : (a b c d e : val nat) → (e + e) + (a + b + c + d + e) ≡ (a + e + (b + e + c)) + e + d
            arithmetic = arithmetic₂₃
        rank-z'≤rank-z : rank (node c g d) Nat.≤ rank (node (node a p (node b k c)) g d)
        rank-z'≤rank-z = 
          let open Nat.≤-Reasoning in
          begin
            rank (node c g d)
          ≡⟨⟩
            ⌊log₂ (tree-size c + 1 + tree-size d) ⌋ 
          ≤⟨ ⌊log₂⌋-mono-≤ (Nat.m≤m+n (tree-size c + 1 + tree-size d) (tree-size a + 1 + tree-size b + 1)) ⟩
            ⌊log₂ ((tree-size c + 1 + tree-size d) + (tree-size a + 1 + tree-size b + 1)) ⌋
          ≡⟨ Eq.cong (λ e → ⌊log₂ e ⌋) (arithmetic (tree-size a) 1 (tree-size b) (tree-size c) (tree-size d)) ⟩
            ⌊log₂ ((tree-size a + 1 + (tree-size b + 1 + tree-size c)) + 1 + tree-size d) ⌋
          ≡⟨⟩
            rank (node (node a p (node b k c)) g d)
          ∎
          where
            arithmetic : (a b c d e : val nat) → (d + b + e) + (a + b + c + b) ≡ (a + b + (c + b + d)) + b + e
            arithmetic = arithmetic₂₄
        rank-x<rank-z : rank (node b k c) < rank (node (node a p (node b k c)) g d)
        rank-x<rank-z = let open Nat.≤-Reasoning in
          begin
            suc (rank (node b k c))
          ≤⟨ rank-x<rank-x' ⟩
            rank (node (node a p b) k (node c g d))
          ≡⟨ rank-x'-z ⟩
            rank (node (node a p (node b k c)) g d)
          ∎
        rank-x'≤rank-z : rank (node (node a p b) k (node c g d)) Nat.≤ rank (node (node a p (node b k c)) g d)
        rank-x'≤rank-z = Nat.≤-reflexive rank-x'-z
        rank-y'≤rank-y : rank (node a p b) Nat.≤ rank (node a p (node b k c))
        rank-y'≤rank-y = let open Nat.≤-Reasoning in
          begin
            rank (node a p b)
          ≡⟨⟩
            ⌊log₂ (tree-size a + 1 + tree-size b) ⌋
          ≤⟨ ⌊log₂⌋-mono-≤ (Nat.m≤m+n (tree-size a + 1 + tree-size b) (tree-size c + 1)) ⟩
            ⌊log₂ ((tree-size a + 1 + tree-size b) + (tree-size c + 1)) ⌋
          ≡⟨ Eq.cong (λ e → ⌊log₂ e ⌋) (arithmetic (tree-size a) (tree-size b) (tree-size c) 1) ⟩
            ⌊log₂ ((tree-size a + 1 + (tree-size b + 1 + tree-size c))) ⌋
          ≡⟨⟩
            rank (node a p (node b k c))
          ∎
          where
            arithmetic : (a b c d : val nat) → (a + d + b) + (c + d) ≡ (a + d + (b + d + c))
            arithmetic = arithmetic₂₅
        rank≤ : (a b c d : val nat) → d < c → 1 Nat.≤ c → 
          a + b + c + c + (2 * (d ∸ d)) Nat.≤ a + (1 + d) + b + d + ((3 * (c ∸ d)) ∸ 1)
        rank≤ a b c d d<c 1≤c = arithmetic-manual₄ a b c d d<c 1≤c
    phi/lemma : 
        sum-of-ranks (reconstruct (node (node a p b) k (node c g d)) anc)
      Nat.≤
        ((3 * (rank (node (node a p b) k (node c g d)) ∸ rank (node b k c))) ∸ 1) + 
        sum-of-ranks (reconstruct (node (node a p (node b k c)) g d) anc)
    phi/lemma = sum-ranks+x/lemma (node (node a p b) k (node c g d)) (node (node a p (node b k c)) g d) 
      anc ((3 * (rank (node (node a p b) k (node c g d)) ∸ rank (node b k c))) ∸ 1) size/lemma rank/lemma
... | tri≈ _ rank-x≡rank-x' _ = 
  let
    rank-x  : val nat
    rank-x  = rank (node b k c)
    rank-y  : val nat
    rank-y  = rank (node a p (node b k c))
    rank-z  : val nat
    rank-z  = rank (node (node a p (node b k c)) g d)
    rank-x' : val nat
    rank-x' = rank (node (node a p b) k (node c g d))
    rank-y' : val nat
    rank-y' = rank (node a p b)
    rank-z' : val nat
    rank-z' = rank (node c g d)
  in
  let open ≤⁻-Reasoning (F (list nat)) in 
  begin
    step (F _) 1 (
      bind (F _) (splay' (node a p b) (node c g d) anc k) (λ ((l' , r') , _) → 
        φ (node l' k r')))
  ≲⟨ step-monoʳ-≤⁻ 1 (splay'/amortized (node a p b) (node c g d) anc k) ⟩
    step (F _) 1 (
      step (F _) (1 + 3 * (rank (reconstruct (node (node a p b) k (node c g d)) anc) ∸ rank-x'))
        (φ (reconstruct (node (node a p b) k (node c g d)) anc)))
  ≡⟨⟩
    step (F _) (1 + 1 + 3 * (rank (reconstruct (node (node a p b) k (node c g d)) anc) ∸ rank-x'))
      (φ (reconstruct (node (node a p b) k (node c g d)) anc)) 
  ≡⟨ Eq.cong (λ e → step (F _) e (φ (reconstruct (node (node a p b) k (node c g d)) anc))) 
      (Eq.cong (λ e → 1 + 1 + 3 * (e ∸ rank-x')) 
        (rank/recon (node (node a p b) k (node c g d)) (node (node a p (node b k c)) g d) anc size/lemma)) ⟩
    step (F _) (1 + 1 + 3 * (rank (reconstruct (node (node a p (node b k c)) g d) anc) ∸ rank-x'))
      (φ (reconstruct (node (node a p b) k (node c g d)) anc)) 
  ≡⟨ Eq.cong (λ e → step (F _) e (φ (reconstruct (node (node a p b) k (node c g d)) anc))) 
      (Eq.cong (λ e → 1 + 1 + 3 * (rank (reconstruct (node (node a p (node b k c)) g d) anc) ∸ e)) rank-x≡rank-x') ⟨
    step (F _) (1 + 1 + 3 * (rank (reconstruct (node (node a p (node b k c)) g d) anc) ∸ rank-x))
      (φ (reconstruct (node (node a p b) k (node c g d)) anc)) 
  ≡⟨⟩
    step (F _) (1 + 1 + 3 * (rank (reconstruct (node (node a p (node b k c)) g d) anc) ∸ rank-x))
      (step (F _) (sum-of-ranks (reconstruct (node (node a p b) k (node c g d)) anc)) 
        (ret (inord (reconstruct (node (node a p b) k (node c g d)) anc))))
  ≡⟨⟩
    step (F _) (1 + 1 + 3 * (rank (reconstruct (node (node a p (node b k c)) g d) anc) ∸ rank-x) + 
      sum-of-ranks (reconstruct (node (node a p b) k (node c g d)) anc))
        (ret (inord (reconstruct (node (node a p b) k (node c g d)) anc)))
  ≡⟨ Eq.cong (λ e → step (F _) e (ret (inord (reconstruct (node (node a p b) k (node c g d)) anc)))) 
      (arithmetic2 1 1 
        (3 * (rank (reconstruct (node (node a p (node b k c)) g d) anc) ∸ rank-x)) 
        (sum-of-ranks (reconstruct (node (node a p b) k (node c g d)) anc))) ⟩
    step (F _) (1 + 3 * (rank (reconstruct (node (node a p (node b k c)) g d) anc) ∸ rank-x) + 
      (sum-of-ranks (reconstruct (node (node a p b) k (node c g d)) anc) + 1))
        (ret (inord (reconstruct (node (node a p b) k (node c g d)) anc)))
  ≲⟨ step-monoˡ-≤⁻ (ret (inord (reconstruct (node (node a p b) k (node c g d)) anc))) 
      (+-monoʳ-≤ (1 + 3 * (rank (reconstruct (node (node a p (node b k c)) g d) anc) ∸ rank-x)) phi/lemma) ⟩
    step (F _) (1 + 3 * (rank (reconstruct (node (node a p (node b k c)) g d) anc) ∸ rank-x) + 
      sum-of-ranks (reconstruct (node (node a p (node b k c)) g d) anc))
        (ret (inord (reconstruct (node (node a p b) k (node c g d)) anc)))
  ≡⟨⟩
    step (F _) (1 + 3 * (rank (reconstruct (node (node a p (node b k c)) g d) anc) ∸ rank-x))
      (step (F _) (sum-of-ranks (reconstruct (node (node a p (node b k c)) g d) anc))
        (ret (inord (reconstruct (node (node a p b) k (node c g d)) anc))))
  ≡⟨ Eq.cong (λ e → step (F _) (1 + 3 * (rank (reconstruct (node (node a p (node b k c)) g d) anc) ∸ rank-x)) e) 
      (Eq.cong (λ e → step (F _) (sum-of-ranks (reconstruct (node (node a p (node b k c)) g d) anc)) e) 
        (Eq.cong ret (inord/reconstruct 
          (node (node a p (node b k c)) g d)
          (node (node a p b) k (node c g d))
          anc 
          (zig/zag/inord/arith a b c d k p g)))) ⟨
    step (F _) (1 + 3 * (rank (reconstruct (node (node a p (node b k c)) g d) anc) ∸ rank-x))
      (step (F _) (sum-of-ranks (reconstruct (node (node a p (node b k c)) g d) anc))
        (ret (inord (reconstruct (node (node a p (node b k c)) g d) anc))))
  ≡⟨⟩
    step (F _) (1 + 3 * (rank (reconstruct (node (node a p (node b k c)) g d) anc) ∸ rank-x)) 
      (φ (reconstruct (node (node a p (node b k c)) g d) anc))
  ∎
  where
    arithmetic1 : (a b c d e f g : val nat) → a + b + c + d + (e + f + g) ≡ a + b + (c + d + e) + f + g
    arithmetic1 = arithmetic₂₆
    size/lemma : tree-size (node (node a p b) k (node c g d)) ≡ tree-size (node (node a p (node b k c)) g d)
    size/lemma = arithmetic1 (tree-size a) 1 (tree-size b) 1 (tree-size c) 1 (tree-size d)
    arithmetic2 : (a b c d : val nat) → a + b + c + d ≡ (a + c) + (d + b)
    arithmetic2 = arithmetic₂₇
    rank/lemma : 
        sum-of-ranks (node (node a p b) k (node c g d)) + 1
      Nat.≤
        sum-of-ranks (node (node a p (node b k c)) g d)
    rank/lemma with Nat.<-cmp (rank (node a p b)) (rank (node (node a p b) k (node c g d)))
    ... | tri< rank-y'<rank-x' _ _ = 
      let open Nat.≤-Reasoning in
      begin
        sum-of-ranks (node (node a p b) k (node c g d)) + 1
      ≡⟨⟩
        ((sum-of-ranks a + rank (node a p b) + sum-of-ranks b) + 
          (rank (node (node a p b) k (node c g d))) + 
          (sum-of-ranks c + rank (node c g d) + sum-of-ranks d)) + 1
      ≡⟨ rank-arithmetic1 (sum-of-ranks a) (rank (node a p b)) (sum-of-ranks b) 
          (rank (node (node a p b) k (node c g d))) (sum-of-ranks c) (rank (node c g d)) (sum-of-ranks d) 1 ⟩
        (sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) +
        (rank (node a p b) + 1) +
        (rank (node (node a p b) k (node c g d))) +
        (rank (node c g d))
      ≤⟨ +-monoˡ-≤ (rank (node c g d)) (+-monoˡ-≤ (rank (node (node a p b) k (node c g d))) 
          (+-monoʳ-≤ (sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) rank-y'-y)) ⟩
        (sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) +
        (rank (node a p (node b k c))) +
        (rank (node (node a p b) k (node c g d))) +
        (rank (node c g d))
      ≡⟨ Eq.cong (λ e → (sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) + 
          (rank (node a p (node b k c))) + e + (rank (node c g d))) rank-x'-z ⟩ 
        (sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) +
        (rank (node a p (node b k c))) +
        (rank (node (node a p (node b k c)) g d)) +
        (rank (node c g d))
      ≤⟨ +-monoʳ-≤ ((sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) + 
          (rank (node a p (node b k c))) + (rank (node (node a p (node b k c)) g d))) rank-z'-x ⟩ -- rank-z' ≤ rank-x
        (sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) +
        (rank (node a p (node b k c))) +
        (rank (node (node a p (node b k c)) g d)) +
        (rank (node b k c))
      ≡⟨ rank-arithmetic2 (sum-of-ranks a) (rank (node a p (node b k c))) (sum-of-ranks b) 
          (rank (node b k c)) (sum-of-ranks c) (rank (node (node a p (node b k c)) g d)) (sum-of-ranks d) ⟨
        sum-of-ranks a + rank (node a p (node b k c)) +
        (sum-of-ranks b + rank (node b k c) + sum-of-ranks c) + 
        rank (node (node a p (node b k c)) g d) + 
        sum-of-ranks d
      ≡⟨⟩
        sum-of-ranks (node (node a p (node b k c)) g d)
      ∎
      where 
        rank-arithmetic1 : (a b c d e f g h : val nat) → ((a + b + c) + d + (e + f + g)) + h ≡ (a + c + e + g) + (b + h) + d + f
        rank-arithmetic1 = arithmetic₂₈
        rank-arithmetic2 : (a b c d e f g : val nat) → a + b + (c + d + e) + f + g ≡ (a + c + e + g) + b + f + d
        rank-arithmetic2 = arithmetic₂₉
        rank-x'-z : rank (node (node a p b) k (node c g d)) ≡ rank (node (node a p (node b k c)) g d)
        rank-x'-z = 
          let open ≡-Reasoning in
          begin
            rank (node (node a p b) k (node c g d))
          ≡⟨⟩
            ⌊log₂ ((tree-size a + 1 + tree-size b) + 1 + (tree-size c + 1 + tree-size d)) ⌋
          ≡⟨ Eq.cong (λ e → ⌊log₂ e ⌋) (arithmetic (tree-size a) 1 (tree-size b) 1 (tree-size c) 1 (tree-size d)) ⟩
            ⌊log₂ ((tree-size a + 1 + (tree-size b + 1 + tree-size c)) + 1 + tree-size d) ⌋
          ≡⟨⟩
            rank (node (node a p (node b k c)) g d)
          ∎
          where
            arithmetic : (a b c d e f g : val nat) → (a + b + c) + d + (e + f + g) ≡ (a + b + (c + d + e)) + f + g
            arithmetic = arithmetic₃₀
        rank-y'-y : rank (node a p b) + 1 Nat.≤ rank (node a p (node b k c))
        rank-y'-y = 
          let open Nat.≤-Reasoning in 
          begin
            rank (node a p b) + 1
          ≡⟨ Nat.+-comm (rank (node a p b)) 1 ⟩
            suc (rank (node a p b))
          ≤⟨ rank-y'<rank-x' ⟩
            rank (node (node a p b) k (node c g d))
          ≡⟨ rank-x'-z ⟩
            rank (node (node a p (node b k c)) g d)
          ≡⟨ Nat.≤-antisym rank-z-y rank-y-z ⟩
            rank (node a p (node b k c))
          ∎
          where
            rank-z-y : rank (node (node a p (node b k c)) g d) Nat.≤ rank (node a p (node b k c))
            rank-z-y = 
              let open Nat.≤-Reasoning in
              begin
                rank (node (node a p (node b k c)) g d)
              ≡⟨ Eq.trans (Eq.sym (rank-x'-z)) (Eq.sym (rank-x≡rank-x')) ⟩
                rank (node b k c)
              ≡⟨⟩
                ⌊log₂ (tree-size b + 1 + tree-size c) ⌋
              ≤⟨ ⌊log₂⌋-mono-≤ (Nat.m≤n+m (tree-size b + 1 + tree-size c) (tree-size a + 1)) ⟩
                ⌊log₂ (tree-size a + 1 + (tree-size b + 1 + tree-size c)) ⌋
              ≡⟨⟩
                rank (node a p (node b k c))
              ∎
            rank-y-z : rank (node a p (node b k c)) Nat.≤ rank (node (node a p (node b k c)) g d)
            rank-y-z = 
              let open Nat.≤-Reasoning in
              begin
                rank (node a p (node b k c))
              ≡⟨⟩
                ⌊log₂ (tree-size a + 1 + (tree-size b + 1 + tree-size c)) ⌋
              ≤⟨ ⌊log₂⌋-mono-≤ (Nat.m≤m+n (tree-size a + 1 + (tree-size b + 1 + tree-size c)) (1 + tree-size d)) ⟩
                ⌊log₂ ((tree-size a + 1 + (tree-size b + 1 + tree-size c)) + (1 + tree-size d)) ⌋
              ≡⟨ Eq.cong (λ e → ⌊log₂ e ⌋) 
                  (+-assoc (tree-size a + 1 + (tree-size b + 1 + tree-size c)) 1 (tree-size d)) ⟨
                rank (node (node a p (node b k c)) g d)
              ∎       
        rank-z'-x : rank (node c g d) Nat.≤ rank (node b k c)
        rank-z'-x = 
          let open Nat.≤-Reasoning in
          begin
            rank (node c g d)
          ≡⟨⟩
            ⌊log₂ (tree-size c + 1 + tree-size d) ⌋
          ≤⟨ ⌊log₂⌋-mono-≤ (Nat.m≤n+m (tree-size c + 1 + tree-size d) ((tree-size a + 1 + tree-size b) + 1)) ⟩
            ⌊log₂ ((tree-size a + 1 + tree-size b) + 1 + (tree-size c + 1 + tree-size d)) ⌋
          ≡⟨⟩
            rank (node (node a p b) k (node c g d))
          ≡⟨ rank-x≡rank-x' ⟨  
            rank (node b k c)
          ∎
    ... | tri≈ _ rank-y'≡rank-x' _ = 
      let open Nat.≤-Reasoning in
      begin
        sum-of-ranks (node (node a p b) k (node c g d)) + 1
      ≡⟨⟩
        ((sum-of-ranks a + rank (node a p b) + sum-of-ranks b) + 
          (rank (node (node a p b) k (node c g d))) + 
          (sum-of-ranks c + rank (node c g d) + sum-of-ranks d)) + 1
      ≡⟨ rank-arithmetic1 (sum-of-ranks a) (rank (node a p b)) (sum-of-ranks b) (rank (node (node a p b) k (node c g d))) 
          (sum-of-ranks c) (rank (node c g d)) (sum-of-ranks d) 1 ⟩
        (sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) +
        (rank (node a p b)) +
        (rank (node (node a p b) k (node c g d))) +
        (rank (node c g d) + 1)
      ≡⟨ Eq.cong (λ e → (sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) + e +
          (rank (node (node a p b) k (node c g d))) + (rank (node c g d) + 1)) rank-y'-y ⟩
        (sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) +
        (rank (node a p (node b k c))) +
        (rank (node (node a p b) k (node c g d))) +
        (rank (node c g d) + 1)
      ≡⟨ Eq.cong (λ e → (sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) + 
          (rank (node a p (node b k c))) + e + (rank (node c g d) + 1)) rank-x'-z ⟩ 
        (sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) +
        (rank (node a p (node b k c))) +
        (rank (node (node a p (node b k c)) g d)) +
        (rank (node c g d) + 1)
      ≤⟨ +-monoʳ-≤ ((sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) + 
          (rank (node a p (node b k c))) + (rank (node (node a p (node b k c)) g d))) rank-z'-x ⟩
        (sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) +
        (rank (node a p (node b k c))) +
        (rank (node (node a p (node b k c)) g d)) +
        (rank (node b k c))
      ≡⟨ rank-arithmetic2 (sum-of-ranks a) (rank (node a p (node b k c))) (sum-of-ranks b) 
          (rank (node b k c)) (sum-of-ranks c) (rank (node (node a p (node b k c)) g d)) (sum-of-ranks d) ⟩
        sum-of-ranks a + rank (node a p (node b k c)) +
        (sum-of-ranks b + rank (node b k c) + sum-of-ranks c) + 
        rank (node (node a p (node b k c)) g d) + 
        sum-of-ranks d
      ≡⟨⟩
        sum-of-ranks (node (node a p (node b k c)) g d)
      ∎
      where
        rank-arithmetic1 : (a b c d e f g h : val nat) → ((a + b + c) + d + (e + f + g) + h) ≡ (a + c + e + g) + b + d + (f + h)
        rank-arithmetic1 = arithmetic₃₁
        rank-arithmetic2 : (a b c d e f g : val nat) → (a + c + e + g) + b + f + d ≡ a + b + (c + d + e) + f + g
        rank-arithmetic2 = arithmetic₃₂
        rank-x'-z : rank (node (node a p b) k (node c g d)) ≡ rank (node (node a p (node b k c)) g d)
        rank-x'-z = 
          let open ≡-Reasoning in
          begin
            rank (node (node a p b) k (node c g d))
          ≡⟨⟩
            ⌊log₂ ((tree-size a + 1 + tree-size b) + 1 + (tree-size c + 1 + tree-size d)) ⌋
          ≡⟨ Eq.cong (λ e → ⌊log₂ e ⌋) (arithmetic (tree-size a) 1 (tree-size b) 1 (tree-size c) 1 (tree-size d)) ⟩
            ⌊log₂ ((tree-size a + 1 + (tree-size b + 1 + tree-size c)) + 1 + tree-size d) ⌋
          ≡⟨⟩
            rank (node (node a p (node b k c)) g d)
          ∎
          where
            arithmetic : (a b c d e f g : val nat) → (a + b + c) + d + (e + f + g) ≡ (a + b + (c + d + e)) + f + g
            arithmetic = arithmetic₃₃
        rank-y'-y : rank (node a p b) ≡ rank (node a p (node b k c))
        rank-y'-y = 
          let open ≡-Reasoning in 
          begin
            rank (node a p b)
          ≡⟨ rank-y'≡rank-x' ⟩
            rank (node (node a p b) k (node c g d))
          ≡⟨ rank-x'-z ⟩
            rank (node (node a p (node b k c)) g d)
          ≡⟨ Nat.≤-antisym rank-z-y rank-y-z ⟩
            rank (node a p (node b k c))
          ∎
          where
            rank-z-y : rank (node (node a p (node b k c)) g d) Nat.≤ rank (node a p (node b k c))
            rank-z-y = 
              let open Nat.≤-Reasoning in
              begin
                rank (node (node a p (node b k c)) g d)
              ≡⟨ Eq.trans (Eq.sym (rank-x'-z)) (Eq.sym (rank-x≡rank-x')) ⟩
                rank (node b k c)
              ≡⟨⟩
                ⌊log₂ (tree-size b + 1 + tree-size c) ⌋
              ≤⟨ ⌊log₂⌋-mono-≤ (Nat.m≤n+m (tree-size b + 1 + tree-size c) (tree-size a + 1)) ⟩
                ⌊log₂ (tree-size a + 1 + (tree-size b + 1 + tree-size c)) ⌋
              ≡⟨⟩
                rank (node a p (node b k c))
              ∎
            rank-y-z : rank (node a p (node b k c)) Nat.≤ rank (node (node a p (node b k c)) g d)
            rank-y-z = 
              let open Nat.≤-Reasoning in
              begin
                rank (node a p (node b k c))
              ≡⟨⟩
                ⌊log₂ (tree-size a + 1 + (tree-size b + 1 + tree-size c)) ⌋
              ≤⟨ ⌊log₂⌋-mono-≤ (Nat.m≤m+n (tree-size a + 1 + (tree-size b + 1 + tree-size c)) (1 + tree-size d)) ⟩
                ⌊log₂ ((tree-size a + 1 + (tree-size b + 1 + tree-size c)) + (1 + tree-size d)) ⌋
              ≡⟨ Eq.cong (λ e → ⌊log₂ e ⌋) 
                  (+-assoc (tree-size a + 1 + (tree-size b + 1 + tree-size c)) 1 (tree-size d)) ⟨
                rank (node (node a p (node b k c)) g d)
              ∎         
        rank-z'-x : rank (node c g d) + 1 Nat.≤ rank (node b k c)
        rank-z'-x = 
          let open Nat.≤-Reasoning in
          begin
            rank (node c g d) + 1
          ≡⟨ Nat.+-comm (rank (node c g d)) 1 ⟩
            suc (rank (node c g d))
          ≤⟨ Nat.≤∧≢⇒< rank-z'≤rank-x' rank-z'≢rank-x' ⟩
            rank (node (node a p b) k (node c g d))
          ≡⟨ rank-x≡rank-x' ⟨
            rank (node b k c)
          ∎ 
          where
            rank-z'≤rank-x' : rank (node c g d) Nat.≤ rank (node (node a p b) k (node c g d))
            rank-z'≤rank-x' = 
              let open Nat.≤-Reasoning in
              begin
                rank (node c g d)
              ≡⟨⟩
                ⌊log₂ (tree-size c + 1 + tree-size d) ⌋
              ≤⟨ ⌊log₂⌋-mono-≤ (Nat.m≤n+m (tree-size c + 1 + tree-size d) ((tree-size a + 1 + tree-size b) + 1)) ⟩
                ⌊log₂ ((tree-size a + 1 + tree-size b) + 1 + (tree-size c + 1 + tree-size d)) ⌋
              ≡⟨⟩
                rank (node (node a p b) k (node c g d))
              ∎
            rank-z'≢rank-x' : rank (node c g d) ≢ rank (node (node a p b) k (node c g d))
            rank-z'≢rank-x' rank-z'≡rank-x' = Nat.<⇒≢ rank-z<rank-x' rank-z'≡rank-x'
              where
                rank-z<rank-x' : rank (node c g d) < rank (node (node a p b) k (node c g d))
                rank-z<rank-x' = 
                  let open Nat.≤-Reasoning in
                  begin
                    suc (rank (node c g d))
                  ≡⟨ Nat.+-comm 1 (rank (node c g d)) ⟩
                    rank (node c g d) + 1
                  ≡⟨ Eq.cong (λ e → e + 1) (Eq.trans rank-z'≡rank-x' (Eq.sym (rank-y'≡rank-x'))) ⟩
                    rank (node a p b) + 1
                  ≤⟨ rank-rule (node a p b) {{node-size-nonzero {a} {p} {b}}} 
                      k (node c g d) {{node-size-nonzero {c} {g} {d}}}
                        (Eq.trans rank-y'≡rank-x' (Eq.sym (rank-z'≡rank-x'))) ⟩
                    rank (node (node a p b) k (node c g d))
                  ∎
    ... | tri> _ _ rank-y'>rank-x' = ⊥-elim (Nat.≤⇒≯ rank-y'≤rank-x' rank-y'>rank-x')
      where
        rank-y'≤rank-x' : rank (node a p b) Nat.≤ rank (node (node a p b) k (node c g d))
        rank-y'≤rank-x' = 
          let open Nat.≤-Reasoning in
          begin
            rank (node a p b)
          ≡⟨⟩
            ⌊log₂ (tree-size a + 1 + tree-size b) ⌋
          ≤⟨ ⌊log₂⌋-mono-≤ (Nat.m≤m+n (tree-size a + 1 + tree-size b) (1 + tree-size c + 1 + tree-size d)) ⟩
            ⌊log₂ ((tree-size a + 1 + tree-size b) + (1 + tree-size c + 1 + tree-size d)) ⌋
          ≡⟨ Eq.cong (λ e → ⌊log₂ e ⌋) (arithmetic (tree-size a) 1 (tree-size b) 1 (tree-size c) 1 (tree-size d)) ⟩
            ⌊log₂ ((tree-size a + 1 + tree-size b) + 1 + (tree-size c + 1 + tree-size d)) ⌋
          ≡⟨⟩
            rank (node (node a p b) k (node c g d))
          ∎
          where
            arithmetic : (a b c d e f g : val nat) → (a + b + c) + (d + e + f + g) ≡ (a + b + c) + d + (e + f + g)
            arithmetic = arithmetic₃₄
    phi/lemma : 
        sum-of-ranks (reconstruct (node (node a p b) k (node c g d)) anc) + 1 
      Nat.≤
        sum-of-ranks (reconstruct (node (node a p (node b k c)) g d) anc)
    phi/lemma = sum-ranks+1/lemma 
      (node (node a p b) k (node c g d)) (node (node a p (node b k c)) g d) anc size/lemma rank/lemma
... | tri> _ _ rank-x>rank-x' = ⊥-elim (Nat.≤⇒≯ rank-x≤rank-x' rank-x>rank-x')
  where
    rank-x≤rank-x' : rank (node b k c) Nat.≤ rank (node (node a p b) k (node c g d))
    rank-x≤rank-x' = 
      let open Nat.≤-Reasoning in 
      begin
        rank (node b k c)
      ≡⟨⟩
        ⌊log₂ (tree-size b + 1 + tree-size c) ⌋
      ≤⟨ ⌊log₂⌋-mono-≤ (Nat.m≤m+n (tree-size b + 1 + tree-size c) (1 + tree-size a + 1 + tree-size d)) ⟩
        ⌊log₂ ((tree-size b + 1 + tree-size c) + (1 + tree-size a + 1 + tree-size d)) ⌋
      ≡⟨ Eq.cong (λ e → ⌊log₂ e ⌋) (arithmetic (tree-size a) 1 (tree-size b) 1 (tree-size c) 1 (tree-size d)) ⟩
        ⌊log₂ ((tree-size a + 1 + tree-size b) + 1 + (tree-size c + 1 + tree-size d)) ⌋
      ≡⟨⟩
        rank (node (node a p b) k (node c g d))
      ∎
      where
        arithmetic : (a b c d e f g : val nat) → (c + d + e) + (b + a + f + g) ≡ (a + b + c) + d + (e + f + g)
        arithmetic = arithmetic₃₅

-- zag-zag
splay'/amortized c d (Right b p ∷ Right a g ∷ anc) k with Nat.<-cmp (rank (node c k d)) (rank (node (node (node a g b) p c) k d))
... | tri< rank-x<rank-x' _ _ = 
  let
    rank-x  : val nat
    rank-x  = rank (node c k d)
    rank-y  : val nat
    rank-y  = rank (node b p (node c k d))
    rank-z  : val nat
    rank-z  = rank (node a g (node b p (node c k d)))
    rank-x' : val nat
    rank-x' = rank (node (node (node a g b) p c) k d)
    rank-y' : val nat
    rank-y' = rank (node (node a g b) p c)
    rank-z' : val nat
    rank-z' = rank (node a g b)
  in
  let open ≤⁻-Reasoning (F (list nat)) in
  begin
    step (F _) 1 (
      bind (F _) (splay' (node (node a g b) p c) d anc k) (λ ((l' , r') , _) → 
        φ (node l' k r')))
  ≲⟨ step-monoʳ-≤⁻ 1 (splay'/amortized (node (node a g b) p c) d anc k) ⟩
    step (F _) 1 (
      step (F _) (1 + 3 * (rank (reconstruct (node (node (node a g b) p c) k d) anc) ∸ rank-x'))
        (φ (reconstruct (node (node (node a g b) p c) k d) anc)))
  ≡⟨⟩ 
    step (F _) (1 + 1 + 3 * (rank (reconstruct (node (node (node a g b) p c) k d) anc) ∸ rank-x'))
      (φ (reconstruct (node (node (node a g b) p c) k d) anc))
  ≡⟨ Eq.cong (λ e → step (F _) e (φ (reconstruct (node (node (node a g b) p c) k d) anc))) 
      (Eq.cong (λ e → 1 + 1 + 3 * (e ∸ rank-x')) 
        (rank/recon (node (node (node a g b) p c) k d) (node a g (node b p (node c k d))) anc size/lemma)) ⟩
    step (F _) (1 + 1 + 3 * (rank (reconstruct (node a g (node b p (node c k d))) anc) ∸ rank-x'))
      (φ (reconstruct (node (node (node a g b) p c) k d) anc))
  ≡⟨⟩ 
    step (F _) (1 + 1 + 3 * (rank (reconstruct (node a g (node b p (node c k d))) anc) ∸ rank-x'))
      (step (F _) (sum-of-ranks (reconstruct (node (node (node a g b) p c) k d) anc)) 
        (ret (inord (reconstruct (node (node (node a g b) p c) k d) anc))))
  ≡⟨⟩
    step (F _) (1 + 1 + 3 * (rank (reconstruct (node a g (node b p (node c k d))) anc) ∸ rank-x') + 
      sum-of-ranks (reconstruct (node (node (node a g b) p c) k d) anc))
        (ret (inord (reconstruct (node (node (node a g b) p c) k d) anc)))
  ≲⟨ step-monoˡ-≤⁻ (ret (inord (reconstruct (node (node (node a g b) p c) k d) anc))) 
      (+-monoʳ-≤ (1 + 1 + 3 * (rank (reconstruct (node a g (node b p (node c k d))) anc) ∸ rank-x')) 
        phi/lemma) ⟩ 
    step (F _) (1 + 1 + 3 * (rank (reconstruct (node a g (node b p (node c k d))) anc) ∸ rank-x') +
      (((3 * (rank-x' ∸ rank-x)) ∸ 1) + sum-of-ranks (reconstruct (node a g (node b p (node c k d))) anc)))
        (ret (inord (reconstruct (node (node (node a g b) p c) k d) anc)))
  ≡⟨ Eq.cong (λ e → step (F _) e (ret (inord (reconstruct (node (node (node a g b) p c) k d) anc)))) 
      (arithmetic2 1 (3 * (rank (reconstruct (node a g (node b p (node c k d))) anc) ∸ rank-x')) 
        ((3 * (rank-x' ∸ rank-x))) (sum-of-ranks (reconstruct (node a g (node b p (node c k d))) anc)) 
          size-arith1) ⟩
    step (F _) ((1 ∸ 1) + 1 + ((3 * (rank (reconstruct (node a g (node b p (node c k d))) anc) ∸ rank-x')) +
      (3 * (rank-x' ∸ rank-x))) + sum-of-ranks (reconstruct (node a g (node b p (node c k d))) anc))
        (ret (inord (reconstruct (node (node (node a g b) p c) k d) anc)))
  ≡⟨ Eq.cong (λ e → step (F _) (e + 1 + ((3 * (rank (reconstruct (node a g (node b p (node c k d))) anc) ∸ rank-x')) +
      (3 * (rank-x' ∸ rank-x))) + sum-of-ranks (reconstruct (node a g (node b p (node c k d))) anc))
        (ret (inord (reconstruct (node (node (node a g b) p c) k d) anc)))) (Nat.n∸n≡0 1) ⟩
    step (F _) (1 + ((3 * (rank (reconstruct (node a g (node b p (node c k d))) anc) ∸ rank-x')) +
      (3 * (rank-x' ∸ rank-x))) + sum-of-ranks (reconstruct (node a g (node b p (node c k d))) anc))
        (ret (inord (reconstruct (node (node (node a g b) p c) k d) anc)))
  ≡⟨ Eq.cong (λ e → step (F _) (1 + e + sum-of-ranks (reconstruct (node a g (node b p (node c k d))) anc))
      (ret (inord (reconstruct (node (node (node a g b) p c) k d) anc)))) 
        (arithmetic3 (rank (reconstruct (node a g (node b p (node c k d))) anc)) rank-x' rank-x
          (size-arith2 (node (node (node a g b) p c) k d) (node a g (node b p (node c k d))) anc size/lemma) 
            (Nat.<⇒≤ rank-x<rank-x')) ⟩
    step (F _) (1 + (3 * (rank (reconstruct (node a g (node b p (node c k d))) anc) ∸ rank-x)) +  
      sum-of-ranks (reconstruct (node a g (node b p (node c k d))) anc))
        (ret (inord (reconstruct (node (node (node a g b) p c) k d) anc)))
  ≡⟨⟩
    step (F _) (1 + 3 * (rank (reconstruct (node a g (node b p (node c k d))) anc) ∸ rank-x))
      (step (F _) (sum-of-ranks (reconstruct (node a g (node b p (node c k d))) anc))
        (ret (inord (reconstruct (node (node (node a g b) p c) k d) anc))))
  ≡⟨ Eq.cong (λ e → step (F _) (1 + 3 * (rank (reconstruct (node a g (node b p (node c k d))) anc) ∸ rank-x)) e) 
      (Eq.cong (λ e → step (F _) (sum-of-ranks (reconstruct (node a g (node b p (node c k d))) anc)) e) 
        (Eq.cong ret (inord/reconstruct 
          (node a g (node b p (node c k d)))
          (node (node (node a g b) p c) k d)
          anc 
          (zag/zag/inord/arith a b c d k p g)))) ⟨
    step (F _) (1 + 3 * (rank (reconstruct (node a g (node b p (node c k d))) anc) ∸ rank-x))
      (step (F _) (sum-of-ranks (reconstruct (node a g (node b p (node c k d))) anc))
        (ret (inord (reconstruct (node a g (node b p (node c k d))) anc))))
  ≡⟨⟩
    step (F _) (1 + 3 * (rank (reconstruct (node a g (node b p (node c k d))) anc) ∸ rank-x)) 
      (φ (reconstruct (node a g (node b p (node c k d))) anc))
  ∎
  where
    arithmetic1 : (a b c d e : val nat) → (((a + e + b) + e + c) + e + d) ≡ a + e + (b + e + (c + e + d))
    arithmetic1 = arithmetic₄₉
    arithmetic2 : (a b c d : val nat) → a Nat.≤ c → a + a + b + ((c ∸ a) + d) ≡ (a ∸ a) + a + (b + c) + d
    arithmetic2 a b c d a≤c = arithmetic-manual₂ a b c d a≤c
    arithmetic3 : (a b c : val nat) → b Nat.≤ a → c Nat.≤ b → (3 * (a ∸ b)) + (3 * (b ∸ c)) ≡ (3 * (a ∸ c))
    arithmetic3 a b c b≤a c≤b = arithmetic-manual₃ a b c b≤a c≤b
    size-arith1 : 1 Nat.≤ 3 * (rank (node (node (node a g b) p c) k d) ∸ rank (node c k d))
    size-arith1 = 
      let open Nat.≤-Reasoning in
      begin
        1
      ≤⟨ s≤s z≤n ⟩
        3
      ≤⟨ Nat.m≤m*n 3 (rank (node (node (node a g b) p c) k d) ∸ rank (node c k d)) 
          {{ >-nonZero (Nat.m<n⇒0<n∸m rank-x<rank-x') }}  ⟩
        3 * (rank (node (node (node a g b) p c) k d) ∸ rank (node c k d))
      ∎
    size-arith2 : (t₁ t₂ : Tree) (anc : List Context) → tree-size t₁ ≡ tree-size t₂ → 
      rank t₁ Nat.≤ rank (reconstruct t₂ anc)
    size-arith2 t₁ t₂ [] t₁≡t₂ = Nat.≤-reflexive (Eq.cong (λ e → ⌊log₂ e ⌋) t₁≡t₂)
    size-arith2 t₁ t₂ (Left k t ∷ anc) t₁≡t₂ = 
      let open Nat.≤-Reasoning in
      begin
        rank t₁
      ≡⟨⟩
        ⌊log₂ (tree-size t₁) ⌋
      ≤⟨ ⌊log₂⌋-mono-≤ (Nat.m≤m+n (tree-size t₁) (1 + tree-size t)) ⟩
        ⌊log₂ ((tree-size t₁) + (1 + tree-size t)) ⌋
      ≡⟨ Eq.cong (λ e → ⌊log₂ (e + (1 + tree-size t)) ⌋) t₁≡t₂ ⟩
        ⌊log₂ ((tree-size t₂) + (1 + tree-size t)) ⌋
      ≡⟨ Eq.cong (λ e → ⌊log₂ e ⌋) (Nat.+-assoc (tree-size t₂) 1 (tree-size t)) ⟨
        ⌊log₂ (tree-size t₂ + 1 + tree-size t) ⌋
      ≡⟨⟩
        rank (node t₂ k t)
      ≤⟨ size-arith2 (node t₂ k t) (node t₂ k t) anc refl ⟩
        rank (reconstruct (node t₂ k t) anc)
      ∎
    size-arith2 t₁ t₂ (Right t k ∷ anc) t₁≡t₂ = 
      let open Nat.≤-Reasoning in
      begin
        rank t₁
      ≡⟨⟩
        ⌊log₂ (tree-size t₁) ⌋
      ≤⟨ ⌊log₂⌋-mono-≤ (Nat.m≤n+m (tree-size t₁) (tree-size t + 1)) ⟩
        ⌊log₂ (tree-size t + 1 + tree-size t₁) ⌋
      ≡⟨ Eq.cong (λ e → ⌊log₂ ((tree-size t + 1) + e) ⌋) t₁≡t₂ ⟩
        ⌊log₂ (tree-size t + 1 + tree-size t₂) ⌋
      ≡⟨⟩
        rank (node t k t₂)
      ≤⟨ size-arith2 (node t k t₂) (node t k t₂) anc refl ⟩
        rank (reconstruct (node t k t₂) anc)
      ∎
    size/lemma : tree-size (node (node (node a g b) p c) k d) ≡ tree-size (node a g (node b p (node c k d)))
    size/lemma = arithmetic1 (tree-size a) (tree-size b) (tree-size c) (tree-size d) 1
    rank/lemma : 
        sum-of-ranks (node (node (node a g b) p c) k d)
      Nat.≤
        ((3 * (rank (node (node (node a g b) p c) k d) ∸ rank (node c k d))) ∸ 1) + 
        sum-of-ranks (node a g (node b p (node c k d)))
    rank/lemma = 
      let open Nat.≤-Reasoning in
      begin
        sum-of-ranks (node (node (node a g b) p c) k d)
      ≡⟨⟩
        (((sum-of-ranks a + rank (node a g b) + sum-of-ranks b) + rank (node (node a g b) p c) + sum-of-ranks c) + 
          rank (node (node (node a g b) p c) k d) + sum-of-ranks d)
      ≡⟨ rank-arithmetic1 (sum-of-ranks a) (sum-of-ranks b) (sum-of-ranks c) (sum-of-ranks d) 
          (rank (node a g b)) (rank (node (node a g b) p c)) (rank (node (node (node a g b) p c) k d)) ⟩
        (sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) +
        (rank (node a g b)) +
        (rank (node (node a g b) p c)) + 
        (rank (node (node (node a g b) p c) k d))
      ≤⟨ +-mono-≤ (+-mono-≤ (+-monoʳ-≤ (sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) 
            rank-z'≤rank-x') rank-y'≤rank-x') Nat.≤-refl ⟩
        (sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) +
        (rank (node (node (node a g b) p c) k d)) +
        (rank (node (node (node a g b) p c) k d)) +
        (rank (node (node (node a g b) p c) k d)) 
      ≡⟨ Nat.+-identityʳ ((sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) +
          (rank (node (node (node a g b) p c) k d)) + (rank (node (node (node a g b) p c) k d)) +
            (rank (node (node (node a g b) p c) k d))) ⟨
        (sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) +
        (rank (node (node (node a g b) p c) k d)) +
        (rank (node (node (node a g b) p c) k d)) +
        (rank (node (node (node a g b) p c) k d)) + 0
      ≡⟨ Eq.cong (λ e → (sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) + 
          (rank (node (node (node a g b) p c) k d)) + (rank (node (node (node a g b) p c) k d)) +
            (rank (node (node (node a g b) p c) k d)) + e) (Eq.trans (Eq.sym (Nat.*-zeroˡ 3)) 
              (Eq.cong (λ e → 3 * e) (Eq.sym (Nat.n∸n≡0 (rank (node c k d)))))) ⟩
        (sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) +
        (rank (node (node (node a g b) p c) k d)) +
        (rank (node (node (node a g b) p c) k d)) +
        (rank (node (node (node a g b) p c) k d)) + 
        (3 * (rank (node c k d) ∸ rank (node c k d)))
      ≡⟨ rank≡ (sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) 
          (rank (node (node (node a g b) p c) k d)) (rank (node c k d)) 
            rank-x<rank-x' 1≤rank-z ⟩
        (sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) +
        (1 + rank (node c k d)) +
        (rank (node c k d)) +
        (rank (node c k d)) + 
        ((3 * (rank (node (node (node a g b) p c) k d) ∸ rank (node c k d))) ∸ 1)
      ≤⟨ +-monoˡ-≤ ((3 * (rank (node (node (node a g b) p c) k d) ∸ rank (node c k d))) ∸ 1) (+-monoˡ-≤ (rank (node c k d)) 
          (+-mono-≤ (+-monoʳ-≤ (sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) 
            (Nat.≤-trans rank-x<rank-x' (Nat.≤-reflexive rank-x'≡rank-z))) rank-x≤rank-y)) ⟩
        (sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) +
        (rank (node a g (node b p (node c k d)))) +
        (rank (node b p (node c k d))) +
        (rank (node c k d)) + 
        ((3 * (rank (node (node (node a g b) p c) k d) ∸ rank (node c k d))) ∸ 1)
      ≡⟨ rank-arithmetic2 (sum-of-ranks a) (sum-of-ranks b) (sum-of-ranks c) (sum-of-ranks d) 
          (rank (node a g (node b p (node c k d)))) (rank (node b p (node c k d))) (rank (node c k d)) 
            ((3 * (rank (node (node (node a g b) p c) k d) ∸ rank (node c k d))) ∸ 1) ⟩
        ((3 * (rank (node (node (node a g b) p c) k d) ∸ rank (node c k d))) ∸ 1) +
        (sum-of-ranks a + rank (node a g (node b p (node c k d))) + (sum-of-ranks b + 
        rank (node b p (node c k d)) + (sum-of-ranks c + rank (node c k d) + sum-of-ranks d)))
      ≡⟨⟩
        ((3 * (rank (node (node (node a g b) p c) k d) ∸ rank (node c k d))) ∸ 1) +
        sum-of-ranks (node a g (node b p (node c k d)))
      ∎ 
      where
        rank-arithmetic1 : (a b c d e f g : val nat) → (((a + e + b) + f + c) + g + d) ≡ (a + b + c + d) + e + f + g
        rank-arithmetic1 = arithmetic₅₀
        rank-arithmetic2 : (a b c d e f g h : val nat) → (a + b + c + d) + e + f + g + h ≡ h + (a + e + (b + f + (c + g + d)))
        rank-arithmetic2 = arithmetic₅₁
        rank-y'≤rank-x' : rank (node (node a g b) p c) Nat.≤ rank (node (node (node a g b) p c) k d)
        rank-y'≤rank-x' = 
          let open Nat.≤-Reasoning in
          begin
            rank (node (node a g b) p c)
          ≡⟨⟩
            ⌊log₂ ((tree-size a + 1 + tree-size b) + 1 + tree-size c) ⌋
          ≤⟨ ⌊log₂⌋-mono-≤ (Nat.m≤m+n ((tree-size a + 1 + tree-size b) + 1 + tree-size c) (1 + tree-size d)) ⟩
            ⌊log₂ (((tree-size a + 1 + tree-size b) + 1 + tree-size c) + (1 + tree-size d)) ⌋
          ≡⟨ Eq.cong (λ e → ⌊log₂ e ⌋) (Nat.+-assoc ((tree-size a + 1 + tree-size b) + 1 + tree-size c) 1 (tree-size d)) ⟨ 
            ⌊log₂ (((tree-size a + 1 + tree-size b) + 1 + tree-size c) + 1 + tree-size d) ⌋
          ≡⟨⟩
            rank (node (node (node a g b) p c) k d)
          ∎
        rank-z'≤rank-x' : rank (node a g b) Nat.≤ rank (node (node (node a g b) p c) k d)
        rank-z'≤rank-x' = 
          let open Nat.≤-Reasoning in
          begin
            rank (node a g b)
          ≡⟨⟩
            ⌊log₂ (tree-size a + 1 + tree-size b) ⌋
          ≤⟨ ⌊log₂⌋-mono-≤ (Nat.m≤m+n (tree-size a + 1 + tree-size b) (1 + tree-size c)) ⟩
            ⌊log₂ ((tree-size a + 1 + tree-size b) + (1 + tree-size c)) ⌋
          ≡⟨ Eq.cong (λ e → ⌊log₂ e ⌋) (Nat.+-assoc (tree-size a + 1 + tree-size b) 1 (tree-size c)) ⟨ 
            ⌊log₂ ((tree-size a + 1 + tree-size b) + 1 + tree-size c) ⌋
          ≤⟨ rank-y'≤rank-x' ⟩
            rank (node (node (node a g b) p c) k d)
          ∎
        rank-x'≡rank-z : rank (node (node (node a g b) p c) k d) ≡ rank (node a g (node b p (node c k d)))
        rank-x'≡rank-z = Eq.cong (λ e → ⌊log₂ e ⌋) size/lemma 
        rank-x≤rank-y : rank (node c k d) Nat.≤ rank (node b p (node c k d))
        rank-x≤rank-y = ⌊log₂⌋-mono-≤ (Nat.m≤n+m (tree-size c + 1 + tree-size d) (tree-size b + 1))
        1≤rank-z : 1 Nat.≤ rank (node (node (node a g b) p c) k d)
        1≤rank-z = 
          let open Nat.≤-Reasoning in
          begin
            1
          ≡⟨⟩
            ⌊log₂ 2 ⌋
          ≤⟨ ⌊log₂⌋-mono-≤ (Nat.m≤m+n 2 (tree-size a + tree-size b + tree-size c + tree-size d + 1)) ⟩
            ⌊log₂ ((1 + 1) + (tree-size a + tree-size b + tree-size c + tree-size d + 1)) ⌋
          ≡⟨ Eq.cong (λ e → ⌊log₂ e ⌋) (arithmetic (tree-size a) (tree-size b) (tree-size c) (tree-size d) 1) ⟩
            ⌊log₂ (((tree-size a + 1 + tree-size b) + 1 + tree-size c) + 1 + tree-size d) ⌋
          ≡⟨⟩
            rank (node (node (node a g b) p c) k d)
          ∎
          where
            arithmetic : (a b c d e : val nat) → (e + e) + (a + b + c + d + e) ≡ (((a + e + b) + e + c) + e + d)
            arithmetic = arithmetic₅₂
        rank≡ : (a b c : val nat) → c < b → 1 Nat.≤ b → 
          a + b + b + b + (3 * (c ∸ c)) ≡ a + (1 + c) + c + c + ((3 * (b ∸ c)) ∸ 1)
        rank≡ a b c c<b 1≤b = arithmetic-manual₅ a b c c<b 1≤b
    phi/lemma : 
        sum-of-ranks (reconstruct (node (node (node a g b) p c) k d) anc)
      Nat.≤
        ((3 * (rank (node (node (node a g b) p c) k d) ∸ rank (node c k d))) ∸ 1) + 
        sum-of-ranks (reconstruct (node a g (node b p (node c k d))) anc)
    phi/lemma = sum-ranks+x/lemma (node (node (node a g b) p c) k d) (node a g (node b p (node c k d))) anc 
      ((3 * (rank (node (node (node a g b) p c) k d) ∸ rank (node c k d))) ∸ 1) size/lemma rank/lemma 
... | tri≈ _ rank-x≡rank-x'' _ = 
  let
    rank-x   : val nat
    rank-x   = rank (node c k d)
    rank-y   : val nat
    rank-y   = rank (node b p (node c k d))
    rank-z   : val nat
    rank-z   = rank (node a g (node b p (node c k d)))
    rank-x'  : val nat
    rank-x'  = rank (node c k d)
    rank-y'  : val nat
    rank-y'  = rank (node (node a g b) p (node c k d))
    rank-z'  : val nat
    rank-z'  = rank (node a g b)
    rank-x'' : val nat
    rank-x'' = rank (node (node (node a g b) p c) k d)
    rank-y'' : val nat
    rank-y'' = rank (node (node a g b) p c)
    rank-z'' : val nat
    rank-z'' = rank (node a g b)
  in  
  let open ≤⁻-Reasoning (F (list nat)) in
  begin
    step (F _) 1 (
      bind (F _) (splay' (node (node a g b) p c) d anc k) (λ ((l' , r') , _) → 
        φ (node l' k r')))
  ≲⟨ step-monoʳ-≤⁻ 1 (splay'/amortized (node (node a g b) p c) d anc k) ⟩
    step (F _) 1 (
      step (F _) (1 + 3 * (rank (reconstruct (node (node (node a g b) p c) k d) anc) ∸ rank-x''))
        (φ (reconstruct (node (node (node a g b) p c) k d) anc)))
  ≡⟨⟩ 
    step (F _) (1 + 1 + 3 * (rank (reconstruct (node (node (node a g b) p c) k d) anc) ∸ rank-x''))
      (φ (reconstruct (node (node (node a g b) p c) k d) anc))
  ≡⟨ Eq.cong (λ e → step (F _) e (φ (reconstruct (node (node (node a g b) p c) k d) anc))) 
      (Eq.cong (λ e → 1 + 1 + 3 * (e ∸ rank-x'')) 
        (rank/recon (node (node (node a g b) p c) k d) (node a g (node b p (node c k d))) anc size/lemma)) ⟩
    step (F _) (1 + 1 + 3 * (rank (reconstruct (node a g (node b p (node c k d))) anc) ∸ rank-x''))
      (φ (reconstruct (node (node (node a g b) p c) k d) anc))
  ≡⟨ Eq.cong (λ e → step (F _) e (φ (reconstruct (node (node (node a g b) p c) k d) anc))) 
      (Eq.cong (λ e → 1 + 1 + 3 * (rank (reconstruct (node a g (node b p (node c k d))) anc) ∸ e)) rank-x≡rank-x'') ⟨
    step (F _) (1 + 1 + 3 * (rank (reconstruct (node a g (node b p (node c k d))) anc) ∸ rank-x))
      (φ (reconstruct (node (node (node a g b) p c) k d) anc)) 
  ≡⟨⟩
    step (F _) (1 + 1 + 3 * (rank (reconstruct (node a g (node b p (node c k d))) anc) ∸ rank-x))
      (step (F _) (sum-of-ranks (reconstruct (node (node (node a g b) p c) k d) anc)) 
        (ret (inord (reconstruct (node (node (node a g b) p c) k d) anc))))
  ≡⟨ Eq.cong (λ e → step (F _) e (ret (inord (reconstruct (node (node (node a g b) p c) k d) anc)))) 
      (arithmetic1 1  
        (3 * (rank (reconstruct (node a g (node b p (node c k d))) anc) ∸ rank-x)) 
          (sum-of-ranks (reconstruct (node (node (node a g b) p c) k d) anc))) ⟩
    step (F _) (1 + 3 * (rank (reconstruct (node a g (node b p (node c k d))) anc) ∸ rank-x) + 
      (sum-of-ranks (reconstruct (node (node (node a g b) p c) k d) anc) + 1))
        (ret (inord (reconstruct (node (node (node a g b) p c) k d) anc)))
  ≲⟨ step-monoˡ-≤⁻ (ret (inord (reconstruct (node (node (node a g b) p c) k d) anc))) 
      (+-monoʳ-≤ (1 + 3 * (rank (reconstruct (node a g (node b p (node c k d))) anc) ∸ rank-x)) phi/lemma) ⟩
    step (F _) (1 + 3 * (rank (reconstruct (node a g (node b p (node c k d))) anc) ∸ rank-x) + 
      sum-of-ranks (reconstruct (node a g (node b p (node c k d))) anc))
        (ret (inord (reconstruct (node (node (node a g b) p c) k d) anc)))
  ≡⟨⟩
    step (F _) (1 + 3 * (rank (reconstruct (node a g (node b p (node c k d))) anc) ∸ rank-x))
      (step (F _) (sum-of-ranks (reconstruct (node a g (node b p (node c k d))) anc))
        (ret (inord (reconstruct (node (node (node a g b) p c) k d) anc))))
  ≡⟨ Eq.cong (λ e → step (F _) (1 + 3 * (rank (reconstruct (node a g (node b p (node c k d))) anc) ∸ rank-x)) e) 
      (Eq.cong (λ e → step (F _) (sum-of-ranks (reconstruct (node a g (node b p (node c k d))) anc)) e) 
        (Eq.cong ret (inord/reconstruct 
          (node a g (node b p (node c k d)))
          (node (node (node a g b) p c) k d)
          anc 
          (zag/zag/inord/arith a b c d k p g)))) ⟨
    step (F _) (1 + 3 * (rank (reconstruct (node a g (node b p (node c k d))) anc) ∸ rank-x))
      (step (F _) (sum-of-ranks (reconstruct (node a g (node b p (node c k d))) anc))
        (ret (inord (reconstruct (node a g (node b p (node c k d))) anc))))
  ≡⟨⟩
    step (F _) (1 + 3 * (rank (reconstruct (node a g (node b p (node c k d))) anc) ∸ rank-x)) 
      (φ (reconstruct (node a g (node b p (node c k d))) anc))
  ∎
  where
    arithmetic0 : (a b c d e : val nat) → (((a + e + b) + e + c) + e + d) ≡ a + e + (b + e + (c + e + d))
    arithmetic0 = arithmetic₄₉
    arithmetic1 : (a b c : val nat) → a + a + b + c ≡ (a + b) + (c + a)
    arithmetic1 = arithmetic₅₃
    size/lemma : tree-size (node (node (node a g b) p c) k d) ≡ tree-size (node a g (node b p (node c k d)))
    size/lemma = arithmetic0 (tree-size a) (tree-size b) (tree-size c) (tree-size d) 1
    rank/lemma : 
        sum-of-ranks (node (node (node a g b) p c) k d) + 1
      Nat.≤
        sum-of-ranks (node a g (node b p (node c k d)))
    rank/lemma = let open Nat.≤-Reasoning in
      begin
        sum-of-ranks (node (node (node a g b) p c) k d) + 1
      ≡⟨⟩
        (((sum-of-ranks a + rank (node a g b) + sum-of-ranks b) + rank (node (node a g b) p c) + sum-of-ranks c) + 
        rank (node (node (node a g b) p c) k d) + sum-of-ranks d) + 1
      ≡⟨ rank-arithmetic1 (sum-of-ranks a) (sum-of-ranks b) (sum-of-ranks c) (sum-of-ranks d) (rank (node a g b)) 
          (rank (node (node a g b) p c)) (rank (node (node (node a g b) p c) k d)) 1 ⟩ 
        (sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) + 
        (rank (node (node (node a g b) p c) k d)) +
        (rank (node (node a g b) p c)) +
        (rank (node a g b) + 1)
      ≤⟨ +-mono-≤ (+-mono-≤ (+-monoʳ-≤ (sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) 
          (Nat.≤-reflexive (Eq.sym (rank-x≡rank-x'')))) rank-y''≤rank-y) rank-z''<rank-z ⟩
        (sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) +
        (rank (node c k d)) +
        (rank (node b p (node c k d))) +
        (rank (node a g (node b p (node c k d))))
      ≡⟨ rank-arithmetic2 (sum-of-ranks a) (sum-of-ranks b) (sum-of-ranks c) (sum-of-ranks d) (rank (node c k d)) (rank (node b p (node c k d))) 
          (rank (node a g (node b p (node c k d)))) ⟩
        sum-of-ranks a + rank (node a g (node b p (node c k d))) + (sum-of-ranks b + rank (node b p (node c k d)) +
        (sum-of-ranks c + rank (node c k d) + sum-of-ranks d))
      ≡⟨⟩
        sum-of-ranks (node a g (node b p (node c k d)))
      ∎
      where
        rank-arithmetic1 : (a b c d e f g h : val nat) → (((a + e + b) + f + c) + g + d) + h ≡ (a + b + c + d) + g + f + (e + h)
        rank-arithmetic1 = arithmetic₅₄
        rank-arithmetic2 : (a b c d e f g : val nat) → (a + b + c + d) + e + f + g ≡ a + g + (b + f + (c + e + d))
        rank-arithmetic2 = arithmetic₅₅
        rank-y''≤rank-y : rank (node (node a g b) p c) Nat.≤ rank (node b p (node c k d))
        rank-y''≤rank-y = let open Nat.≤-Reasoning in
          begin
            rank (node (node a g b) p c)
          ≤⟨ ⌊log₂⌋-mono-≤ (Nat.m≤m+n ((tree-size a + 1 + tree-size b) + 1 + tree-size c) (1 + tree-size d)) ⟩
            ⌊log₂ (((tree-size a + 1 + tree-size b) + 1 + tree-size c) + (1 + tree-size d)) ⌋
          ≡⟨ Eq.cong (λ e → ⌊log₂ e ⌋) (Nat.+-assoc ((tree-size a + 1 + tree-size b) + 1 + tree-size c) 1 (tree-size d)) ⟨
            rank (node (node (node a g b) p c) k d)
          ≡⟨ rank-x≡rank-x'' ⟨ 
            rank (node c k d)
          ≡⟨ Nat.≤-antisym rank-y≤rank-x rank-x≤rank-y ⟨
            rank (node b p (node c k d))
          ∎ 
          where
            rank-y≤rank-x : rank (node b p (node c k d)) Nat.≤ rank (node c k d)
            rank-y≤rank-x = 
              let open Nat.≤-Reasoning in
              begin
                rank (node b p (node c k d))
              ≤⟨ ⌊log₂⌋-mono-≤ (Nat.m≤n+m (tree-size b + 1 + (tree-size c + 1 + tree-size d)) (tree-size a + 1)) ⟩
                rank (node a g (node b p (node c k d)))
              ≡⟨ Eq.cong (λ e → ⌊log₂ e ⌋) size/lemma ⟨
                rank (node (node (node a g b) p c) k d)  
              ≡⟨ rank-x≡rank-x'' ⟨
                rank (node c k d)
              ∎
            rank-x≤rank-y : rank (node c k d) Nat.≤ rank (node b p (node c k d))
            rank-x≤rank-y = ⌊log₂⌋-mono-≤ (Nat.m≤n+m (tree-size c + 1 + tree-size d) (tree-size b + 1))
        rank-z''<rank-z : rank (node a g b) + 1 Nat.≤ rank (node a g (node b p (node c k d)))
        rank-z''<rank-z = let open Nat.≤-Reasoning in
          begin
            rank (node a g b) + 1
          ≡⟨ Nat.+-comm (rank (node a g b)) 1 ⟩ 
            suc (rank (node a g b))
          ≤⟨ Nat.≤∧≢⇒< rank-z''≤rank-y' rank-z''≢rank-y' ⟩
            rank (node (node a g b) p (node c k d))
          ≡⟨ rank-y'≡rank-z ⟩
            rank (node a g (node b p (node c k d)))
          ∎
          where
            rank-y'≡rank-z   : rank (node (node a g b) p (node c k d)) ≡ rank (node a g (node b p (node c k d)))
            rank-y'≡rank-z   = 
              let open ≡-Reasoning in 
              begin
                rank (node (node a g b) p (node c p d))
              ≡⟨⟩
                ⌊log₂ ((tree-size a + 1 + tree-size b) + 1 + (tree-size c + 1 + tree-size d)) ⌋
              ≡⟨ Eq.cong (λ e → ⌊log₂ e ⌋) (arithmetic (tree-size a) (tree-size b) (tree-size c) (tree-size d) 1) ⟩
                ⌊log₂ (tree-size a + 1 + (tree-size b + 1 + (tree-size c + 1 + tree-size d))) ⌋
              ≡⟨⟩ 
                rank (node a g (node b p (node c k d)))
              ∎ 
              where
                arithmetic : (a b c d e : val nat) → ((a + e + b) + e + (c + e + d)) ≡ (a + e + (b + e + (c + e + d)))
                arithmetic = arithmetic₅₆
            rank-z''≤rank-y' : rank (node a g b) Nat.≤ rank (node (node a g b) p (node c p d))
            rank-z''≤rank-y' = 
              let open Nat.≤-Reasoning in
              begin
                rank (node a g b)
              ≡⟨⟩
                ⌊log₂ (tree-size a + 1 + tree-size b) ⌋
              ≤⟨ ⌊log₂⌋-mono-≤ (Nat.m≤m+n (tree-size a + 1 + tree-size b) (1 + tree-size c + 1 + tree-size d)) ⟩
                ⌊log₂ ((tree-size a + 1 + tree-size b) + (1 + tree-size c + 1 + tree-size d)) ⌋
              ≡⟨ Eq.cong (λ e → ⌊log₂ e ⌋) (arithmetic (tree-size a) (tree-size b) (tree-size c) (tree-size d) 1) ⟩
                rank (node (node a g b) p (node c p d))
              ∎
              where
                arithmetic : (a b c d e : val nat) → ((a + e + b) + (e + c + e + d)) ≡ ((a + e + b) + e + (c + e + d))
                arithmetic = arithmetic₅₇
            rank-z''≢rank-y' : rank (node a g b) ≢ rank (node (node a g b) p (node c p d))
            rank-z''≢rank-y' rank-z''≡rank-y' = Nat.<⇒≢ rank-z''<rank-y' rank-z''≡rank-y'
              where
                rank-z''<rank-y' : rank (node a g b) < rank (node (node a g b) p (node c k d))
                rank-z''<rank-y' = 
                  let open Nat.≤-Reasoning in
                  begin
                    suc (rank (node a g b))
                  ≡⟨ Nat.+-comm 1 (rank (node a g b)) ⟩
                    rank (node a g b) + 1
                  ≤⟨ rank-rule (node a g b) {{node-size-nonzero {a} {g} {b}}} p (node c k d) {{node-size-nonzero {c} {k} {d}}} 
                      rank-z''≡rank-x ⟩  
                    rank (node (node a g b) p (node c k d))
                  ∎ 
                  where 
                    rank-z''≡rank-x : rank (node a g b) ≡ rank (node c k d)
                    rank-z''≡rank-x = 
                      let open ≡-Reasoning in
                      begin
                        rank (node a g b)
                      ≡⟨ rank-z''≡rank-y' ⟩
                        rank (node (node a g b) p (node c k d))
                      ≡⟨ rank-y'≡rank-z ⟩
                        rank (node a g (node b p (node c k d)))
                      ≡⟨ Eq.cong (λ e → ⌊log₂ e ⌋) size/lemma ⟨ 
                        rank (node (node (node a g b) p c) k d)
                      ≡⟨ rank-x≡rank-x'' ⟨
                        rank (node c k d)
                      ∎
    phi/lemma : 
        sum-of-ranks (reconstruct (node (node (node a g b) p c) k d) anc) + 1
      Nat.≤
        sum-of-ranks (reconstruct (node a g (node b p (node c k d))) anc)
    phi/lemma = sum-ranks+1/lemma (node (node (node a g b) p c) k d) (node a g (node b p (node c k d))) anc size/lemma rank/lemma
... | tri> _ _ rank-x>rank-x' = ⊥-elim (Nat.≤⇒≯ rank-x≤rank-x' rank-x>rank-x')
  where
    rank-x≤rank-x' : rank (node c k d) Nat.≤ rank (node (node (node a g b) p c) k d)
    rank-x≤rank-x' = 
      let open Nat.≤-Reasoning in
      begin
        rank (node c k d)
      ≤⟨ ⌊log₂⌋-mono-≤ (Nat.m≤n+m (tree-size c + 1 + tree-size d) (tree-size a + 1 + tree-size b + 1)) ⟩
        ⌊log₂ ((tree-size a + 1 + tree-size b + 1) + (tree-size c + 1 + tree-size d)) ⌋
      ≡⟨ Eq.cong (λ e → ⌊log₂ e ⌋) (arithmetic (tree-size a) (tree-size b) (tree-size c) (tree-size d) 1) ⟩ 
        rank (node (node (node a g b) p c) k d)
      ∎
      where
        arithmetic : (a b c d e : val nat) → (a + e + b + e) + (c + e + d) ≡ (((a + e + b) + e + c) + e + d)
        arithmetic = arithmetic₅₈