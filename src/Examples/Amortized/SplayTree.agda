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
open import Data.Nat.Base using (⌊_/2⌋)
open import Data.List.Properties as List 
open import Data.Fin using (Fin; fromℕ<)
open import Relation.Nullary using (Dec; yes; no)

open import Relation.Binary 
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; module ≡-Reasoning)

open import Tactic.MonoidSolver using (solve; solve-macro)

open import Data.Nat.Logarithm
open import Data.Nat.PredExp2

record BST : Set where
  field 
    T : tp⁺
    splay : cmp (Π T (λ _ → Π nat (λ _ → F (nat ×⁺ T))))


ListTree : BST
ListTree .BST.T = list nat
ListTree .BST.splay l i with i <? length l 
... | yes p = let i' = fromℕ< p in step (F _) ((3 * ⌊log₂ (length l)⌋) ⊕ 1) (ret (lookup l i' , l))
... | no _ = ret (0 , l)

data Tree : Set where
  leaf : Tree
  node : Tree → val nat → Tree → Tree

tree : tp⁺
tree = meta⁺ Tree  

tree-size : Tree → val nat
tree-size leaf = 0
tree-size (node l z r) = (tree-size l) + 1 + (tree-size r)

data Context : Set where
  Left : (t : Tree) (k : val nat) → Context
  Right : (k : val nat) (t : Tree) → Context

context : tp⁺
context = meta⁺ (Context)



-- data Splayed : Set where
--   valid : (t : Tree) → Splayed 
--   zig :   (a : Tree) (x : val nat) (b : Tree) (y : val nat) (c : Tree) → Splayed 
--   zag :   (a : Tree) (y : val nat) (b : Tree) (x : val nat) (c : Tree) → Splayed

-- splayed : tp⁺
-- splayed = meta⁺ (Splayed)
pathType : tp⁺
pathType = tree ×⁺ (list context)

path : (i : val nat) (t : Tree) (anc : List Context) → cmp (F (pathType))
path i leaf anc = ret (leaf , anc)
path i (node l x r) anc with <-cmp i (tree-size l) 
... | tri< _ _ _ = bind (F _) (path i l {!   !}) {!   !}
... | tri≈ _ _ _ = {!   !}
... | tri> _ _ _ = {!   !}

-- with <-cmp i (tree-size l)

SplayTree : BST
SplayTree .BST.T = tree
SplayTree .BST.splay t i with <-cmp i (tree-size t)
... | tri< i<t _ _ = {!   !}
... | tri≈ _ _ _ = ret (0 , t)
... | tri> _ _ _ = ret (0 , t)

-- splayed-size : Splayed → val nat
-- splayed-size (valid t) = tree-size t
-- splayed-size (zig a x b y c) = tree-size a + 1 + tree-size b + 1 + tree-size c
-- splayed-size (zag a y b x c) = tree-size a + 1 + tree-size b + 1 + tree-size c

-- tree-list : Tree → val (list nat)
-- tree-list leaf = []
-- tree-list (node l z r) = tree-list l ++ z ∷ [] ++ tree-list r

-- splay-list : Splayed → val (list nat)
-- splay-list (valid t) = tree-list t
-- splay-list (zig a x b y c) = 
--   tree-list a ++ x ∷ [] ++ tree-list b ++ y ∷ [] ++ tree-list c
-- splay-list (zag a y b x c) =
--   tree-list a ++ y ∷ [] ++ tree-list b ++ x ∷ [] ++ tree-list c

-- tree-list-length : (t : Tree) → length (tree-list t) ≡ tree-size t
-- tree-list-length leaf          = refl
-- tree-list-length (node t x t₁) = Eq.trans (length-++ (tree-list t)) (Eq.trans ((Eq.sym (+-assoc (length (tree-list t)) 1 (length (tree-list t₁))))) (Eq.cong₂ (λ a b → a + 1 + b) (tree-list-length t) (tree-list-length t₁)))

-- size-tree-list : (t t' : Tree) → tree-list t ≡ tree-list t' → tree-size t ≡ tree-size t'
-- size-tree-list t t' p = Eq.trans (Eq.sym (tree-list-length t)) (Eq.trans (Eq.cong length p) (tree-list-length t'))

-- splay-list-length : (s : Splayed) → length (splay-list s) ≡ splayed-size s
-- splay-list-length (valid t)       = tree-list-length t
-- splay-list-length (zig a x b y c) = 
--   let open ≡-Reasoning in
--   begin
--     length (tree-list a ++ (x ∷ tree-list b ++ y ∷ tree-list c))
--   ≡⟨ length-++ (tree-list a) ⟩
--     length (tree-list a) + length (x ∷ tree-list b ++ y ∷ tree-list c)
--   ≡⟨ Eq.cong (_+ length (x ∷ tree-list b ++ y ∷ tree-list c)) (tree-list-length a) ⟩
--     tree-size a + length (x ∷ tree-list b ++ y ∷ tree-list c)
--   ≡⟨ Eq.cong (tree-size a +_) (length-++ (x ∷ tree-list b) {ys = y ∷ tree-list c})  ⟩
--     tree-size a + (length (x ∷ tree-list b) + length (y ∷ tree-list c))
--   ≡⟨ Eq.cong (tree-size a +_) (Eq.cong₂ _+_ {x = length (x ∷ tree-list b)} refl refl) ⟩
--     tree-size a + ((1 + length (tree-list b)) + (1 + length (tree-list c)))
--   ≡⟨ Eq.cong (tree-size a +_) (Eq.cong₂ _+_ (Eq.cong (1 +_) (tree-list-length b)) (Eq.cong (1 +_) (tree-list-length c))) ⟩
--     tree-size a + ((1 + tree-size b) + (1 + tree-size c))
--   ≡⟨ +-assoc (tree-size a) ((1 + tree-size b)) ((1 + tree-size c)) ⟨
--     (tree-size a + (1 + tree-size b)) + (1 + tree-size c)
--   ≡⟨ Eq.cong (_+ (1 + tree-size c)) (+-assoc (tree-size a) 1 (tree-size b)) ⟨
--     (tree-size a + 1 + tree-size b) + (1 + tree-size c)
--   ≡⟨ +-assoc (tree-size a + 1 + tree-size b) 1 (tree-size c) ⟨
--     tree-size a + 1 + tree-size b + 1 + tree-size c
--   ∎ 
-- splay-list-length (zag a y b x c) = 
--   let open ≡-Reasoning in
--   begin
--     length (tree-list a ++ (y ∷ tree-list b ++ x ∷ tree-list c))
--   ≡⟨ length-++ (tree-list a) ⟩
--     length (tree-list a) + length (y ∷ tree-list b ++ x ∷ tree-list c)
--   ≡⟨ Eq.cong (_+ length (y ∷ tree-list b ++ x ∷ tree-list c)) (tree-list-length a) ⟩
--     tree-size a + length (y ∷ tree-list b ++ x ∷ tree-list c)
--   ≡⟨ Eq.cong (tree-size a +_) (length-++ (y ∷ tree-list b) {ys = x ∷ tree-list c})  ⟩
--     tree-size a + (length (y ∷ tree-list b) + length (x ∷ tree-list c))
--   ≡⟨ Eq.cong (tree-size a +_) (Eq.cong₂ _+_ {x = length (y ∷ tree-list b)} refl refl) ⟩
--     tree-size a + ((1 + length (tree-list b)) + (1 + length (tree-list c)))
--   ≡⟨ Eq.cong (tree-size a +_) (Eq.cong₂ _+_ (Eq.cong (1 +_) (tree-list-length b)) (Eq.cong (1 +_) (tree-list-length c))) ⟩
--     tree-size a + ((1 + tree-size b) + (1 + tree-size c))
--   ≡⟨ +-assoc (tree-size a) ((1 + tree-size b)) ((1 + tree-size c)) ⟨
--     (tree-size a + (1 + tree-size b)) + (1 + tree-size c)
--   ≡⟨ Eq.cong (_+ (1 + tree-size c)) (+-assoc (tree-size a) 1 (tree-size b)) ⟨
--     (tree-size a + 1 + tree-size b) + (1 + tree-size c)
--   ≡⟨ +-assoc (tree-size a + 1 + tree-size b) 1 (tree-size c) ⟨
--     tree-size a + 1 + tree-size b + 1 + tree-size c
--   ∎

-- size-splayed-list : (s : Splayed) (t : Tree) → splay-list s ≡ tree-list t → splayed-size s ≡ tree-size t
-- size-splayed-list s t p = Eq.trans (Eq.sym (splay-list-length s)) (Eq.trans (Eq.cong length p) (tree-list-length t))

-- <-splayResultType : Tree → val nat → Splayed → tp⁺
-- <-splayResultType r z l = Σ⁺ splayed λ t' → meta⁺ (splay-list t' ≡ splay-list l ++ z ∷ [] ++ tree-list r)

-- <-splayHelper : (z : val nat) (r : Tree) (l : Splayed) {i : val nat} {i<l : i < (splayed-size l)} → cmp (F (<-splayResultType r z l))
-- <-splayHelper z r (valid (node a x b)) = ret (zig a x b z r , Eq.sym (++-assoc (tree-list a) _ _))
-- <-splayHelper z r (zig a x b y c) = 
--   ret (valid (node a x (node b y (node c z r))) , arithmetic (tree-list a) (x ∷ tree-list b) (y ∷ tree-list c) (z ∷ tree-list r))
--     where 
--       arithmetic : (l₁ l₂ l₃ l₄ : val (list nat)) → l₁ ++ l₂ ++ l₃ ++ l₄ ≡ (l₁ ++ l₂ ++ l₃) ++ l₄
--       arithmetic l₁ l₂ l₃ l₄ = 
--         let open Eq.≡-Reasoning in 
--         begin 
--           l₁ ++ l₂ ++ l₃ ++ l₄
--         ≡⟨ ++-assoc l₁ l₂ (l₃ ++ l₄) ⟨ 
--           (l₁ ++ l₂) ++ l₃ ++ l₄
--         ≡⟨ ++-assoc (l₁ ++ l₂) l₃ l₄ ⟨ 
--           ((l₁ ++ l₂) ++ l₃) ++ l₄
--         ≡⟨ Eq.cong (λ l → l ++ l₄) (++-assoc l₁ l₂ l₃) ⟩ 
--           (l₁ ++ l₂ ++ l₃) ++ l₄
--         ∎
-- <-splayHelper z r (zag a y b x c) = 
--   ret (valid (node (node a y b) x (node c z r)) , arithmetic (tree-list a) (y ∷ tree-list b) (x ∷ tree-list c) (z ∷ tree-list r))
--     where 
--       arithmetic : (l₁ l₂ l₃ l₄ : val (list nat)) → (l₁ ++ l₂) ++ l₃ ++ l₄ ≡ (l₁ ++ l₂ ++ l₃) ++ l₄
--       arithmetic l₁ l₂ l₃ l₄ = 
--         let open ≡-Reasoning in
--         begin
--           (l₁ ++ l₂) ++ l₃ ++ l₄
--         ≡⟨ ++-assoc (l₁ ++ l₂) l₃ l₄ ⟨
--           ((l₁ ++ l₂) ++ l₃) ++ l₄
--         ≡⟨ Eq.cong (_++ l₄) (++-assoc l₁ l₂ l₃) ⟩
--           (l₁ ++ l₂ ++ l₃) ++ l₄
--         ∎

-- >-splayResultType : Tree → val nat → Splayed → tp⁺
-- >-splayResultType l z r = Σ⁺ splayed λ t' → meta⁺ (splay-list t' ≡ tree-list l ++ z ∷ [] ++ splay-list r)

-- >-splayHelper : (z : val nat) (l : Tree) (r : Splayed) {i : val nat} {i<r : i < splayed-size r} → cmp (F (>-splayResultType l z r))
-- >-splayHelper z l (valid (node a x b)) = 
--   ret (zag l z a x b , refl)
-- >-splayHelper z l (zig a x b y c) = 
--   ret (valid (node (node l z a) x (node b y c)) , arithmetic (tree-list l) (z ∷ tree-list a) (x ∷ tree-list b) (y ∷ tree-list c))
--     where 
--       arithmetic : (l₁ l₂ l₃ l₄ : val (list nat)) → (l₁ ++ l₂) ++ l₃ ++ l₄ ≡ l₁ ++ l₂ ++ l₃ ++ l₄
--       arithmetic l₁ l₂ l₃ l₄ = 
--         let open ≡-Reasoning in
--           (l₁ ++ l₂) ++ (l₃ ++ l₄)
--         ≡⟨ ++-assoc l₁ l₂ (l₃ ++ l₄) ⟩
--           l₁ ++ l₂ ++ l₃ ++ l₄
--         ∎
-- >-splayHelper z l (zag a y b x c) = 
--   ret (valid (node (node (node l z a) y b) x c) , arithmetic (tree-list l) (z ∷ tree-list a) (y ∷ tree-list b) (x ∷ tree-list c))
--     where
--       arithmetic : (l₁ l₂ l₃ l₄ : val (list nat)) → ((l₁ ++ l₂) ++ l₃) ++ l₄ ≡ l₁ ++ l₂ ++ l₃ ++ l₄
--       arithmetic l₁ l₂ l₃ l₄ = 
--         let open ≡-Reasoning in 
--         begin
--           ((l₁ ++ l₂) ++ l₃) ++ l₄
--         ≡⟨ ++-assoc (l₁ ++ l₂) l₃ l₄ ⟩
--           (l₁ ++ l₂) ++ (l₃ ++ l₄)
--         ≡⟨ ++-assoc l₁ l₂ (l₃ ++ l₄) ⟩
--           l₁ ++ (l₂ ++ (l₃ ++ l₄))
--         ∎

-- splayResultType : Tree → tp⁺ 
-- splayResultType t = Σ⁺ splayed λ l → meta⁺ (splay-list l ≡ tree-list t)

-- splay : (t : Tree) → (i : val nat) → i < (tree-size t) → cmp (F (splayResultType t))
-- splay (node l z r) i i<t with <-cmp i (tree-size l)
-- ... | tri< i<l i≢l _ = 
--   bind (F (splayResultType (node l z r))) (splay l i i<l) λ (l' , l'≡l) → 
--     bind (F _) (<-splayHelper z r l' {i = i} {i<l = Eq.subst (λ n → i < n) (Eq.sym (size-splayed-list l' l l'≡l)) i<l}) λ (l'' , l''≡r+1+l') → 
--       ret (l'' , Eq.trans l''≡r+1+l' (Eq.cong (λ l → l ++ z ∷ tree-list r) l'≡l)) 
-- ... | tri≈ _ _ _ = ret (valid (node l z r) , refl)
-- ... | tri> _ _ i>l = 
--   let
--     arithmetic : i ∸ ((tree-size l) + 1) Nat.< (tree-size r)
--     arithmetic = let open Nat.≤-Reasoning in 
--       Nat.+-cancelˡ-< ((tree-size l) + 1) (i ∸ ((tree-size l) + 1)) (tree-size r) (
--         begin-strict
--           ((tree-size l) + 1) + (i ∸ ((tree-size l) + 1))
--         ≡⟨ Nat.m+[n∸m]≡n (Eq.subst (i Nat.≥_) (Nat.+-comm 1 (tree-size l)) i>l) ⟩ 
--           i
--         <⟨ i<t ⟩
--           (tree-size l) + 1 + (tree-size r)
--         ∎
--       )
--   in 
--     bind (F (splayResultType (node l z r))) (splay r (i ∸ ((tree-size l) + 1)) arithmetic) λ (r' , r'≡r) → 
--       bind (F _) (>-splayHelper z l r' {i = i ∸ (tree-size l + 1)} {i<r = Eq.subst (λ n → i ∸ (tree-size l + 1) < n) (Eq.sym (size-splayed-list r' r r'≡r)) arithmetic}) λ (r'' , r''≡l+1+r') → 
--         ret (r'' , Eq.trans r''≡l+1+r' (Eq.cong (λ l' → tree-list l ++ z ∷ l') r'≡r))

-- splayTopLevelHelper : (t : Splayed) {i : val nat} {i<t : i < splayed-size t} → cmp (F (nat ×⁺ (meta⁺ (Tree))))
-- splayTopLevelHelper (valid (node l z r)) = ret (z , node l z r)
-- splayTopLevelHelper (zig a x b y c) = ret (y , node (node a x b) y c)
-- splayTopLevelHelper (zag a y b x c) = ret (y , node a x (node b y c)) 

-- SplayTree : BST
-- SplayTree .BST.T = tree
-- SplayTree .BST.splay t i with <-cmp i (tree-size t)
-- ... | tri< i<t _ _ = 
--   bind (F _) (splay t i i<t) 
--     (λ (t' , t'≡t) → splayTopLevelHelper t' {i = i} {i<t = Eq.subst (λ n → i < n) (Eq.sym (size-splayed-list t' t t'≡t)) i<t})
-- ... | tri≈ _ _ _ = ret (0 , t)
-- ... | tri> _ _ _ = ret (0 , t)

-- open BST renaming (splay to splay')

-- record BSTHom (bst bst' : BST) : Set where
--   field
--     ϕ : cmp (Π (bst .T) λ _ → F (bst' .T))
--     ϕ/splay : (t : val (bst .T)) (i : val nat) → 
--         bind (F _) (bst .splay' t i) (λ { (_ , t') → ϕ t'})
--       ≤⁻[ F (bst' .T) ]
--         bind (F _) (ϕ t) (λ t' → bind (F _) (bst' .splay' t' i) (λ { (_ , t'') → ret t''}))
        
-- open BSTHom

-- rank : (T : Tree) → val nat
-- rank t = ⌊log₂ (tree-size t)⌋

rank' : (s : Splayed) → val nat
rank' s = ⌊log₂ splayed-size s ⌋

-- sum-of-ranks : (T : Tree) → val nat
-- sum-of-ranks leaf = 0
-- sum-of-ranks (node l z r) = sum-of-ranks l + rank (node l z r) + sum-of-ranks r

-- log-rule : (x : val nat) → 2 ^ ⌊log₂ (suc x)⌋ Nat.≤ suc x
-- log-rule Nat.zero = 
--   let open Nat.≤-Reasoning in
--   begin
--     2 ^ ⌊log₂ 1 ⌋
--   ≡⟨⟩
--     1
--   ∎
-- log-rule (suc x) = 
--   let open Nat.≤-Reasoning in
--   begin
--     2 ^ ⌊log₂ suc (suc x) ⌋
--   ≡⟨ Eq.cong (2 ^_) {x = ⌊log₂ suc (suc x) ⌋} {y = 1 + ⌊log₂ (suc ⌊ x /2⌋)⌋} {!   !} ⟩
--     2 ^ (1 + ⌊log₂ (suc ⌊ x /2⌋)⌋)
--   ≡⟨ {!   !} ⟩
--     suc (suc x)
--   ∎

-- rank-rule : (l : Tree) (z : val nat) (r : Tree) → rank l ≡ rank r → (rank l) + 1 Nat.≤ rank (node l z r)
-- rank-rule l z r p = 
--   let open Nat.≤-Reasoning in 
--   begin
--     rank l + 1
--   ≡⟨⟩
--     ⌊log₂ (tree-size l)⌋ + 1
--   ≡⟨ {!   !} ⟩
--     ⌊log₂ (2 * tree-size l)⌋
--   ≡⟨ {!   !} ⟩
--     rank (node l z r)
--   ∎
--   where
--     tree-size-lemma : (t : Tree) → 2 ^ (rank t) Nat.≤ tree-size t
--     tree-size-lemma t = 
--       let open Nat.≤-Reasoning in
--       begin
--         2 ^ rank t
--       ≡⟨ {!   !} ⟩
--         tree-size t
--       ∎


-- ST⇒LT : BSTHom SplayTree ListTree
-- ST⇒LT .ϕ t = step (F _) (sum-of-ranks t) (ret (tree-list t))
-- ST⇒LT .ϕ/splay t i with <-cmp i (tree-size t)
-- ... | tri< a ¬b ¬c = {!   !}
-- ... | tri≈ ¬a b ¬c = 
--   let open ≤⁻-Reasoning (F (meta⁺ (List ℕ))) in 
--   begin
--     {!   !}
--   ≡⟨ {!   !} ⟩
--     {!   !}
--   ∎
-- ... | tri> _ _ _ = {!   !}



-- {-
--   - define s(x) = Σ w(y) ∀ y ∈ T(x)
--   - define w(y) = 1 ∀ y ∈ T
-- 2) define and prove rank rule: Suppose that two siblings have the same rank, r. Then the parent has rank at least r+1.
-- 3) define and prove splay step cost
-- 4) define and prove access lemma
-- 5) define and prove balance theorem (overall amortized cost)

-- Actually proving in Agda:

-- Rank rule is its own lemma seperately
-- splay step is <-splayHelper and >-splayHelper
-- access lemma is cost of whole splay (no need to account for BST .splay or splayTopLevelHelper
-- modified balance theorem is thm (like in queue-again)

-- Modifications from original proof:

-- For access lemma, proof weaker bound of 3log₂n + 1 (harder to quantify r(i)) for splay t i
-- Prove amortized portion of balance theorem (i.e. mlogn amortized instead of mlogn + nlogn for actual)
-- -}