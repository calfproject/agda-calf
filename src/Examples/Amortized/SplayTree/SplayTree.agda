{-# OPTIONS --rewriting #-}

module Examples.Amortized.SplayTree.SplayTree where

open import Algebra.Cost

costMonoid = ℕ-CostMonoid
open CostMonoid costMonoid renaming (_+_ to _⊕_)

open import Calf costMonoid 
open import Calf.Data.List hiding (find)
open import Calf.Data.Nat 
open import Calf.Data.Bool as Bool using (bool; true; false)
open import Calf.Data.Product

open import Data.Nat as Nat using (ℕ; _<_; _≤?_; _<?_; zero)
open import Data.Nat.Properties as Nat using (module ≤-Reasoning; _≟_)
open import Data.Bool.Properties as Bool
open import Data.List.Properties as List

open import Relation.Binary 
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≢_; refl; module ≡-Reasoning)

open import Data.Empty using (⊥; ⊥-elim)

open import Examples.Amortized.SplayTree.Base

data Tree : Set where
  leaf : Tree
  node : Tree → val nat → Tree → Tree

tree : tp⁺
tree = meta⁺ Tree  

tree-size : Tree → val nat
tree-size leaf = 0
tree-size (node l z r) = (tree-size l) + 1 + (tree-size r)

inord : Tree → val (list nat)
inord leaf = []
inord (node l z r) = inord l ++ z ∷ [] ++ inord r

data Context : Set where
  Left  : (k : val nat) (t : Tree) → Context
  Right : (t : Tree) (k : val nat) → Context

context : tp⁺
context = meta⁺ (Context)

searchType : tp⁺
searchType = bool ×⁺ tree ×⁺ (list context)

reconstruct : (t : Tree) (anc : List Context) → Tree
reconstruct t [] = t
reconstruct t (Left x r ∷ anc') = reconstruct (node t x r) anc'
reconstruct t (Right l x ∷ anc') = reconstruct (node l x t) anc'

inord/reconstruct : (t₁ t₂ : Tree) (anc : List Context) → inord t₁ ≡ inord t₂ →
  inord (reconstruct t₁ anc) ≡ inord (reconstruct t₂ anc)
inord/reconstruct t₁ t₂ [] t₁≡t₂ = t₁≡t₂
inord/reconstruct t₁ t₂ (Left k t ∷ anc) t₁≡t₂ = 
  inord/reconstruct (node t₁ k t) (node t₂ k t) anc 
    (Eq.cong (λ e → e ++ (k ∷ inord t)) t₁≡t₂)
inord/reconstruct t₁ t₂ (Right t k ∷ anc) t₁≡t₂ = 
  inord/reconstruct (node t k t₁) (node t k t₂) anc 
    (Eq.cong (λ e → inord t ++ e) (Eq.cong (λ e → k ∷ e) t₁≡t₂))

-- when we have empty tree return default value of 0 since there is no root
root : (t : Tree) → val nat
root leaf = 0
root (node l x r) = x

size>0 : (a : Tree) (z : val nat) (b : Tree) → tree-size (node a z b) > 0
size>0 a z b = let open Nat.≤-Reasoning in 
  begin
    1
  ≤⟨ Nat.m≤m+n 1 (tree-size a + tree-size b) ⟩
    1 + (tree-size a + tree-size b)
  ≡⟨ Nat.+-assoc 1 (tree-size a) (tree-size b) ⟨
    (1 + tree-size a) + tree-size b
  ≡⟨ Eq.cong (λ e → e + tree-size b) (Nat.+-comm 1 (tree-size a)) ⟩
    (tree-size a + 1) + tree-size b
  ∎

searchInordType : Tree → val nat → List Context → tp⁺
searchInordType t k anc = Σ⁺ searchType (λ (b , t' , anc') → 
  (meta⁺ (reconstruct t anc ≡ reconstruct t' anc')) ×⁺ 
   meta⁺ ((b ≡ true) → 0 < tree-size t') ×⁺
   meta⁺ ((b ≡ true) → root t' ≡ k)) 

search : (t : Tree) (k : val nat) (anc : List Context) → val (searchInordType t k anc)
search leaf k anc = 
  (((false , leaf , anc) , refl , (λ x → ⊥-elim (Bool.<-irrefl x Bool.f<t)) , λ x → ⊥-elim (Bool.<-irrefl x Bool.f<t)))
search (node l x r) k anc with Nat.<-cmp k x 
... | tri< _ _ _   = search l k (Left x r ∷ anc)
... | tri≈ _ k≡x _ = 
  (((true , node l x r , anc) , refl , (λ _ → size>0 l x r) , λ _ → Eq.sym k≡x))
... | tri> _ _ _   = search r k (Right l x ∷ anc)

splay'ResultType : val nat → Tree → Tree → List Context → tp⁺
splay'ResultType k a b anc = Σ⁺ (tree ×⁺ tree) (λ (a' , b') → 
  meta⁺ (inord (reconstruct (node a k b) anc) ≡ inord (node a' k b')))

zig/zig/arithmetic : (l₁ l₂ l₃ l₄ : val (list nat)) → ((l₁ ++ l₂) ++ l₃) ++ l₄ ≡ l₁ ++ l₂ ++ l₃ ++ l₄
zig/zig/arithmetic l₁ l₂ l₃ l₄ = 
  let open ≡-Reasoning in 
  begin
    ((l₁ ++ l₂) ++ l₃) ++ l₄
  ≡⟨ ++-assoc (l₁ ++ l₂) l₃ l₄ ⟩
    (l₁ ++ l₂) ++ (l₃ ++ l₄)
  ≡⟨ ++-assoc l₁ l₂ (l₃ ++ l₄) ⟩
    l₁ ++ (l₂ ++ (l₃ ++ l₄))
  ∎
zig/zig/inord/arith : (a b c d : Tree) (k p g : val nat) →  
  inord (node (node (node a k b) p c) g d) ≡ inord (node a k (node b p (node c g d)))
zig/zig/inord/arith a b c d k p g = zig/zig/arithmetic (inord a) (k ∷ inord b) (p ∷ inord c) (g ∷ inord d)

zig/zag/arithmetic : (l₁ l₂ l₃ l₄ : val (list nat)) → (l₁ ++ l₂ ++ l₃) ++ l₄ ≡ (l₁ ++ l₂) ++ l₃ ++ l₄
zig/zag/arithmetic l₁ l₂ l₃ l₄ = 
  let open ≡-Reasoning in
  begin
    (l₁ ++ (l₂ ++ l₃)) ++ l₄
  ≡⟨ Eq.cong (λ e → e ++ l₄) (++-assoc l₁ l₂ l₃) ⟨
    ((l₁ ++ l₂) ++ l₃) ++ l₄
  ≡⟨ ++-assoc (l₁ ++ l₂) l₃ l₄ ⟩
    (l₁ ++ l₂) ++ l₃ ++ l₄
  ∎
zig/zag/inord/arith : (a b c d : Tree) (k p g : val nat) → 
  inord (node (node a p (node b k c)) g d) ≡ inord (node (node a p b) k (node c g d))
zig/zag/inord/arith a b c d k p g = zig/zag/arithmetic (inord a) (p ∷ inord b) (k ∷ inord c) (g ∷ inord d)


zag/zag/arithmetic : (l₁ l₂ l₃ l₄ : val (list nat)) → l₁ ++ l₂ ++ l₃ ++ l₄ ≡ ((l₁ ++ l₂) ++ l₃) ++ l₄
zag/zag/arithmetic l₁ l₂ l₃ l₄ = 
  let open ≡-Reasoning in
  begin
    l₁ ++ (l₂ ++ (l₃ ++ l₄))
  ≡⟨ ++-assoc l₁ l₂ (l₃ ++ l₄) ⟨
    (l₁ ++ l₂) ++ (l₃ ++ l₄)
  ≡⟨ ++-assoc (l₁ ++ l₂) l₃ l₄ ⟨
    ((l₁ ++ l₂) ++ l₃) ++ l₄
  ∎

zag/zag/inord/arith : (a b c d : Tree) (k p g : val nat) → 
  inord (node a g (node b p (node c k d))) ≡ inord (node (node (node a g b) p c) k d)
zag/zag/inord/arith a b c d k p g = zag/zag/arithmetic (inord a) (g ∷ inord b) (p ∷ inord c) (k ∷ inord d)

zag/zig/arithmetic : (l₁ l₂ l₃ l₄ : val (list nat)) → l₁ ++ (l₂ ++ l₃) ++ l₄ ≡ (l₁ ++ l₂) ++ l₃ ++ l₄
zag/zig/arithmetic l₁ l₂ l₃ l₄ =
  let open ≡-Reasoning in
  begin
    l₁ ++ (l₂ ++ l₃) ++ l₄
  ≡⟨ ++-assoc l₁ (l₂ ++ l₃) l₄ ⟨
    (l₁ ++ (l₂ ++ l₃)) ++ l₄
  ≡⟨ Eq.cong (λ e → e ++ l₄) (++-assoc l₁ l₂ l₃) ⟨
    ((l₁ ++ l₂) ++ l₃) ++ l₄
  ≡⟨ ++-assoc (l₁ ++ l₂) l₃ l₄ ⟩
    (l₁ ++ l₂) ++ l₃ ++ l₄
  ∎

zag/zig/inord/arith : (a b c d : Tree) (k p g : val nat) →  
  inord (node a g (node (node b k c) p d)) ≡ inord (node (node a g b) k (node c p d))
zag/zig/inord/arith a b c d k p g = zag/zig/arithmetic (inord a) (g ∷ inord b) (k ∷ inord c) (p ∷ inord d)


splay' : (a : Tree) (b : Tree) (anc : List Context) (k : val nat) → cmp (F (splay'ResultType k a b anc))
-- done
splay' a b [] k = ret ((a , b) , refl)
-- zig
splay' a b (Left p c ∷ []) k = 
  step (F _) 1 (
    ret ((a , node b p c) , ++-assoc (inord a) (k ∷ inord b) (p ∷ inord c)))
-- zag
splay' b c (Right a p ∷ []) k = 
  step (F _) 1 (
    ret ((node a p b , c) , arithmetic (inord a) (p ∷ inord b) (k ∷ inord c)))
  where
    arithmetic : (l₁ l₂ l₃ : val (list nat)) → l₁ ++ l₂ ++ l₃ ≡ (l₁ ++ l₂) ++ l₃
    arithmetic l₁ l₂ l₃ = Eq.sym (++-assoc l₁ l₂ l₃)
-- zig-zig
splay' a b (Left p c ∷ Left g d ∷ anc) k = 
  step (F _) 1 (
    bind (F _) (splay' a (node b p (node c g d)) anc k) (λ ((l' , r') , recon≡inord) → 
      ret ((l' , r') , Eq.trans (inord/reconstruct 
        (node (node (node a k b) p c) g d)
        (node a k (node b p (node c g d)))
        anc
        (zig/zig/inord/arith a b c d k p g)) recon≡inord)))
-- zag-zig
splay' b c (Left p d ∷ Right a g ∷ anc) k = 
  step (F _) 1 (
    bind (F _) (splay' (node a g b) (node c p d) anc k) (λ ((l' , r') , recon≡inord) →
      ret ((l' , r') , Eq.trans (inord/reconstruct
        (node a g (node (node b k c) p d))
        (node (node a g b) k (node c p d))
        anc
        (zag/zig/inord/arith a b c d k p g)) recon≡inord)))
-- zig-zag
splay' b c (Right a p ∷ Left g d ∷ anc) k = 
  step (F _) 1 (
    bind (F _) (splay' (node a p b) (node c g d) anc k) (λ ((l' , r') , recon≡inord) →
      ret ((l' , r') , Eq.trans (inord/reconstruct
        (node (node a p (node b k c)) g d)
        (node (node a p b) k (node c g d))
        anc
        (zig/zag/inord/arith a b c d k p g)) recon≡inord)))
-- zag-zag
splay' c d (Right b p ∷ Right a g ∷ anc) k = 
  step (F _) 1 (
    bind (F _) (splay' (node (node a g b) p c) d anc k) (λ ((l' , r') , recon≡inord) →
      ret ((l' , r') , Eq.trans (inord/reconstruct
        (node a g (node b p (node c k d)))
        (node (node (node a g b) p c) k d)
        anc 
        (zag/zag/inord/arith a b c d k p g)) recon≡inord)))
makeTree/nodups/sorted : (t : Tree) (l : val (list nat)) → val (tree)
makeTree/nodups/sorted t [] = t
makeTree/nodups/sorted t (k ∷ ks) = makeTree/nodups/sorted (node t k leaf) ks

SplayTree : BST
SplayTree .BST.T = tree
SplayTree .BST.fromList l = ret (makeTree/nodups/sorted leaf (sort/val (deduplicate {R = _≡_} Nat._≟_ l)))
SplayTree .BST.size t = ret (tree-size t)
SplayTree .BST.find t k with (search t k []) 
... | ((false , t' , anc) , _ , _ , _) = ret (false , t)
... | ((true , leaf , anc) , _ , 0<0 , _) = ⊥-elim (Nat.<-irrefl refl (0<0 refl))
... | ((true , node l x r , anc) , _ , _ , _) = 
  bind (F _) (splay' l r anc k) (λ ((l' , r') , _) → ret (true , node l' x r')) 
