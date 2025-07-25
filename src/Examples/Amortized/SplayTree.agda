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
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≢_; refl; module ≡-Reasoning)

open import Tactic.MonoidSolver using (solve; solve-macro)

open import Data.Nat.Logarithm
open import Data.Nat.PredExp2
open import Data.Empty using (⊥; ⊥-elim)

open import Data.Nat.Tactic.RingSolver


record BST : Set where
  field 
    T : tp⁺
    splay : cmp (Π T (λ _ → Π nat (λ _ → F (nat ×⁺ T))))

ListTree : BST
ListTree .BST.T = list nat
ListTree .BST.splay l i with i <? length l 
... | yes p = let i' = fromℕ< p in step (F _) ((3 * ⌊log₂ (length l)⌋) + 1) (ret (lookup l i' , l))
... | no _ = ret (i , l)

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

inord/cmp : cmp (Π tree λ _ → F (list nat))
inord/cmp leaf = ret []
inord/cmp (node l z r) = 
  bind (F _) (inord/cmp l) (λ l' → 
  bind (F _) (inord/cmp r) (λ r' → ret (l' ++ z ∷ [] ++ r'))) 

data Context : Set where
  Left  : (k : val nat) (t : Tree) → Context
  Right : (t : Tree) (k : val nat) → Context

context : tp⁺
context = meta⁺ (Context)

pathType : tp⁺
pathType = tree ×⁺ (list context)

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

root : (t : Tree) (k : val nat) → val nat
root leaf k = k
root (node l x r) k = x

pathInordType : val nat → Tree → List Context → tp⁺
pathInordType k t anc = Σ⁺ pathType (λ (t' , anc') → 
  (meta⁺ (reconstruct t anc ≡ reconstruct t' anc')) ×⁺ meta⁺ (root t' k ≡ k)) 

path : (k : val nat) (t : Tree) (anc : List Context) → cmp (F (pathInordType k t anc))
path k leaf anc = ret ((leaf , anc) , refl , refl)
path k (node l x r) anc with <-cmp k x 
... | tri< _ _ _   = path k l (Left x r ∷ anc)
... | tri≈ _ k≡x _ = ret ((node l x r , anc) , refl , Eq.sym k≡x)
... | tri> _ _ _   = path k r (Right l x ∷ anc)

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

splay' : (a : Tree) (b : Tree) (anc : List Context) (k : val nat) → cmp (F (splay'ResultType k a b anc))
splay' a b [] k = ret ((a , b) , refl)
-- done
splay' a b (Left p c ∷ []) k = 
  step (F _) 1 (
    ret ((a , node b p c) , ++-assoc (inord a) (k ∷ inord b) (p ∷ inord c)))
-- zig
splay' b c (Right a p ∷ []) k = 
  step (F _) 1 (
    ret ((node a p b , c) , arithmetic (inord a) (p ∷ inord b) (k ∷ inord c)))
  where
    arithmetic : (l₁ l₂ l₃ : val (list nat)) → l₁ ++ l₂ ++ l₃ ≡ (l₁ ++ l₂) ++ l₃
    arithmetic l₁ l₂ l₃ = Eq.sym (++-assoc l₁ l₂ l₃)
-- zag
splay' a b (Left p c ∷ Left g d ∷ anc) k = 
  step (F _) 1 (
    bind (F _) (splay' a (node b p (node c g d)) anc k) (λ ((l' , r') , recon≡inord) → 
      ret ((l' , r') , Eq.trans (inord/reconstruct 
        (node (node (node a k b) p c) g d)
        (node a k (node b p (node c g d)))
        anc
        (zig/zig/inord/arith a b c d k p g)) recon≡inord)))
-- zig-zig
splay' b c (Left p d ∷ Right a g ∷ anc) k = 
  bind (F _) (splay' (node a g b) (node c p d) anc k) (λ ((l' , r') , recon≡inord) → 
    step (F _) 1 (
      ret ((l' , r') , Eq.trans (inord/reconstruct 
       (node a g (node (node b k c) p d))
       (node (node a g b) k (node c p d))
       anc 
       (inord/arith a b c d k p g)) recon≡inord)))
  where
    arithmetic : (l₁ l₂ l₃ l₄ : val (list nat)) → l₁ ++ (l₂ ++ l₃) ++ l₄ ≡ (l₁ ++ l₂) ++ l₃ ++ l₄
    arithmetic l₁ l₂ l₃ l₄ = 
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
    inord/arith : (a b c d : Tree) (k p g : val nat) →  
      inord (node a g (node (node b k c) p d)) ≡ inord (node (node a g b) k (node c p d))
    inord/arith a b c d k p g = arithmetic (inord a) (g ∷ inord b) (k ∷ inord c) (p ∷ inord d)
-- zag-zig
splay' b c (Right a p ∷ Left g d ∷ anc) k = 
  step (F _) 1 (
    bind (F _) (splay' (node a p b) (node c g d) anc k) (λ ((l' , r') , recon≡inord) →
      ret ((l' , r') , Eq.trans (inord/reconstruct
        (node (node a p (node b k c)) g d)
        (node (node a p b) k (node c g d))
        anc
        (zig/zag/inord/arith a b c d k p g)) recon≡inord)))
-- zig-zag
splay' c d (Right b p ∷ Right a g ∷ anc) k = 
  bind (F _) (splay' (node (node a g b) p c) d anc k) (λ ((l' , r') , recon≡inord) →
    step (F _) 1 (
      ret ((l' , r') , Eq.trans (inord/reconstruct 
       (node a g (node b p (node c k d)))
       (node (node (node a g b) p c) k d)
       anc 
       (inord/arith a b c d k p g)) recon≡inord)))
  where
    arithmetic : (l₁ l₂ l₃ l₄ : val (list nat)) → l₁ ++ l₂ ++ l₃ ++ l₄ ≡ ((l₁ ++ l₂) ++ l₃) ++ l₄
    arithmetic l₁ l₂ l₃ l₄ = 
      let open ≡-Reasoning in
      begin
        l₁ ++ (l₂ ++ (l₃ ++ l₄))
      ≡⟨ ++-assoc l₁ l₂ (l₃ ++ l₄) ⟨
        (l₁ ++ l₂) ++ (l₃ ++ l₄)
      ≡⟨ ++-assoc (l₁ ++ l₂) l₃ l₄ ⟨
        ((l₁ ++ l₂) ++ l₃) ++ l₄
      ∎
    inord/arith : (a b c d : Tree) (k p g : val nat) → 
      inord (node a g (node b p (node c k d))) ≡ inord (node (node (node a g b) p c) k d)
    inord/arith a b c d k p g = arithmetic (inord a) (g ∷ inord b) (p ∷ inord c) (k ∷ inord d)
-- zag-zag

splayResultType : (t' : Tree) → (k : val nat) → List Context → k ≡ root t' k → tp⁺
splayResultType t' k anc k≡root = Σ⁺ (nat ×⁺ tree) (λ (k' , t'') → 
  (meta⁺ (inord (reconstruct t' anc) ≡ inord t'')) ×⁺ (meta⁺ (0 < tree-size t' → k ≡ root t'' k)) ×⁺ (meta⁺ (k' ≡ k)))

splay : (t' : Tree) (k : val nat) (anc : List Context) (k≡root : k ≡ root t' k) → cmp (F (splayResultType t' k anc k≡root))
splay leaf k anc k≡root = ret ((k , reconstruct leaf anc) , refl , (λ x → ⊥-elim (Nat.<-irrefl refl x)) , refl)
splay (node l x r) k anc k≡root = bind (F _) (splay' l r anc k) (λ ((l' , r') , t''≡recon) → 
  ret ((x , node l' x r') , 
      Eq.trans 
        (inord/reconstruct (node l x r) (node l k r) anc (inord/arith l r x k≡root)) 
        (Eq.trans t''≡recon (Eq.sym (inord/arith l' r' x k≡root))) , 
      (λ _ → k≡root) , 
      Eq.sym k≡root))
  where
    inord/arith : (l r : Tree) (x : val nat) (k≡x : k ≡ x) → inord (node l x r) ≡ inord (node l k r)
    inord/arith l r x k≡x = Eq.cong (λ e → inord l ++ e) (Eq.cong (λ e → e ∷ inord r) (Eq.sym k≡x))

SplayTree : BST
SplayTree .BST.T = tree
SplayTree .BST.splay t k =
  bind (F _) (path k t []) (λ ((t' , anc) , _ , k≡root) → 
    bind (F _) (splay t' k anc (Eq.sym k≡root)) (λ ((k' , t'') , _ , _ , _) → ret (k' , t''))) 

rank : (T : Tree) → val nat
rank t = ⌊log₂ (tree-size t)⌋

sum-of-ranks : (T : Tree) → val nat
sum-of-ranks leaf = 0
sum-of-ranks (node l z r) = sum-of-ranks l + rank (node l z r) + sum-of-ranks r

rank-rule : ∀ l {{_ : NonZero (tree-size l)}} → (z : val nat) → ∀ r {{_ : NonZero (tree-size r)}} → 
            rank l ≡ rank r → rank l + 1 Nat.≤ rank (node l z r)
rank-rule l z r p = 
  let open Nat.≤-Reasoning in 
  begin
    rank l + 1
  ≡⟨ ⌊log₂[2^n]⌋≡n (rank l + 1) ⟨
    ⌊log₂ (2 ^ (rank l + 1)) ⌋
  ≡⟨ Eq.cong (λ e → ⌊log₂ (2 ^ e) ⌋) (Nat.+-comm (rank l) 1) ⟩
    ⌊log₂ (2 ^ suc (rank l)) ⌋
  ≡⟨ Eq.cong (λ e → ⌊log₂ e ⌋) (lemma/2^suc (rank l)) ⟨
    ⌊log₂ (2 ^ rank l + 2 ^ rank l) ⌋
  ≡⟨ Eq.cong (λ e → ⌊log₂ (2 ^ rank l + 2 ^ e) ⌋) p ⟩
    ⌊log₂ (2 ^ rank l + 2 ^ rank r) ⌋
  ≤⟨ ⌊log₂⌋-mono-≤ (Nat.n≤1+n (2 ^ rank l + 2 ^ rank r)) ⟩
    ⌊log₂ (1 + 2 ^ rank l + 2 ^ rank r) ⌋
  ≡⟨ Eq.cong (λ e → ⌊log₂ e ⌋) (Nat.+-assoc 1 (2 ^ rank l) (2 ^ rank r)) ⟨
    ⌊log₂ (1 + 2 ^ rank l + 2 ^ rank r) ⌋
  ≡⟨ Eq.cong (λ e → ⌊log₂ (e + 2 ^ rank r) ⌋) (Nat.+-comm 1 (2 ^ rank l)) ⟩
    ⌊log₂ (2 ^ rank l + 1 + 2 ^ rank r) ⌋
  ≤⟨ ⌊log₂⌋-mono-≤ (Nat.+-mono-≤ (Nat.+-monoˡ-≤ 1 (rank-to-size l (rank l) refl)) (rank-to-size r (rank r) refl)) ⟩
    ⌊log₂ (tree-size l + 1 + tree-size r) ⌋
  ≡⟨⟩
    rank (node l z r)
  ∎
  where
    rank-to-size : ∀ t {{_ : NonZero (tree-size t)}} → (x : val nat) → x ≡ rank t → 2 ^ x Nat.≤ tree-size t
    rank-to-size t x p = 
      let open Nat.≤-Reasoning in
      begin
        2 ^ x
      ≡⟨ Eq.cong (λ e → 2 ^ e) p ⟩
        2 ^ (rank t)
      ≡⟨⟩
        2 ^ ⌊log₂ (tree-size t)⌋
      ≤⟨ log-rule (tree-size t) ⟩
        tree-size t
      ∎
      where
        log-rule : ∀ n {{p : NonZero n}} → 2 ^ ⌊log₂ n ⌋ Nat.≤ n
        log-rule n = lemma
          where
            open import Data.Nat.Logarithm.Core
            open import Induction.WellFounded using (Acc; acc)

            lemma : ∀ {n acc} {{p : NonZero n}} → 2 ^ (⌊log2⌋ n acc) Nat.≤ n
            lemma {suc Nat.zero} {acc _} = s≤s z≤n
            lemma {2+ n} {acc rs} = 
              let open Nat.≤-Reasoning in
              begin
                2 ^ ⌊log2⌋ (suc ⌊ n /2⌋) (rs (s≤s (s≤s (Nat.⌊n/2⌋≤n n)))) +
                  (2 ^ ⌊log2⌋ (suc ⌊ n /2⌋) (rs (s≤s (s≤s (Nat.⌊n/2⌋≤n n)))) + Nat.zero)
              ≡⟨ Eq.cong (λ e → 2 ^ ⌊log2⌋ (suc ⌊ n /2⌋) (rs (s≤s (s≤s (Nat.⌊n/2⌋≤n n)))) + e) 
                  (Nat.+-comm (2 ^ ⌊log2⌋ (suc ⌊ n /2⌋) (rs (s≤s (s≤s (Nat.⌊n/2⌋≤n n))))) Nat.zero) ⟩
                2 ^ ⌊log2⌋ (suc ⌊ n /2⌋) (rs (s≤s (s≤s (Nat.⌊n/2⌋≤n n)))) +
                  2 ^ ⌊log2⌋ (suc ⌊ n /2⌋) (rs (s≤s (s≤s (Nat.⌊n/2⌋≤n n))))
              ≤⟨ Nat.+-mono-≤ lemma lemma ⟩
                (suc ⌊ n /2⌋) + (suc ⌊ n /2⌋)
              ≡⟨ arithmetic 1 ⌊ n /2⌋ 1 ⌊ n /2⌋ ⟩
                (1 + 1) + (⌊ n /2⌋ + ⌊ n /2⌋)
              ≤⟨ s≤s (s≤s (Nat.+-monoʳ-≤ ⌊ n /2⌋ (Nat.⌊n/2⌋-mono (Nat.n≤1+n n)))) ⟩
                (1 + 1) + (⌊ n /2⌋ + ⌈ n /2⌉)
              ≡⟨ Eq.cong (λ e → (1 + 1) + e) (Nat.⌊n/2⌋+⌈n/2⌉≡n n) ⟩
                2+ n
              ∎
              where
                arithmetic : (a b c d : ℕ) → (a + b) + (c + d) ≡ (a + c) + (b + d)
                arithmetic a b c d = 
                  let open ≡-Reasoning in
                  begin
                    (a + b) + (c + d)
                  ≡⟨ Nat.+-assoc a b (c + d) ⟩
                    a + (b + (c + d))
                  ≡⟨ Eq.cong (λ e → a + e) (Nat.+-assoc b c d) ⟨
                    a + ((b + c) + d)
                  ≡⟨ Eq.cong (λ e → a + (e + d)) (Nat.+-comm b c) ⟩
                    a + ((c + b) + d)
                  ≡⟨ Eq.cong (λ e → a + e) (Nat.+-assoc c b d) ⟩
                    a + (c + (b + d))
                  ≡⟨ Nat.+-assoc a c (b + d) ⟨
                    (a + c) + (b + d)
                  ∎

rank/recon : (t₁ t₂ : Tree) (anc : List Context) → tree-size t₁ ≡ tree-size t₂ → rank (reconstruct t₁ anc) ≡ rank (reconstruct t₂ anc)
rank/recon t₁ t₂ [] st₁≡st₂ = Eq.cong (λ e → ⌊log₂ e ⌋) st₁≡st₂
rank/recon t₁ t₂ (Left k t ∷ anc) st₁≡st₂ = rank/recon (node t₁ k t) (node t₂ k t) anc 
  (Eq.cong (λ e → e + 1 + tree-size t) st₁≡st₂)
rank/recon t₁ t₂ (Right t k ∷ anc) st₁≡st₂ = rank/recon (node t k t₁) (node t k t₂) anc 
  (Eq.cong (λ e → tree-size t + 1 + e) st₁≡st₂)

φ : cmp (Π tree λ _ → F (list nat))
φ t = step (F _) (sum-of-ranks t) (ret (inord t))

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

instance
  node-size-nonzero : ∀ {a z b} → NonZero (tree-size (node a z b))
  node-size-nonzero {a} {z} {b} = >-nonZero (size>0 a z b)

sum-ranks+1/lemma : (t₁ t₂ : Tree) (anc : List Context) → tree-size t₁ ≡ tree-size t₂ → sum-of-ranks t₁ + 1 Nat.≤ sum-of-ranks t₂ →
    sum-of-ranks (reconstruct t₁ anc) + 1
  Nat.≤ 
    sum-of-ranks (reconstruct t₂ anc)
sum-ranks+1/lemma t₁ t₂ [] size ranks = ranks
sum-ranks+1/lemma t₁ t₂ (Left k t ∷ anc) size ranks = sum-ranks+1/lemma (node t₁ k t) (node t₂ k t) anc 
  (Eq.cong (λ e → e + 1 + tree-size t) size)
  (let open Nat.≤-Reasoning in
  begin
    sum-of-ranks t₁ + rank (node t₁ k t) + sum-of-ranks t + 1
  ≡⟨ arithmetic (sum-of-ranks t₁) (rank (node t₁ k t)) (sum-of-ranks t) 1 ⟩
    (sum-of-ranks t₁ + 1) + rank (node t₁ k t) + sum-of-ranks t
  ≤⟨ +-monoˡ-≤ (sum-of-ranks t) (+-monoˡ-≤ (rank (node t₁ k t)) ranks) ⟩
    sum-of-ranks t₂ + rank (node t₁ k t) + sum-of-ranks t
  ≡⟨ Eq.cong (λ e → sum-of-ranks t₂ + e + sum-of-ranks t) 
      (Eq.cong (λ e → ⌊log₂ (e + 1 + tree-size t) ⌋) size) ⟩
    sum-of-ranks t₂ + rank (node t₂ k t) + sum-of-ranks t
  ∎)
  where 
    arithmetic : (a b c d : val nat) → a + b + c + d ≡ (a + d) + b + c
    arithmetic = solve-∀
sum-ranks+1/lemma t₁ t₂ (Right t k ∷ anc) size ranks = sum-ranks+1/lemma (node t k t₁) (node t k t₂) anc 
  (Eq.cong (λ e → tree-size t + 1 + e) size)
  (let open Nat.≤-Reasoning in
  begin
    sum-of-ranks t + rank (node t k t₁) + sum-of-ranks t₁ + 1
  ≡⟨ arithmetic (sum-of-ranks t) (rank (node t k t₁)) (sum-of-ranks t₁) 1 ⟩
    sum-of-ranks t + rank (node t k t₁) + (sum-of-ranks t₁ + 1)
  ≤⟨ +-monoʳ-≤ (sum-of-ranks t + rank (node t k t₁)) ranks ⟩
    sum-of-ranks t + rank (node t k t₁) + sum-of-ranks t₂
  ≡⟨ Eq.cong (λ e → sum-of-ranks t + e + sum-of-ranks t₂) 
      (Eq.cong (λ e → ⌊log₂ (tree-size t + 1 + e) ⌋) size) ⟩
    sum-of-ranks t + rank (node t k t₂) + sum-of-ranks t₂
  ∎) 
  where
    arithmetic : (a b c d : val nat) → a + b + c + d ≡ a + b + (c + d)
    arithmetic = solve-∀

sum-ranks+x/lemma : (t₁ t₂ : Tree) (anc : List Context) (x : val nat) → tree-size t₁ ≡ tree-size t₂ → sum-of-ranks t₁ Nat.≤ x + sum-of-ranks t₂ →
    sum-of-ranks (reconstruct t₁ anc)
  Nat.≤ 
    x + sum-of-ranks (reconstruct t₂ anc)
sum-ranks+x/lemma t₁ t₂ [] x sizet₁≡sizet₂ rank+t₁≤xrank+t₂ = rank+t₁≤xrank+t₂
sum-ranks+x/lemma t₁ t₂ (Left k t ∷ anc) x sizet₁≡sizet₂ rank+t₁≤xrank+t₂ = sum-ranks+x/lemma (node t₁ k t) (node t₂ k t) anc x 
  (Eq.cong (λ e → e + 1 + tree-size t) (sizet₁≡sizet₂)) 
  (let open Nat.≤-Reasoning in
  begin
    sum-of-ranks t₁ + rank (node t₁ k t) + sum-of-ranks t
  ≡⟨ Eq.cong (λ e → sum-of-ranks t₁ + (⌊log₂ (e + 1 + tree-size t) ⌋) + sum-of-ranks t) sizet₁≡sizet₂ ⟩
    sum-of-ranks t₁ + rank (node t₂ k t) + sum-of-ranks t
  ≤⟨ +-monoˡ-≤ (sum-of-ranks t) (+-monoˡ-≤ (rank (node t₂ k t)) rank+t₁≤xrank+t₂) ⟩
    (x + sum-of-ranks t₂) + rank (node t₂ k t) + sum-of-ranks t
  ≡⟨ Eq.cong (λ e → e + sum-of-ranks t) (Nat.+-assoc x (sum-of-ranks t₂) (rank (node t₂ k t))) ⟩
    x + (sum-of-ranks t₂ + rank (node t₂ k t)) + sum-of-ranks t
  ≡⟨ Nat.+-assoc x (sum-of-ranks t₂ + rank (node t₂ k t)) (sum-of-ranks t) ⟩
    x + (sum-of-ranks t₂ + rank (node t₂ k t) + sum-of-ranks t)
  ∎)
sum-ranks+x/lemma t₁ t₂ (Right t k ∷ anc) x sizet₁≡sizet₂ rank+t₁≤xrank+t₂ = sum-ranks+x/lemma (node t k t₁) (node t k t₂) anc x 
  (Eq.cong (λ e → tree-size t + 1 + e) (sizet₁≡sizet₂)) 
  (let open Nat.≤-Reasoning in
  begin
    sum-of-ranks t + rank (node t k t₁) + sum-of-ranks t₁
  ≡⟨ Eq.cong (λ e → sum-of-ranks t + ⌊log₂ (tree-size t + 1 + e) ⌋ + sum-of-ranks t₁) sizet₁≡sizet₂ ⟩
    sum-of-ranks t + rank (node t k t₂) + sum-of-ranks t₁
  ≤⟨ +-monoʳ-≤ (sum-of-ranks t + rank (node t k t₂)) rank+t₁≤xrank+t₂ ⟩
    sum-of-ranks t + rank (node t k t₂) + (x + sum-of-ranks t₂)
  ≡⟨ arithmetic (sum-of-ranks t) (rank (node t k t₂)) x (sum-of-ranks t₂) ⟩
    x + (sum-of-ranks t + rank (node t k t₂) + sum-of-ranks t₂)
  ∎)
  where
    arithmetic : (a b c d : val nat) → a + b + (c + d) ≡ c + (a + b + d)
    arithmetic = solve-∀

splay'/amortized : (l : Tree) (r : Tree) (anc : List Context) (k : val nat) → 
   bind (F _) (splay' l r anc k) (λ ((l' , r') , _) → φ (node l' k r')) 
  ≤⁻[ F _ ] 
   step (F _) (1 + 3 * (rank (reconstruct (node l k r) anc) ∸ rank (node l k r))) (φ (reconstruct (node l k r) anc))
splay'/amortized a b [] k = step-monoˡ-≤⁻ {c' = 1 + 3 * (rank (reconstruct (node a k b) []) ∸ rank (node a k b))} (φ (node a k b)) z≤n 
-- done
splay'/amortized a b (Left p c ∷ []) k = 
  let
    rank-x  : val nat
    rank-x  = rank (node a k b)
    rank-y  : val nat
    rank-y  = rank (node (node a k b) p c)
    rank-x' : val nat
    rank-x' = rank (node a k (node b p c))
    rank-y' : val nat
    rank-y' = rank (node b p c)
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
    step (F _) 1 (step (F _) (sum-of-ranks (node a k (node b p c))) (ret (inord (node (node a k b) p c))))
  ≡⟨⟩ 
    step (F _) (1 + sum-of-ranks (node a k (node b p c))) (ret (inord (node (node a k b) p c)))
  ≡⟨⟩  
    step (F _) (1 + sum-of-ranks a + rank-x' + (sum-of-ranks b + rank-y' + sum-of-ranks c))
      (ret (inord (node (node a k b) p c)))
  ≡⟨ Eq.cong (λ e → step (F _) e (ret (inord (node (node a k b) p c)))) 
      (arithmetic3 1 (sum-of-ranks a) rank-x' (sum-of-ranks b) rank-y' (sum-of-ranks c)) ⟩
    step (F _) ((1 + sum-of-ranks a + sum-of-ranks b + sum-of-ranks c) + (rank-x' + rank-y'))
      (ret (inord (node (node a k b) p c)))
  ≲⟨ step-monoˡ-≤⁻ (ret (inord (node (node a k b) p c))) 
      (+-monoʳ-≤ (1 + sum-of-ranks a + sum-of-ranks b + sum-of-ranks c) 
        (+-mono-≤ (rank/ordering a b c k p) (rank/containment1 a b c k p))) ⟩
    step (F _) ((1 + sum-of-ranks a + sum-of-ranks b + sum-of-ranks c) + (rank-y + rank-y))
      (ret (inord (node (node a k b) p c)))
  ≡⟨ Eq.cong (λ e → step (F _) ((1 + sum-of-ranks a + sum-of-ranks b + sum-of-ranks c) + e) (ret (inord (node (node a k b) p c)))) 
      (Nat.m+n∸n≡m (rank-y + rank-y) (rank-y ∸ rank-x)) ⟨
    step (F _) ((1 + sum-of-ranks a + sum-of-ranks b + sum-of-ranks c) + 
      ((rank-y + rank-y) + (rank-y ∸ rank-x) ∸ (rank-y ∸ rank-x)))
        (ret (inord (node (node a k b) p c)))
  ≡⟨ Eq.cong (λ e → step (F _) ((1 + sum-of-ranks a + sum-of-ranks b + sum-of-ranks c) + e) (ret (inord (node (node a k b) p c)))) 
      (arithmetic1 rank-y rank-x (rank/containment2 a b c k p)) ⟩
    step (F _) ((1 + sum-of-ranks a + sum-of-ranks b + sum-of-ranks c) +
      ((rank-y + rank-x) + (rank-y ∸ rank-x)))
        (ret (inord (node (node a k b) p c)))
  ≲⟨ step-monoˡ-≤⁻ (ret (inord (node (node a k b) p c))) 
      (+-monoʳ-≤ (1 + sum-of-ranks a + sum-of-ranks b + sum-of-ranks c) 
        (+-mono-≤ ≤-refl (Nat.m≤n*m (rank-y ∸ rank-x) 3)) ) ⟩
    step (F _) ((1 + sum-of-ranks a + sum-of-ranks b + sum-of-ranks c) + 
      ((rank-y + rank-x) + 3 * (rank-y ∸ rank-x)))
        (ret (inord (node (node a k b) p c)))
  ≡⟨ Eq.cong (λ e → step (F _) e (ret (inord (node (node a k b) p c)))) 
      (arithmetic2 1 (sum-of-ranks a) (sum-of-ranks b) (sum-of-ranks c) rank-y rank-x (3 * (rank-y ∸ rank-x))) ⟩
    step (F _) (1 + 3 * (rank-y ∸ rank-x) + ((sum-of-ranks a + rank-x + sum-of-ranks b) + rank-y + sum-of-ranks c))
      (ret (inord (node (node a k b) p c))) 
  ≡⟨⟩
    step (F _) (1 + 3 * (rank-y ∸ rank-x) + sum-of-ranks (node (node a k b) p c)) (ret (inord (node (node a k b) p c)))
  ≡⟨⟩
    step (F _) (1 + 3 * (rank-y ∸ rank-x)) (step (F _) (sum-of-ranks (node (node a k b) p c)) (ret (inord (node (node a k b) p c))))
  ≡⟨⟩
    step (F _) (1 + 3 * (rank-y ∸ rank-x)) (φ (node (node a k b) p c))
  ∎
  where
    rank/ordering : (a b c : Tree) (k p : val nat) → rank (node a k (node b p c)) Nat.≤ rank (node (node a k b) p c)
    rank/ordering a b c k p = 
      let open Nat.≤-Reasoning in 
      begin
        rank (node a k (node b p c))
      ≡⟨⟩
        ⌊log₂ ((tree-size a + 1) + ((tree-size b + 1) + tree-size c)) ⌋
      ≡⟨ Eq.cong (λ e → ⌊log₂ e ⌋) (+-assoc (tree-size a + 1) (tree-size b + 1) (tree-size c)) ⟨
        ⌊log₂ (((tree-size a + 1) + (tree-size b + 1)) + (tree-size c)) ⌋ 
      ≡⟨ Eq.cong (λ e → ⌊log₂ (e + tree-size c) ⌋) (+-assoc (tree-size a + 1) (tree-size b) 1) ⟨
        ⌊log₂ (((tree-size a + 1 + tree-size b) + 1) + (tree-size c)) ⌋
      ≡⟨ Eq.cong (λ e → ⌊log₂ e ⌋) (+-assoc (tree-size a + 1 + tree-size b) 1 (tree-size c)) ⟩
        ⌊log₂ ((tree-size a + 1 + tree-size b) + (1 + tree-size c)) ⌋
      ≡⟨ Eq.cong (λ e → ⌊log₂ e ⌋) (+-assoc (tree-size a + 1 + tree-size b) 1 (tree-size c)) ⟨
        ⌊log₂ ((tree-size a + 1 + tree-size b) + 1 + tree-size c) ⌋
      ≡⟨⟩
        rank (node (node a k b) p c)
      ∎
    rank/containment1 : (a b c : Tree) (k p : val nat) → rank (node b p c) Nat.≤ rank (node (node a k b) p c)
    rank/containment1 a b c k p = 
      let open Nat.≤-Reasoning in 
      begin
        rank (node b p c)
      ≡⟨⟩
        ⌊log₂ (tree-size b + 1 + tree-size c) ⌋
      ≤⟨ ⌊log₂⌋-mono-≤ (Nat.m≤n+m (tree-size b + 1 + tree-size c) (tree-size a + 1)) ⟩
        ⌊log₂ ((tree-size a + 1) + ((tree-size b + 1) + tree-size c)) ⌋
      ≡⟨ Eq.cong (λ e → ⌊log₂ e ⌋) (+-assoc (tree-size a + 1) (tree-size b + 1) (tree-size c)) ⟨
        ⌊log₂ ((tree-size a + 1 + (tree-size b + 1)) + tree-size c) ⌋
      ≡⟨ Eq.cong (λ e → ⌊log₂ (e + tree-size c) ⌋) (+-assoc (tree-size a + 1) (tree-size b) 1) ⟨
        ⌊log₂ (((tree-size a + 1) + tree-size b) + 1 + tree-size c) ⌋
      ≡⟨⟩
        rank (node (node a k b) p c)
      ∎
    rank/containment2 : (a b c : Tree) (k p : val nat) → rank (node a k b) Nat.≤ rank (node (node a k b) p c)
    rank/containment2 a b c k p = 
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
    arithmetic1 : (a b : val nat) → b Nat.≤ a → (a + a) + (a ∸ b) ∸ (a ∸ b) ≡ (a + b) + (a ∸ b)
    arithmetic1 a b p = 
      let open ≡-Reasoning in 
      begin
        (a + a) + (a ∸ b) ∸ (a ∸ b)
      ≡⟨ Nat.m+n∸n≡m (a + a) (a ∸ b) ⟩
        a + a
      ≡⟨ Nat.m+n∸n≡m (a + a) b ⟨
        ((a + a) + b) ∸ b
      ≡⟨ Eq.cong (λ e → e ∸ b) (+-assoc a a b) ⟩
        (a + (a + b)) ∸ b
      ≡⟨ Eq.cong (λ e → (a + e) ∸ b) (Nat.+-comm a b) ⟩
        (a + (b + a)) ∸ b
      ≡⟨ Eq.cong (λ e → e ∸ b) (+-assoc a b a) ⟨
        ((a + b) + a) ∸ b
      ≡⟨ Nat.+-∸-assoc (a + b) p ⟩
        (a + b) + (a ∸ b)
      ∎
    arithmetic2 : (a b c d e f g : val nat) → (a + b + c + d) + ((e + f) + g) ≡ a + g + ((b + f + c) + e + d)
    arithmetic2 = solve-∀
    arithmetic3 : (a b c d e f : val nat) → a + b + c + (d + e + f) ≡ (a + b + d + f) + (c + e)
    arithmetic3 = solve-∀
-- zig
splay'/amortized b c (Right a p ∷ []) k = {!   !}
-- zag
splay'/amortized a b (Left p c ∷ Left g d ∷ anc) k with <-cmp (rank (node a k b)) (rank (node a k (node b p (node c g d))))
... | tri< rank-x<rank-x' ¬b ¬c  = let
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
    size-arith2 t₁ t₂ [] t₁≡t₂ = ≤-reflexive (Eq.cong (λ e → ⌊log₂ e ⌋) t₁≡t₂)
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
    arithmetic2 a b c d a≤c =  
      let open ≡-Reasoning in
      begin
        a + a + b + ((c ∸ a) + d)
      ≡⟨ Eq.cong (λ e → a + a + b + e) (Nat.+-∸-comm d a≤c) ⟨ 
        (((a + a) + b) + ((c + d) ∸ a))
      ≡⟨ Nat.+-assoc (a + a) b ((c + d) ∸ a) ⟩
        a + a + (b + ((c + d) ∸ a))
      ≡⟨ Eq.cong (λ e → a + a + e) (Nat.+-∸-assoc b (≤-trans a≤c (Nat.m≤m+n c d))) ⟨
        a + a + ((b + (c + d)) ∸ a)
      ≡⟨ Eq.cong (λ e → a + a + (e ∸ a)) (Nat.+-assoc b c d) ⟨ 
        a + a + (((b + c) + d) ∸ a)
      ≡⟨ Nat.+-assoc a a (((b + c) + d) ∸ a) ⟩
        a + (a + (((b + c) + d) ∸ a))
      ≡⟨ Eq.cong (λ e → a + e) (Nat.+-∸-assoc a 
          (≤-trans a≤c (≤-trans (Nat.m≤n+m c b) (Nat.m≤m+n (b + c) d)))) ⟨ 
        a + ((a + ((b + c) + d)) ∸ a)
      ≡⟨ Eq.cong (λ e → a + (e ∸ a)) (Nat.+-comm a ((b + c) + d)) ⟩
        a + ((((b + c) + d) + a) ∸ a)
      ≡⟨ Eq.cong (λ e → a + e) (Nat.+-∸-assoc ((b + c) + d) {a} {a} ≤-refl) ⟩
        a + (((b + c) + d) + (a ∸ a))
      ≡⟨ Eq.cong (λ e → a + e) (Nat.+-comm ((b + c) + d) (a ∸ a)) ⟩
        a + ((a ∸ a) + ((b + c) + d))
      ≡⟨ Nat.+-assoc a (a ∸ a) ((b + c) + d) ⟨
        a + (a ∸ a) + ((b + c) + d)
      ≡⟨ Eq.cong (λ e → e + ((b + c) + d)) (Nat.+-comm a (a ∸ a)) ⟩
        (a ∸ a) + a + ((b + c) + d)
      ≡⟨ Nat.+-assoc ((a ∸ a) + a) (b + c) d ⟨
        (a ∸ a) + a + (b + c) + d
      ∎
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
      ≡⟨ Eq.cong (λ e → 3 * (e ∸ c)) (Nat.+-∸-assoc a {b} {b} ≤-refl) ⟩ 
        3 * ((a + (b ∸ b)) ∸ c)
      ≡⟨ Eq.cong (λ e → 3 * ((a + e) ∸ c)) (Nat.n∸n≡0 b) ⟩
        3 * ((a + 0) ∸ c)
      ≡⟨ Eq.cong (λ e → 3 * (e ∸ c)) (Nat.+-comm a 0) ⟩
        3 * (a ∸ c) 
      ∎
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
      ≤⟨ +-mono-≤ (+-mono-≤ (+-monoʳ-≤ (sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) ≤-refl) rank-y'≤rank-x') rank-z'≤rank-x' ⟩
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
          (+-mono-≤ (+-monoʳ-≤ (sum-of-ranks a + sum-of-ranks b + sum-of-ranks c + sum-of-ranks d) (≤-trans rank-x<rank-x' (≤-reflexive rank-x'≡rank-z))) 
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
        rank-arithmetic1 = solve-∀
        rank-arithmetic2 : (a b c d e f g h : val nat) → (a + b + c + d) + e + f + g + h ≡ h + (a + g + b + f + c + e + d)
        rank-arithmetic2 = solve-∀
        rank-y'≤rank-x' : rank (node b p (node c g d)) Nat.≤ rank (node a k (node b p (node c g d)))
        rank-y'≤rank-x' = ⌊log₂⌋-mono-≤ (Nat.m≤n+m (tree-size b + 1 + (tree-size c + 1 + tree-size d)) (tree-size a + 1))
        rank-z'≤rank-x' : rank (node c g d) Nat.≤ rank (node a k (node b p (node c g d)))
        rank-z'≤rank-x' = ≤-trans (⌊log₂⌋-mono-≤ (Nat.m≤n+m (tree-size c + 1 + tree-size d) (tree-size b + 1))) rank-y'≤rank-x'
        rank-x'≡rank-z : rank (node a k (node b p (node c g d))) ≡ rank (node (node (node a k b) p c) g d)
        rank-x'≡rank-z = Eq.cong (λ e → ⌊log₂ e ⌋) size/lemma
        rank-x≤rank-y : rank (node a k b) Nat.≤ rank (node (node a k b) p c)
        rank-x≤rank-y = ≤-trans (⌊log₂⌋-mono-≤ (Nat.m≤m+n (tree-size a + 1 + tree-size b) (1 + tree-size c))) 
          (≤-reflexive (Eq.cong (λ e → ⌊log₂ e ⌋) (Eq.sym (+-assoc (tree-size a + 1 + tree-size b) 1 (tree-size c)))))
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
            arithmetic = solve-∀ 
        rank≡ : (a b c : val nat) → c < b → 1 Nat.≤ b → 
          a + b + b + b + (3 * (c ∸ c)) ≡ a + (1 + c) + c + c + ((3 * (b ∸ c)) ∸ 1)
        rank≡ a b c c<b 1≤b = 
          let open ≡-Reasoning in
          begin
            a + b + b + b + (3 * (c ∸ c))
          ≡⟨ Eq.cong (λ e → e + (3 * (c ∸ c))) (Nat.+-assoc (a + b) b b) ⟩
            a + b + (b + b) + (3 * (c ∸ c))
          ≡⟨ Eq.cong (λ e → e + (3 * (c ∸ c))) (Nat.+-assoc a b (b + b)) ⟩
            a + (b + (b + b)) + (3 * (c ∸ c))
          ≡⟨ Eq.cong (λ e → a + e + (3 * (c ∸ c))) (Eq.cong (λ e → b + (b + e)) (Nat.+-identityʳ b)) ⟨
            a + (3 * b) + (3 * (c ∸ c))
          ≡⟨ Nat.+-assoc a (3 * b) (3 * (c ∸ c)) ⟩
            a + ((3 * b) + (3 * (c ∸ c)))
          ≡⟨ Eq.cong (λ e → a + e) (Nat.*-distribˡ-+ 3 b (c ∸ c)) ⟨
            a + (3 * (b + (c ∸ c)))
          ≡⟨ Eq.cong (λ e → a + (3 * e)) (Nat.+-∸-assoc b {c} {c} ≤-refl) ⟨
            a + (3 * ((b + c) ∸ c))
          ≡⟨ Eq.cong (λ e → a + (3 * (e ∸ c))) (Nat.+-comm b c) ⟩
            a + (3 * ((c + b) ∸ c))
          ≡⟨ Eq.cong (λ e → a + (3 * e)) (Nat.+-∸-assoc c {b} {c} (Nat.<⇒≤ c<b)) ⟩
            a + (3 * (c + (b ∸ c)))
          ≡⟨ Eq.cong (λ e → a + e) (Nat.+-identityʳ (3 * (c + (b ∸ c)))) ⟨
            a + ((3 * (c + (b ∸ c))) + (1 ∸ 1))
          ≡⟨ Eq.cong (λ e → a + e) (Nat.+-∸-assoc (3 * (c + (b ∸ c))) {1} {1} ≤-refl) ⟨ 
            a + (((3 * (c + (b ∸ c))) + 1) ∸ 1)
          ≡⟨ Eq.cong (λ e → a + (e ∸ 1)) (Nat.+-comm (3 * (c + (b ∸ c))) 1) ⟩
            a + ((1 + (3 * (c + (b ∸ c)))) ∸ 1)
          ≡⟨ Eq.cong (λ e → a + e) (Nat.+-∸-assoc 1 {3 * (c + (b ∸ c))} {1} 1≤arith1) ⟩
            a + (1 + ((3 * (c + (b ∸ c))) ∸ 1))
          ≡⟨ Nat.+-assoc a 1 ((3 * (c + (b ∸ c))) ∸ 1) ⟨
            a + 1 + ((3 * (c + (b ∸ c))) ∸ 1)
          ≡⟨ Eq.cong (λ e → a + 1 + (e ∸ 1)) (Nat.*-distribˡ-+ 3 c (b ∸ c)) ⟩
            a + 1 + (((3 * c) + (3 * (b ∸ c))) ∸ 1)
          ≡⟨ Eq.cong (λ e → a + 1 + e) (Nat.+-∸-assoc (3 * c) {3 * (b ∸ c)} {1} 1≤arith2) ⟩
            a + 1 + ((3 * c) + ((3 * (b ∸ c)) ∸ 1))
          ≡⟨ Nat.+-assoc (a + 1) (3 * c) ((3 * (b ∸ c)) ∸ 1) ⟨
            a + 1 + (3 * c) + ((3 * (b ∸ c)) ∸ 1)
          ≡⟨ Eq.cong (λ e → a + 1 + e + ((3 * (b ∸ c)) ∸ 1)) (Eq.cong (λ e → c + (c + e)) (Nat.+-identityʳ c)) ⟩
            a + 1 + (c + (c + c)) + ((3 * (b ∸ c)) ∸ 1)
          ≡⟨ Eq.cong (λ e → e + ((3 * (b ∸ c)) ∸ 1)) (Nat.+-assoc (a + 1) c (c + c)) ⟨
            a + 1 + c + (c + c) + ((3 * (b ∸ c)) ∸ 1)
          ≡⟨ Eq.cong (λ e → e + ((3 * (b ∸ c)) ∸ 1)) (Nat.+-assoc (a + 1 + c) c c) ⟨
            a + 1 + c + c + c + ((3 * (b ∸ c)) ∸ 1)
          ≡⟨ Eq.cong (λ e → e + c + c + ((3 * (b ∸ c)) ∸ 1)) (Nat.+-assoc a 1 c) ⟩
            a + (1 + c) + c + c + ((3 * (b ∸ c)) ∸ 1)
          ∎
          where
            1≤arith1 : 1 Nat.≤ 3 * (c + (b ∸ c))
            1≤arith1 = 
              let open Nat.≤-Reasoning in
              begin
                1
              ≤⟨ 1≤b ⟩
                b
              ≤⟨ Nat.m≤n*m b 3 ⟩
                3 * b
              ≡⟨ Eq.cong (λ e → 3 * e) (Nat.m+n∸m≡n c b) ⟨ 
                3 * (c + b ∸ c)
              ≡⟨ Eq.cong (λ e → 3 * e) (Nat.+-∸-assoc c {b} {c} (Nat.<⇒≤ c<b)) ⟩
                3 * (c + (b ∸ c))
              ∎
            1≤arith2 : 1 Nat.≤ 3 * (b ∸ c)
            1≤arith2 = 
              let open Nat.≤-Reasoning in
              begin
                1
              ≤⟨ Nat.m<n⇒0<n∸m c<b ⟩ 
                b ∸ c
              ≤⟨ Nat.m≤n*m (b ∸ c) 3 ⟩
                3 * (b ∸ c)
              ∎
    phi/lemma : 
        sum-of-ranks (reconstruct (node a k (node b p (node c g d))) anc)
      Nat.≤
        ((3 * (rank (node a k (node b p (node c g d))) ∸ rank (node a k b))) ∸ 1) + 
        sum-of-ranks (reconstruct (node (node (node a k b) p c) g d) anc)
    phi/lemma = sum-ranks+x/lemma (node a k (node b p (node c g d))) (node (node (node a k b) p c) g d) anc 
      ((3 * (rank (node a k (node b p (node c g d))) ∸ rank (node a k b))) ∸ 1) size/lemma rank/lemma
... | tri≈ ¬a rank-x≡rank-x'' ¬c = 
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
    arithmetic1 a b c = 
      let open ≡-Reasoning in
      begin
        a + a + b + c
      ≡⟨ Nat.+-assoc (a + a) b c ⟩
        a + a + (b + c)
      ≡⟨ Nat.+-assoc a a (b + c) ⟩
        a + (a + (b + c))
      ≡⟨ Eq.cong (λ e → a + e) (Nat.+-comm a (b + c)) ⟩
        a + ((b + c) + a)
      ≡⟨ Nat.+-assoc a (b + c) a ⟨
        a + (b + c) + a
      ≡⟨ Eq.cong (λ e → e + a) (Nat.+-assoc a b c) ⟨
        a + b + c + a
      ≡⟨ Nat.+-assoc (a + b) c a ⟩
        a + b + (c + a)
      ∎
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
          (≤-reflexive (Eq.sym (rank-x≡rank-x'')))) rank-y''≤rank-y) rank-z''<rank-z ⟩
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
        rank-arithmetic1 = solve-∀
        rank-arithmetic2 : (a b c d e f g : val nat) → (a + b + c + d) + e + f + g ≡ a + e + b + f + c + g + d
        rank-arithmetic2 = solve-∀
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
              ≤⟨ ≤-trans (⌊log₂⌋-mono-≤ (Nat.m≤m+n (((tree-size a + 1 + tree-size b) + 1 + tree-size c)) (1 + tree-size d))) 
                  (≤-reflexive (Eq.cong (λ e → ⌊log₂ e ⌋) (Eq.sym (Nat.+-assoc ((tree-size a + 1 + tree-size b) + 1 + tree-size c) 1 (tree-size d))))) ⟩
                rank (node (node (node a k b) p c) g d)
              ≡⟨ Eq.cong (λ e → ⌊log₂ e ⌋) size/lemma ⟨
                rank (node a k (node b p (node c g d)))  
              ≡⟨ rank-x≡rank-x'' ⟨
                rank (node a k b)
              ∎
            rank-x≤rank-y : rank (node a k b) Nat.≤ rank (node (node a k b) p c)
            rank-x≤rank-y = ≤-trans (⌊log₂⌋-mono-≤ (Nat.m≤m+n (tree-size a + 1 + tree-size b) (1 + tree-size c))) 
              (≤-reflexive (Eq.cong (λ e → ⌊log₂ e ⌋) (Eq.sym (Nat.+-assoc (tree-size a + 1 + tree-size b) 1 (tree-size c)))))
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
... | tri> ¬a ¬b rank-x>rank-x'  = ⊥-elim (Nat.≤⇒≯ rank-x≤rank-x' rank-x>rank-x')
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
        arithmetic = solve-∀
-- zig-zig
splay'/amortized b c (Left p d ∷ Right a g ∷ anc) k = {!   !}
-- zag-zig
splay'/amortized b c (Right a p ∷ Left g d ∷ anc) k with <-cmp (rank (node b k c)) (rank (node (node a p b) k (node c g d)))
... | tri< rank-x<rank-x' ¬b ¬c = 
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
    arithmetic1 = solve-∀
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
        arithmetic = solve-∀
    size-arith2 : (t₁ t₂ : Tree) (anc : List Context) → tree-size t₁ ≡ tree-size t₂ → 
      rank t₁ Nat.≤ rank (reconstruct t₂ anc)
    size-arith2 t₁ t₂ [] t₁≡t₂ = ≤-reflexive (Eq.cong (λ e → ⌊log₂ e ⌋) t₁≡t₂)
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
    arithmetic2 a b c d a≤c =  
      let open ≡-Reasoning in
      begin
        a + a + b + ((c ∸ a) + d)
      ≡⟨ Eq.cong (λ e → a + a + b + e) (Nat.+-∸-comm d a≤c) ⟨ 
        (((a + a) + b) + ((c + d) ∸ a))
      ≡⟨ Nat.+-assoc (a + a) b ((c + d) ∸ a) ⟩
        a + a + (b + ((c + d) ∸ a))
      ≡⟨ Eq.cong (λ e → a + a + e) (Nat.+-∸-assoc b (≤-trans a≤c (Nat.m≤m+n c d))) ⟨
        a + a + ((b + (c + d)) ∸ a)
      ≡⟨ Eq.cong (λ e → a + a + (e ∸ a)) (Nat.+-assoc b c d) ⟨ 
        a + a + (((b + c) + d) ∸ a)
      ≡⟨ Nat.+-assoc a a (((b + c) + d) ∸ a) ⟩
        a + (a + (((b + c) + d) ∸ a))
      ≡⟨ Eq.cong (λ e → a + e) (Nat.+-∸-assoc a 
          (≤-trans a≤c (≤-trans (Nat.m≤n+m c b) (Nat.m≤m+n (b + c) d)))) ⟨ 
        a + ((a + ((b + c) + d)) ∸ a)
      ≡⟨ Eq.cong (λ e → a + (e ∸ a)) (Nat.+-comm a ((b + c) + d)) ⟩
        a + ((((b + c) + d) + a) ∸ a)
      ≡⟨ Eq.cong (λ e → a + e) (Nat.+-∸-assoc ((b + c) + d) {a} {a} ≤-refl) ⟩
        a + (((b + c) + d) + (a ∸ a))
      ≡⟨ Eq.cong (λ e → a + e) (Nat.+-comm ((b + c) + d) (a ∸ a)) ⟩
        a + ((a ∸ a) + ((b + c) + d))
      ≡⟨ Nat.+-assoc a (a ∸ a) ((b + c) + d) ⟨
        a + (a ∸ a) + ((b + c) + d)
      ≡⟨ Eq.cong (λ e → e + ((b + c) + d)) (Nat.+-comm a (a ∸ a)) ⟩
        (a ∸ a) + a + ((b + c) + d)
      ≡⟨ Nat.+-assoc ((a ∸ a) + a) (b + c) d ⟨
        (a ∸ a) + a + (b + c) + d
      ∎
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
      ≡⟨ Eq.cong (λ e → 3 * (e ∸ c)) (Nat.+-∸-assoc a {b} {b} ≤-refl) ⟩ 
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
              (≤-trans rank-x<rank-x' rank-x'≤rank-z)))) ⟩
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
        rank-arithmetic1 = solve-∀
        rank-arithmetic2 : (a b c d e f g h : val nat) → (a + c + e + g) + f + b + d + h ≡ h + (a + b + (c + d + e) + f + g)
        rank-arithmetic2 = solve-∀
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
            arithmetic = solve-∀
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
            arithmetic = solve-∀
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
        rank-x'≤rank-z = ≤-reflexive rank-x'-z
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
            arithmetic = solve-∀
        rank≤ : (a b c d : val nat) → d < c → 1 Nat.≤ c → 
          a + b + c + c + (2 * (d ∸ d)) Nat.≤ a + (1 + d) + b + d + ((3 * (c ∸ d)) ∸ 1)
        rank≤ a b c d d<c 1≤c = 
          let open Nat.≤-Reasoning in
          begin
            a + b + c + c + (2 * (d ∸ d))
          ≡⟨ Eq.cong (λ e → e + (2 * (d ∸ d))) (Nat.+-assoc (a + b) c c) ⟩
           a + b + (c + c) + (2 * (d ∸ d))
          ≡⟨ Eq.cong (λ e → a + b + e + (2 * (d ∸ d))) (Eq.cong (λ e → c + e) (Nat.+-identityʳ c)) ⟨
            a + b + (2 * c) + (2 * (d ∸ d)) 
          ≡⟨ Nat.+-assoc (a + b) (2 * c) (2 * (d ∸ d)) ⟩
            a + b + ((2 * c) + (2 * (d ∸ d)))
          ≡⟨ Eq.cong (λ e → a + b + e) (Nat.*-distribˡ-+ 2 c (d ∸ d)) ⟨
            a + b + (2 * (c + (d ∸ d)))
          ≡⟨ Eq.cong (λ e → a + b + (2 * e)) (Nat.+-∸-assoc c {d} {d} ≤-refl) ⟨
            a + b + (2 * ((c + d) ∸ d))
          ≡⟨ Eq.cong (λ e → a + b + (2 * (e ∸ d))) (Nat.+-comm c d) ⟩
            a + b + (2 * ((d + c) ∸ d))
          ≡⟨ Eq.cong (λ e → a + b + (2 * e)) (Nat.+-∸-assoc d {c} {d} (Nat.<⇒≤ d<c)) ⟩
            a + b + (2 * (d + (c ∸ d)))
          ≡⟨ Eq.cong (λ e → a + b + e) (Nat.+-identityʳ (2 * (d + (c ∸ d)))) ⟨
            a + b + ((2 * (d + (c ∸ d))) + (1 ∸ 1))
          ≡⟨ Eq.cong (λ e → a + b + e) (Nat.+-∸-assoc (2 * (d + (c ∸ d))) {1} {1} ≤-refl) ⟨
            a + b + (((2 * (d + (c ∸ d))) + 1) ∸ 1)
          ≡⟨ Eq.cong (λ e → a + b + (e ∸ 1)) (Nat.+-comm (2 * (d + (c ∸ d))) 1) ⟩
            a + b + ((1 + (2 * (d + (c ∸ d)))) ∸ 1)
          ≡⟨ Eq.cong (λ e → a + b + e) (Nat.+-∸-assoc 1 {2 * (d + (c ∸ d))} {1} 1≤arith1) ⟩
            a + b + (1 + ((2 * (d + (c ∸ d))) ∸ 1))
          ≡⟨ Nat.+-assoc (a + b) 1 ((2 * (d + (c ∸ d))) ∸ 1) ⟨
            a + b + 1 + ((2 * (d + (c ∸ d))) ∸ 1)
          ≡⟨ Eq.cong (λ e → a + b + 1 + (e ∸ 1)) (Nat.*-distribˡ-+ 2 d (c ∸ d)) ⟩
            a + b + 1 + (((2 * d) + (2 * (c ∸ d))) ∸ 1)
          ≡⟨ Eq.cong (λ e → a + b + 1 + e) (Nat.+-∸-assoc (2 * d) {2 * (c ∸ d)} {1} 1≤arith2) ⟩
            a + b + 1 + ((2 * d) + ((2 * (c ∸ d)) ∸ 1))
          ≡⟨ Nat.+-assoc (a + b + 1) (2 * d) ((2 * (c ∸ d)) ∸ 1) ⟨
            a + b + 1 + (2 * d) + ((2 * (c ∸ d)) ∸ 1)
          ≡⟨ Eq.cong (λ e → a + b + 1 + e + ((2 * (c ∸ d)) ∸ 1)) 
              (Eq.cong (λ e → d + e) (Nat.+-identityʳ d)) ⟩
            a + b + 1 + (d + d) + ((2 * (c ∸ d)) ∸ 1)
          ≡⟨ Eq.cong (λ e → e + ((2 * (c ∸ d)) ∸ 1)) (Nat.+-assoc (a + b + 1) d d) ⟨
            a + b + 1 + d + d + ((2 * (c ∸ d)) ∸ 1)
          ≡⟨ Eq.cong (λ e → e + d + ((2 * (c ∸ d)) ∸ 1)) (Nat.+-assoc (a + b) 1 d) ⟩
            a + b + (1 + d) + d + ((2 * (c ∸ d)) ∸ 1)
          ≡⟨ Eq.cong (λ e → e + d + ((2 * (c ∸ d)) ∸ 1)) (Nat.+-assoc a b (1 + d)) ⟩
            a + (b + (1 + d)) + d + ((2 * (c ∸ d)) ∸ 1)
          ≡⟨ Eq.cong (λ e → a + e + d + ((2 * (c ∸ d)) ∸ 1)) (Nat.+-comm b (1 + d)) ⟩
            a + ((1 + d) + b) + d + ((2 * (c ∸ d)) ∸ 1)
          ≡⟨ Eq.cong (λ e → e + d + ((2 * (c ∸ d)) ∸ 1)) (Nat.+-assoc a (1 + d) b) ⟨
            a + (1 + d) + b + d + ((2 * (c ∸ d)) ∸ 1)
          ≤⟨ +-monoʳ-≤ (a + (1 + d) + b + d) 
              (Nat.∸-monoˡ-≤ 1 (Nat.*-monoˡ-≤ (c ∸ d) {2} {3} (s≤s (s≤s z≤n)))) ⟩
            a + (1 + d) + b + d + ((3 * (c ∸ d)) ∸ 1)
          ∎
          where
            1≤arith1 : 1 Nat.≤ 2 * (d + (c ∸ d))
            1≤arith1 = 
              let open Nat.≤-Reasoning in
              begin
                1
              ≤⟨ 1≤c ⟩
                c
              ≤⟨ Nat.m≤n*m c 2 ⟩
                2 * c
              ≡⟨ Eq.cong (λ e → 2 * e) (Nat.m+n∸m≡n d c) ⟨ 
                2 * (d + c ∸ d)
              ≡⟨ Eq.cong (λ e → 2 * e) (Nat.+-∸-assoc d {c} {d} (Nat.<⇒≤ d<c)) ⟩
                2 * (d + (c ∸ d))
              ∎
            1≤arith2 : 1 Nat.≤ 2 * (c ∸ d)
            1≤arith2 = 
              let open Nat.≤-Reasoning in
              begin
                1
              ≤⟨ Nat.m<n⇒0<n∸m d<c ⟩ 
                c ∸ d
              ≤⟨ Nat.m≤n*m (c ∸ d) 2 ⟩
                2 * (c ∸ d)
              ∎
    phi/lemma : 
        sum-of-ranks (reconstruct (node (node a p b) k (node c g d)) anc)
      Nat.≤
        ((3 * (rank (node (node a p b) k (node c g d)) ∸ rank (node b k c))) ∸ 1) + 
        sum-of-ranks (reconstruct (node (node a p (node b k c)) g d) anc)
    phi/lemma = sum-ranks+x/lemma (node (node a p b) k (node c g d)) (node (node a p (node b k c)) g d) 
      anc ((3 * (rank (node (node a p b) k (node c g d)) ∸ rank (node b k c))) ∸ 1) size/lemma rank/lemma
... | tri≈ ¬a rank-x≡rank-x' ¬c = 
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
    arithmetic1 = solve-∀
    size/lemma : tree-size (node (node a p b) k (node c g d)) ≡ tree-size (node (node a p (node b k c)) g d)
    size/lemma = arithmetic1 (tree-size a) 1 (tree-size b) 1 (tree-size c) 1 (tree-size d)
    arithmetic2 : (a b c d : val nat) → a + b + c + d ≡ (a + c) + (d + b)
    arithmetic2 = solve-∀
    rank/lemma : 
        sum-of-ranks (node (node a p b) k (node c g d)) + 1
      Nat.≤
        sum-of-ranks (node (node a p (node b k c)) g d)
    rank/lemma with <-cmp (rank (node a p b)) (rank (node (node a p b) k (node c g d)))
    ... | tri< rank-y'<rank-x' ¬b ¬c = 
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
        rank-arithmetic1 = solve-∀
        rank-arithmetic2 : (a b c d e f g : val nat) → a + b + (c + d + e) + f + g ≡ (a + c + e + g) + b + f + d
        rank-arithmetic2 = solve-∀
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
            arithmetic = solve-∀
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
    ... | tri≈ ¬a rank-y'≡rank-x' ¬c = 
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
        rank-arithmetic1 = solve-∀
        rank-arithmetic2 : (a b c d e f g : val nat) → (a + c + e + g) + b + f + d ≡ a + b + (c + d + e) + f + g
        rank-arithmetic2 = solve-∀
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
            arithmetic = solve-∀
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
    ... | tri> ¬a ¬b rank-y'>rank-x' = ⊥-elim (Nat.≤⇒≯ rank-y'≤rank-x' rank-y'>rank-x')
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
            arithmetic = solve-∀
    phi/lemma : 
        sum-of-ranks (reconstruct (node (node a p b) k (node c g d)) anc) + 1 
      Nat.≤
        sum-of-ranks (reconstruct (node (node a p (node b k c)) g d) anc)
    phi/lemma = sum-ranks+1/lemma 
      (node (node a p b) k (node c g d)) (node (node a p (node b k c)) g d) anc size/lemma rank/lemma
... | tri> ¬a ¬b rank-x>rank-x' = ⊥-elim (Nat.≤⇒≯ rank-x≤rank-x' rank-x>rank-x')
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
        arithmetic = solve-∀
-- zig-zag
splay'/amortized c d (Right b p ∷ Right a g ∷ anc) k = {!   !}
-- zag-zag

open BST renaming (splay to splay/)

record BSTHom (bst bst' : BST) : Set where
  field
    ϕ : cmp (Π (bst .T) λ _ → F (bst' .T))
    ϕ/splay : (t : val (bst .T)) (k : val nat) → 
        bind (F _) (bst .splay/ t k) (λ (k' , t') → ϕ t')
      ≡
        ϕ t

open BSTHom

-- ST⇒LT : BSTHom SplayTree ListTree
-- ST⇒LT .ϕ t = ret (inord t)
-- ST⇒LT .ϕ/splay t k = 
--   let open ≡-Reasoning in 
--   begin
--     bind (F _) (path k t []) (λ ((t' , anc) , _ , k≡root) →
--       bind (F _) (splay t' k anc (Eq.sym k≡root)) (λ ((k' , t'') , _ , _ , _) → ret (inord t'')))
--   ≡⟨ Eq.cong (bind (F _) (path k t [])) (funext (λ ((t' , anc) , t≡recon/t' , k≡root) → 
--       Eq.cong (bind (F _) (splay t' k anc (Eq.sym k≡root))) (funext (λ ((k' , t'') , inord/recon/t'≡inord/t'' , _ , _) → 
--         Eq.cong ret (Eq.sym (Eq.trans (Eq.cong inord t≡recon/t') inord/recon/t'≡inord/t'')))))) ⟩
--     bind (F _) (path k t []) (λ ((t' , anc) , _ , k≡root) →
--       bind (F _) (splay t' k anc (Eq.sym k≡root)) (λ ((k' , t'') , _ , _ , _) → ret (inord t)))
--   ≡⟨ {!   !} ⟩
--     ret (inord t)
--   ∎

-- open BST renaming (splay to splay/)

-- ex : Tree
-- ex = node (node (node (node (node (node (node leaf 3 leaf) 5 leaf) 6 leaf) 8 leaf) 10 leaf) 11 leaf) 12 leaf

-- _ = {! bind (F _) (splay/ SplayTree ex 0) (λ (_ , t) → splay/ SplayTree t 14)   !}