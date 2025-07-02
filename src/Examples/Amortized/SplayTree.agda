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
open import Data.Empty using (⊥; ⊥-elim)


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
  Left : (k : val nat) (t : Tree) → Context
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
... | tri< _ _ _ = path k l (Left x r ∷ anc)
... | tri≈ _ k≡x _ = ret ((node l x r , anc) , refl , Eq.sym k≡x)
... | tri> _ _ _ = path k r (Right l x ∷ anc)

splay'ResultType : val nat → Tree → Tree → List Context → tp⁺
splay'ResultType k a b anc = Σ⁺ (tree ×⁺ tree) (λ (a' , b') → 
  meta⁺ (inord (reconstruct (node a k b) anc) ≡ inord (node a' k b')))

splay' : (a : Tree) (b : Tree) (anc : List Context) (k : val nat) → cmp (F (splay'ResultType k a b anc))
splay' a b [] k = ret ((a , b) , refl)
-- done
splay' a b (Left p c ∷ []) k = ret ((a , node b p c) , arithmetic (inord a) (k ∷ inord b) (p ∷ inord c))
  where
    arithmetic : (l₁ l₂ l₃ : val (list nat)) → (l₁ ++ l₂) ++ l₃ ≡ l₁ ++ l₂ ++ l₃
    arithmetic l₁ l₂ l₃ = ++-assoc l₁ l₂ l₃
-- zig
splay' b c (Right a p ∷ []) k = ret ((node a p b , c) , arithmetic (inord a) (p ∷ inord b) (k ∷ inord c))
  where
    arithmetic : (l₁ l₂ l₃ : val (list nat)) → l₁ ++ l₂ ++ l₃ ≡ (l₁ ++ l₂) ++ l₃
    arithmetic l₁ l₂ l₃ = Eq.sym (++-assoc l₁ l₂ l₃)
-- zag
splay' a b (Left p c ∷ Left g d ∷ anc) k = 
  bind (F _) (splay' a (node b p (node c g d)) anc k) (λ ((l' , r') , recon≡inord) → 
    ret ((l' , r') , Eq.trans (inord/reconstruct 
       (node (node (node a k b) p c) g d) 
       (node a k (node b p (node c g d))) 
       anc 
       (inord/arith a b c d k p g)) recon≡inord))
  where
    arithmetic : (l₁ l₂ l₃ l₄ : val (list nat)) → ((l₁ ++ l₂) ++ l₃) ++ l₄ ≡ l₁ ++ l₂ ++ l₃ ++ l₄
    arithmetic l₁ l₂ l₃ l₄ = 
      let open ≡-Reasoning in 
      begin
        ((l₁ ++ l₂) ++ l₃) ++ l₄
      ≡⟨ ++-assoc (l₁ ++ l₂) l₃ l₄ ⟩
        (l₁ ++ l₂) ++ (l₃ ++ l₄)
      ≡⟨ ++-assoc l₁ l₂ (l₃ ++ l₄) ⟩
        l₁ ++ (l₂ ++ (l₃ ++ l₄))
      ∎
    inord/arith : (a b c d : Tree) (k p g : val nat) →  
      inord (node (node (node a k b) p c) g d) ≡ inord (node a k (node b p (node c g d)))
    inord/arith a b c d k p g = arithmetic (inord a) (k ∷ inord b) (p ∷ inord c) (g ∷ inord d)
-- zig-zig
splay' b c (Left p d ∷ Right a g ∷ anc) k = 
  bind (F _) (splay' (node a g b) (node c p d) anc k) (λ ((l' , r') , recon≡inord) → 
    ret ((l' , r') , Eq.trans (inord/reconstruct 
       (node a g (node (node b k c) p d))
       (node (node a g b) k (node c p d))
       anc 
       (inord/arith a b c d k p g)) recon≡inord))
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
  bind (F _) (splay' (node a p b) (node c g d) anc k) (λ ((l' , r') , recon≡inord) → 
    ret ((l' , r') , Eq.trans (inord/reconstruct 
       (node (node a p (node b k c)) g d)
       (node (node a p b) k (node c g d))
       anc 
       (inord/arith a b c d k p g)) recon≡inord))
  where
    arithmetic : (l₁ l₂ l₃ l₄ : val (list nat)) → (l₁ ++ l₂ ++ l₃) ++ l₄ ≡ (l₁ ++ l₂) ++ l₃ ++ l₄
    arithmetic l₁ l₂ l₃ l₄ = 
      let open ≡-Reasoning in
      begin
        (l₁ ++ (l₂ ++ l₃)) ++ l₄
      ≡⟨ Eq.cong (λ e → e ++ l₄) (++-assoc l₁ l₂ l₃) ⟨
        ((l₁ ++ l₂) ++ l₃) ++ l₄
      ≡⟨ ++-assoc (l₁ ++ l₂) l₃ l₄ ⟩
        (l₁ ++ l₂) ++ l₃ ++ l₄
      ∎
    inord/arith : (a b c d : Tree) (k p g : val nat) → 
      inord (node (node a p (node b k c)) g d) ≡ inord (node (node a p b) k (node c g d))
    inord/arith a b c d k p g = arithmetic (inord a) (p ∷ inord b) (k ∷ inord c) (g ∷ inord d)
-- zig-zag
splay' c d (Right b p ∷ Right a g ∷ anc) k = 
  bind (F _) (splay' (node (node a g b) p c) d anc k) (λ ((l' , r') , recon≡inord) →
    ret ((l' , r') , Eq.trans (inord/reconstruct 
       (node a g (node b p (node c k d)))
       (node (node (node a g b) p c) k d)
       anc 
       (inord/arith a b c d k p g)) recon≡inord))
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

open BST renaming (splay to splay/)

record BSTHom (bst bst' : BST) : Set where
  field
    ϕ : cmp (Π (bst .T) λ _ → F (bst' .T))
    ϕ/splay : (t : val (bst .T)) (k : val nat) → 
        bind (F _) (bst .splay/ t k) (λ (k' , t') → ϕ t')
      ≡
        ϕ t

open BSTHom

ST⇒LT : BSTHom SplayTree ListTree
ST⇒LT .ϕ t = ret (inord t)
ST⇒LT .ϕ/splay t k = 
  let open ≡-Reasoning in 
  begin
    bind (F _) (path k t []) (λ ((t' , anc) , _ , k≡root) →
      bind (F _) (splay t' k anc (Eq.sym k≡root)) (λ ((k' , t'') , _ , _ , _) → ret (inord t'')))
  ≡⟨ Eq.cong (bind (F _) (path k t [])) (funext (λ ((t' , anc) , t≡recon/t' , k≡root) → 
      Eq.cong (bind (F _) (splay t' k anc (Eq.sym k≡root))) (funext (λ ((k' , t'') , inord/recon/t'≡inord/t'' , _ , _) → 
        Eq.cong ret (Eq.sym (Eq.trans (Eq.cong inord t≡recon/t') inord/recon/t'≡inord/t'')))))) ⟩
    bind (F _) (path k t []) (λ ((t' , anc) , _ , k≡root) →
      bind (F _) (splay t' k anc (Eq.sym k≡root)) (λ ((k' , t'') , _ , _ , _) → ret (inord t)))
  ≡⟨ {!   !} ⟩
    ret (inord t)
  ∎

-- open BST renaming (splay to splay/)

-- ex : Tree
-- ex = node (node (node (node (node (node (node leaf 0 leaf) 1 leaf) 2 leaf) 3 leaf) 4 leaf) 5 leaf) 6 leaf

-- _ = {! splay/ SplayTree ex 0    !}