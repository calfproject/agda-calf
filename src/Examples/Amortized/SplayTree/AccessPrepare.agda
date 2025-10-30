{-# OPTIONS --rewriting --allow-unsolved-metas #-}

module Examples.Amortized.SplayTree.AccessPrepare where

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
              ≡⟨ arithmetic₄ 1 ⌊ n /2⌋ 1 ⌊ n /2⌋ ⟩
                (1 + 1) + (⌊ n /2⌋ + ⌊ n /2⌋)
              ≤⟨ s≤s (s≤s (Nat.+-monoʳ-≤ ⌊ n /2⌋ (Nat.⌊n/2⌋-mono (Nat.n≤1+n n)))) ⟩
                (1 + 1) + (⌊ n /2⌋ + ⌈ n /2⌉)
              ≡⟨ Eq.cong (λ e → (1 + 1) + e) (Nat.⌊n/2⌋+⌈n/2⌉≡n n) ⟩
                2+ n
              ∎

rank/recon : (t₁ t₂ : Tree) (anc : List Context) → tree-size t₁ ≡ tree-size t₂ → rank (reconstruct t₁ anc) ≡ rank (reconstruct t₂ anc)
rank/recon t₁ t₂ [] st₁≡st₂ = Eq.cong (λ e → ⌊log₂ e ⌋) st₁≡st₂
rank/recon t₁ t₂ (Left k t ∷ anc) st₁≡st₂ = rank/recon (node t₁ k t) (node t₂ k t) anc 
  (Eq.cong (λ e → e + 1 + tree-size t) st₁≡st₂)
rank/recon t₁ t₂ (Right t k ∷ anc) st₁≡st₂ = rank/recon (node t k t₁) (node t k t₂) anc 
  (Eq.cong (λ e → tree-size t + 1 + e) st₁≡st₂)

φ : cmp (Π tree λ _ → F (list nat))
φ t = step (F _) (sum-of-ranks t) (ret (inord t))

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
  ≡⟨ arithmetic₁ (sum-of-ranks t₁) (rank (node t₁ k t)) (sum-of-ranks t) 1 ⟩
    (sum-of-ranks t₁ + 1) + rank (node t₁ k t) + sum-of-ranks t
  ≤⟨ +-monoˡ-≤ (sum-of-ranks t) (+-monoˡ-≤ (rank (node t₁ k t)) ranks) ⟩
    sum-of-ranks t₂ + rank (node t₁ k t) + sum-of-ranks t
  ≡⟨ Eq.cong (λ e → sum-of-ranks t₂ + e + sum-of-ranks t) 
      (Eq.cong (λ e → ⌊log₂ (e + 1 + tree-size t) ⌋) size) ⟩
    sum-of-ranks t₂ + rank (node t₂ k t) + sum-of-ranks t
  ∎)
sum-ranks+1/lemma t₁ t₂ (Right t k ∷ anc) size ranks = sum-ranks+1/lemma (node t k t₁) (node t k t₂) anc 
  (Eq.cong (λ e → tree-size t + 1 + e) size)
  (let open Nat.≤-Reasoning in
  begin
    sum-of-ranks t + rank (node t k t₁) + sum-of-ranks t₁ + 1
  ≡⟨ arithmetic₂ (sum-of-ranks t) (rank (node t k t₁)) (sum-of-ranks t₁) 1 ⟩
    sum-of-ranks t + rank (node t k t₁) + (sum-of-ranks t₁ + 1)
  ≤⟨ +-monoʳ-≤ (sum-of-ranks t + rank (node t k t₁)) ranks ⟩
    sum-of-ranks t + rank (node t k t₁) + sum-of-ranks t₂
  ≡⟨ Eq.cong (λ e → sum-of-ranks t + e + sum-of-ranks t₂) 
      (Eq.cong (λ e → ⌊log₂ (tree-size t + 1 + e) ⌋) size) ⟩
    sum-of-ranks t + rank (node t k t₂) + sum-of-ranks t₂
  ∎) 

sum-ranks+x/lemma : (t₁ t₂ : Tree) (anc : List Context) (x : val nat) 
    → tree-size t₁ ≡ tree-size t₂ 
    → sum-of-ranks t₁ Nat.≤ x + sum-of-ranks t₂ 
    → sum-of-ranks (reconstruct t₁ anc) Nat.≤ x + sum-of-ranks (reconstruct t₂ anc)
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
  ≡⟨ arithmetic₃ (sum-of-ranks t) (rank (node t k t₂)) x (sum-of-ranks t₂) ⟩
    x + (sum-of-ranks t + rank (node t k t₂) + sum-of-ranks t₂)
  ∎)
  