{-# OPTIONS --prop --rewriting #-}

module Examples.AVLTree where

open import Algebra.Cost

costMonoid = ℕ-CostMonoid
open CostMonoid costMonoid using (ℂ)

open import Calf costMonoid
open import Calf.Data.Nat
open import Calf.Data.IsBounded costMonoid
open import Calf.Data.IsBoundedG costMonoid using (cost; step⋆; step⋆-mono-≤⁻)

open import Data.Nat.Properties
  using ( ≤-refl; ≤-trans; ≤-antisym; ≤-reflexive; n≤1+n; m≤n⇒m≤1+n
        ; ≰⇒>; ≮⇒≥; m≤n⇒m⊔n≡n; ⊔-comm; +-mono-≤; +-identityʳ
        ; m≤m+n; +-suc; +-comm
        ; _≟_; _≤?_ )
open import Data.Nat.Log2 using (⌈log₂_⌉; log₂-mono)
import Data.Nat.Logarithm as Logarithm
import Data.Nat.Solver
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; subst; trans)
open import Function using (_∘_; _$_)
open import Relation.Nullary using (Dec; yes; no)

data ∼ : ℕ → ℕ → ℕ → Set where
  ∼+ : ∀ {n} → ∼ n (1 + n) (2 + n)    -- right-heavy
  ∼0 : ∀ {n} → ∼ n n (1 + n)          -- balanced
  ∼- : ∀ {n} → ∼ (1 + n) n (2 + n)    -- left-heavy

data Tree : ℕ → Set where
  Leaf : Tree 0
  Node : ∀ {hl hr h} → ∼ hl hr h → Tree hl → ℕ → Tree hr → Tree h

data Tree⁺ (h : ℕ) : Set where
  same   : Tree h       → Tree⁺ h
  higher : Tree (1 + h) → Tree⁺ h

tree : ℕ → tp⁺
tree h = meta⁺ (Tree h)

tree⁺ : ℕ → tp⁺
tree⁺ h = meta⁺ (Tree⁺ h)

-- Rebalance when right subtree may have grown by 1
joinR⁺ : ∀ {hl hr h} → ∼ hl hr h → Tree hl → ℕ → Tree⁺ hr → Tree⁺ h
joinR⁺ bal l v (same r)                                    = {!   !}
joinR⁺ ∼- l v (higher r)                                   = {!   !}
joinR⁺ ∼0 l v (higher r)                                   = {!   !}
joinR⁺ ∼+ l v (higher (Node ∼+ rl rv rr))                  = {!   !}
joinR⁺ ∼+ l v (higher (Node ∼0 rl rv rr))                  = {!   !}
joinR⁺ ∼+ l v (higher (Node ∼- (Node ∼0 rll rlv rlr) rv rr)) = {!   !}
joinR⁺ ∼+ l v (higher (Node ∼- (Node ∼+ rll rlv rlr) rv rr)) = {!   !}
joinR⁺ ∼+ l v (higher (Node ∼- (Node ∼- rll rlv rlr) rv rr)) = {!   !}

-- Rebalance when left subtree may have grown by 1
joinL⁺ : ∀ {hl hr h} → ∼ hl hr h → Tree⁺ hl → ℕ → Tree hr → Tree⁺ h
joinL⁺ bal (same l) v r                                    = {!   !}
joinL⁺ ∼+ (higher l) v r                                   = {!   !}
joinL⁺ ∼0 (higher l) v r                                   = {!   !}
joinL⁺ ∼- (higher (Node ∼- ll lv lr)) v r                  = {!   !}
joinL⁺ ∼- (higher (Node ∼0 ll lv lr)) v r                  = {!   !}
joinL⁺ ∼- (higher (Node ∼+ ll lv (Node ∼0 lrl lrv lrr))) v r = {!   !}
joinL⁺ ∼- (higher (Node ∼+ ll lv (Node ∼- lrl lrv lrr))) v r = {!   !}
joinL⁺ ∼- (higher (Node ∼+ ll lv (Node ∼+ lrl lrv lrr))) v r = {!   !}

-- Build a node from c and tr where hr ≤ h_c ≤ suc hr
mkNode : ∀ {h_c hr} → Tree h_c → ℕ → Tree hr → hr ≤ h_c → h_c ≤ suc hr → Tree (suc h_c)
mkNode {h_c} {hr} c k tr hr≤hc hc≤1+hr with h_c ≟ hr
... | yes refl   = Node ∼0 c k tr
... | no  hc≢hr  = go (sym (≤-antisym (≰⇒> (hc≢hr ∘ sym ∘ ≤-antisym hr≤hc)) hc≤1+hr))
  where
    go : h_c ≡ suc hr → Tree (suc h_c)
    go refl = Node ∼- c k tr

-- Mirror of mkNode for the left-heavy case
mkNodeL : ∀ {hl h_l} → Tree hl → ℕ → Tree h_l → hl ≤ h_l → h_l ≤ suc hl → Tree (suc h_l)
mkNodeL {hl} {h_l} tl k c hl≤hl' hl'≤1+hl with h_l ≟ hl
... | yes refl    = Node ∼0 tl k c
... | no  h_l≢hl  = go (sym (≤-antisym (≰⇒> (h_l≢hl ∘ sym ∘ ≤-antisym hl≤hl')) hl'≤1+hl))
  where
    go : h_l ≡ suc hl → Tree (suc h_l)
    go refl = Node ∼+ tl k c

-- Derive hr ≤ h_c from balance tag and spine precondition
bal-hr≤hc : ∀ {h_l h_c hl hr} → ∼ h_l h_c (suc hl) → suc hr ≤ hl → hr ≤ h_c
bal-hr≤hc ∼0 p        = ≤-trans (n≤1+n _) p
bal-hr≤hc ∼+ (s≤s p)  = m≤n⇒m≤1+n p
bal-hr≤hc ∼- (s≤s p)  = p

-- Mirror: derive hl' ≤ h_l from balance tag and spine precondition
bal-hl≤hl : ∀ {h_l h_c hl hl'} → ∼ h_l h_c (suc hl) → suc hl' ≤ hl → hl' ≤ h_l
bal-hl≤hl ∼0 p        = ≤-trans (n≤1+n _) p
bal-hl≤hl ∼- (s≤s p)  = m≤n⇒m≤1+n p
bal-hl≤hl ∼+ (s≤s p)  = p

-- Build a balanced node when the heights differ by at most 1
mkBal : ∀ {hl hr} → Tree (suc hl) → ℕ → Tree (suc hr)
      → hl ≤ suc hr → hr ≤ suc hl → Tree⁺ (suc (hl ⊔ hr))
mkBal {hl} {hr} tl k tr hl≤1+hr hr≤1+hl with hl ≟ hr
... | yes refl   = subst Tree⁺ (sym (cong suc (m≤n⇒m⊔n≡n ≤-refl)))
                         (higher (Node ∼0 tl k tr))
... | no  hl≢hr  with hl ≤? hr
...   | yes hl≤hr = go (sym (≤-antisym (≰⇒> (λ hr≤hl → hl≢hr (≤-antisym hl≤hr hr≤hl))) hr≤1+hl))
  where
    go : hr ≡ suc hl → Tree⁺ (suc (hl ⊔ hr))
    go refl = subst Tree⁺ (sym (cong suc (m≤n⇒m⊔n≡n (n≤1+n hl))))
                    (higher (Node ∼+ tl k tr))
mkBal {hl} {hr} tl k tr hl≤1+hr hr≤1+hl | no hl≢hr | no ¬hl≤hr =
  go (≤-antisym (≰⇒> ¬hl≤hr) hl≤1+hr)
  where
    go : suc hr ≡ hl → Tree⁺ (suc (hl ⊔ hr))
    go refl = subst Tree⁺ (sym (cong suc (trans (⊔-comm (suc hr) hr) (m≤n⇒m⊔n≡n (n≤1+n hr)))))
                     (higher (Node ∼- tl k tr))

-- Right-spine descent helper for joinRight.
descend-right : ∀ {hr} {h_c} → 
  cmp (Π nat λ _ → 
       Π (tree hr) λ _ → 
       Π (tree h_c) λ _ → 
       Π (meta⁺ (hr ≤ h_c)) λ _ → 
       F (tree⁺ h_c))
descend-right {hr} k tr Leaf z≤n = {!   !}
descend-right {hr} k tr (Node (∼0 {n}) l' lv' c') hr≤sn with n ≤? hr
... | yes q = {!   !}
... | no ¬q = {!   !}
descend-right {hr} k tr (Node (∼+ {n}) l' lv' c') hr≤2sn with suc n ≤? hr
... | yes q = {!   !}
... | no ¬q = {!   !}
descend-right {hr} k tr (Node (∼- {n}) l' lv' c') hr≤2sn with suc n ≤? hr
... | yes q = {!   !}
... | no ¬q = {!   !}

-- Descend the right spine of the left tree, then rebalance upward.
joinRight : ∀ {hl hr} →
  cmp (Π (tree (suc hl)) λ _ →
       Π nat λ _ →
       Π (tree hr) λ _ →
       Π (meta⁺ (suc hr ≤ hl)) λ _ →
       F (tree⁺ (suc hl)))
joinRight {hr = hr} (Node bal l lv c) k tr p = {!   !}

-- Left-spine descent helper for joinLeft.
descend-left : ∀ {hl} {h_c} →
  cmp (Π (tree hl) λ _ →
       Π nat λ _ →
       Π (tree h_c) λ _ →
       Π (meta⁺ (hl ≤ h_c)) λ _ →
       F (tree⁺ h_c))
descend-left {hl} tl k Leaf z≤n = {!   !}
descend-left {hl} tl k (Node (∼0 {n}) l' lv' r') hl≤sn with n ≤? hl
... | yes q = {!   !}
... | no ¬q = {!   !}
descend-left {hl} tl k (Node (∼+ {n}) l' lv' r') hl≤2sn with suc n ≤? hl
... | yes q = {!   !}
... | no ¬q = {!   !}
descend-left {hl} tl k (Node (∼- {n}) l' lv' r') hl≤2sn with suc n ≤? hl
... | yes q = {!   !}
... | no ¬q = {!   !}

-- Descend the left spine of the right tree, then rebalance upward.
joinLeft : ∀ {hl hr} →
  cmp (Π (tree hl) λ _ →
       Π nat λ _ →
       Π (tree (suc hr)) λ _ →
       Π (meta⁺ (suc hl ≤ hr)) λ _ →
       F (tree⁺ (suc hr)))
joinLeft {hl} tl k (Node bal c rv r) p = {!   !}

-- Top-level join: dispatch to joinRight, joinLeft, or mkBal.
join : ∀ {hl hr} →
  cmp (Π (tree hl) λ _ →
       Π nat λ _ →
       Π (tree hr) λ _ →
       F (tree⁺ (hl ⊔ hr)))
-- Both empty
join {zero}          {zero}          Leaf k Leaf = {!   !}
-- One side empty
join {zero}          {suc zero}      Leaf k tr   = {!   !}
join {zero}          {suc (suc hr')} Leaf k tr   = {!   !}
join {suc zero}      {zero}          tl   k Leaf = {!   !}
join {suc (suc hl')} {zero}          tl   k Leaf = {!   !}
-- Both non-empty: compare heights and dispatch
join {suc hl'} {suc hr'} tl k tr = {!   !}
