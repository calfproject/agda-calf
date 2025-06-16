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
open import Data.List.Properties as List 
open import Data.Fin using (Fin; fromℕ<)
open import Relation.Nullary using (Dec; yes; no)

open import Relation.Binary 
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; module ≡-Reasoning)

open import Tactic.MonoidSolver using (solve; solve-macro)

record BST : Set where
  field 
    T : tp⁺
    splay : cmp (Π T (λ _ → Π nat (λ _ → F (nat ×⁺ T))))
    size : cmp (Π T (λ _ → F nat))


ListTree : BST
ListTree .BST.T = list nat
ListTree .BST.splay l i with i <? length l 
... | yes p = let finIdx = fromℕ< p in ret (lookup l finIdx , l)
... | no _ = ret (0 , l)
ListTree .BST.size l = ret (length l)

data Tree : Set where
  leaf : Tree
  node : Tree → val nat → Tree → Tree

tree : tp⁺
tree = meta⁺ (Tree)

data Splayed : Set where
  valid : (t : Tree) → Splayed 
  zig :   (a : Tree) (x : val nat) (b : Tree) (y : val nat) (c : Tree) → Splayed 
  zag :   (a : Tree) (y : val nat) (b : Tree) (x : val nat) (c : Tree) → Splayed

splayed : tp⁺
splayed = meta⁺ (Splayed)

tree-size : Tree → val nat
tree-size leaf = 0
tree-size (node l z r) = (tree-size l) + 1 + (tree-size r)

splayed-size : Splayed → val nat
splayed-size (valid t) = tree-size t
splayed-size (zig a x b y c) = tree-size a + 1 + tree-size b + 1 + tree-size c
splayed-size (zag a y b x c) = tree-size a + 1 + tree-size b + 1 + tree-size c

<-splayHelper : (z : val nat) (r : Tree) → (l : Splayed) {i : val nat} {i<l : i < (splayed-size l)} → cmp (F (splayed))
<-splayHelper z r (valid (node a x b)) = ret (zig a x b z r)
<-splayHelper z r (zig a x b y c) = ret (valid (node a x (node b y (node c z r))))
<-splayHelper z r (zag a y b x c) = ret (valid (node (node a y b) x (node c z r))) 

>-splayHelper : (z : val nat) (l : Tree) → (r : Splayed) {i : val nat} {i<r : i < (splayed-size r)} → cmp (F (splayed))
>-splayHelper z l (valid (node a x b)) = ret (zag l z a x b)
>-splayHelper z l (zig a x b y c) = ret (valid (node (node l z a) x (node b y c)))
>-splayHelper z l (zag a y b x c) = ret (valid (node (node (node l z a) y b) x c))

<-splayResultType : Tree → Splayed → tp⁺
<-splayResultType r l = Σ⁺ splayed λ l' → meta⁺ (splayed-size l' ≡ splayed-size l + 1 + tree-size r)

<-splayHelper' : (z : val nat) (r : Tree) (l : Splayed) {i : val nat} {i<l : i < (splayed-size l)} → cmp (F (<-splayResultType r l))
<-splayHelper' z r (valid (node a x b)) = ret (zig a x b z r , refl)
<-splayHelper' z r (zig a x b y c) = 
  ret (valid (node a x (node b y (node c z r))) , 
    arithmetic (tree-size a) (tree-size b) (tree-size c) (tree-size r))
    where 
      arithmetic : (a b c d : val nat) → a + 1 + (b + 1 + (c + 1 + d)) ≡ a + 1 + b + 1 + c + 1 + d
      arithmetic a b c d = solve Nat.+-0-monoid
<-splayHelper' z r (zag a y b x c) = {!   !}

splayResultType : Tree → tp⁺ 
splayResultType t = Σ⁺ splayed λ l → meta⁺ (splayed-size l ≡ tree-size t)

splay' : (t : Tree) → (i : val nat) → i < (tree-size t) → cmp (F (splayResultType t))
splay' (node l z r) i i<t with <-cmp i (tree-size l)
... | tri< i<l i≢l _ = 
  bind (F (splayResultType (node l z r))) (splay' l i i<l) λ (l' , l'≡l) → 
    bind (F _) (<-splayHelper' z r l' {i = i} {i<l = Eq.subst (λ n → i < n) (Eq.sym l'≡l) i<l}) λ (l'' , l''≡r+1+l') → 
      ret (l'' , Eq.trans l''≡r+1+l' (Eq.cong (λ n → n + 1 + tree-size r) l'≡l)) 

splay : (t : Tree) → (i : val nat) → i < (tree-size t) → cmp (F (splayed))
splay (node l z r) i i<t with <-cmp i (tree-size l)
... | tri< i<l i≢l _ = 
  bind (F (splayed)) (splay l i i<l) λ l → <-splayHelper z r l {i = i} {i<l = {! i<l  !}}
  -- λ
    -- { (valid leaf) → ret (valid leaf)
    -- ; (valid (node a x b)) → ret (zig a x b z r) 
    -- ; (zig a x b y c) → ret (valid (node a x (node b y (node c z r))))
    -- ; (zag a y b x c) → ret (valid (node (node a y b) x (node c z r))) 
    -- }
... | tri≈ _ i=l _ = ret (valid (node l z r))
... | tri> _ _ i>l = 
  let
    arithmetic : i ∸ ((tree-size l) + 1) Nat.< (tree-size r)
    arithmetic = let open Nat.≤-Reasoning in 
      Nat.+-cancelˡ-< ((tree-size l) + 1) (i ∸ ((tree-size l) + 1)) (tree-size r) (
        begin-strict
          ((tree-size l) + 1) + (i ∸ ((tree-size l) + 1))
        ≡⟨ Nat.m+[n∸m]≡n (Eq.subst (i Nat.≥_) (Nat.+-comm 1 (tree-size l)) i>l) ⟩ 
          i
        <⟨ i<t ⟩
          (tree-size l) + 1 + (tree-size r)
        ∎
      )
  in
  bind (F (splayed)) (splay r (i ∸ ((tree-size l) + 1)) arithmetic) λ 
    { (valid leaf) → ret (valid leaf)
    ; (valid (node a x b)) → ret (zag l z a x b)
    ; (zig a x b y c) → ret (valid (node (node l z a) x (node b y c)))
    ; (zag a y b x c) → ret (valid (node (node (node l z a) y b) x c))
    }

SplayTree : BST
SplayTree .BST.T = tree
SplayTree .BST.splay t i with <-cmp i (tree-size t)
... | tri< i<t _ _ = 
  bind (F _) (splay t i i<t) λ 
    { (valid leaf) → ret (0 , t)
    ; (valid (node l z r)) → ret (z , node l z r)
    ; (zig a x b y c) → ret (y , node (node a x b) y c)
    ; (zag a y b x c) → ret (y , node a y (node b x c))
    }
... | tri≈ _ _ _ = ret (0 , t)
... | tri> _ _ _ = ret (0 , t)
SplayTree .BST.size leaf = ret 0
SplayTree .BST.size (node l z r) = ret (tree-size (node l z r))

-- inord : {n : ℕ} → Tree n → val (list nat)
-- inord leaf = []
-- inord (node l z r) = (inord l) ++ (z ∷ []) ++ (inord r)

inord/cmp : cmp (Π tree λ _ → F (list nat))
inord/cmp leaf = ret []
inord/cmp (node l z r) = 
  bind (F _) (inord/cmp l) (λ l' → 
  bind (F _) (inord/cmp r) (λ r' → ret (l' ++ z ∷ [] ++ r')))


-- inord/correct : {n : val nat} {t : Tree n} → length (inord t) ≡ n
-- inord/correct {n} {leaf} = refl
-- inord/correct {n} {node {n₁} {n₂} t₁ x t₂} = 
--   let open ≡-Reasoning in
--   begin 
--     length (inord t₁ ++ x ∷ inord t₂)
--   ≡⟨ length-++ {A = val nat} (inord t₁) ⟩ 
--     length (inord t₁) + length (x ∷ inord t₂)
--   ≡⟨⟩ 
--     length (inord t₁) + (1 + length (inord t₂))
--   ≡⟨ Eq.cong₂ _+_ (inord/correct {t = t₁}) (Eq.cong (1 +_) (inord/correct {t = t₂})) ⟩ 
--     n₁ + (1 + n₂)
--   ≡⟨ +-assoc n₁ 1 n₂ ⟨ 
--     n₁ + 1 + n₂
--   ∎

-- inord/splayed : {n : val nat} → val (splayed n) → val (list nat)
-- inord/splayed (valid t)       = inord t
-- inord/splayed (zig a x b y c) = inord a ++ x ∷ [] ++ inord b ++ y ∷ [] ++ inord c
-- inord/splayed (zag a y b x c) = inord a ++ y ∷ [] ++ inord b ++ x ∷ [] ++ inord c

inord/splayed/cmp : cmp (Π splayed λ _ → F (list nat))
inord/splayed/cmp (valid t)       = inord/cmp t
inord/splayed/cmp (zig a x b y c) = 
  bind (F _) (inord/cmp a) (λ a' → 
  bind (F _) (inord/cmp b) (λ b' → 
  bind (F _) (inord/cmp c) λ c' → 
    ret (a' ++ x ∷ [] ++ b' ++ y ∷ [] ++ c')))
inord/splayed/cmp (zag a y b x c) = 
  bind (F _) (inord/cmp a) (λ a' → 
  bind (F _) (inord/cmp b) (λ b' → 
  bind (F _) (inord/cmp c) λ c' → 
    ret (a' ++ y ∷ [] ++ b' ++ x ∷ [] ++ c')))

<-splayHelper'/correct : 
  (z : val nat) (r : Tree) (l : Splayed) {i : val nat} {i<l : i < splayed-size l}  → 
  bind (F (list nat)) (<-splayHelper' z r l {i = i} {i<l = i<l}) (λ (l' , _) → inord/splayed/cmp l')
  ≡
  bind (F (list nat)) (inord/splayed/cmp l) λ l' → bind (F _) (inord/cmp r) (λ r' → ret (l' ++ z ∷ [] ++ r'))
<-splayHelper'/correct z r (valid (node t x t₁)) {i} {i<l} = {!   !}
<-splayHelper'/correct z r (zig a x b y c) {i} {i<l} = 
  let open ≡-Reasoning in
  begin 
    bind (F _) (inord/cmp a) (λ l₁ →
      bind (F _) (inord/cmp b) (λ l₂ →
        bind (F _) (inord/cmp c) (λ l₃ →
          bind (F _) (inord/cmp r) (λ l₄ → 
            ret (l₁ ++ x ∷ l₂ ++ y ∷ l₃ ++ z ∷ l₄))))) 
  ≡⟨ Eq.cong (bind (F _) (inord/cmp a)) (funext (λ l₁ → 
      Eq.cong (bind (F _) (inord/cmp b)) (funext (λ l₂ → 
        Eq.cong (bind (F _) (inord/cmp c)) (funext (λ l₃ → 
          Eq.cong (bind (F _) (inord/cmp r)) (funext (λ l₄ → 
            Eq.cong ret (arithmetic l₁ (x ∷ l₂) (y ∷ l₃) (z ∷ l₄)))))))))) ⟩
    bind (F _) (inord/cmp a) (λ l₁ →
      bind (F _) (inord/cmp b) (λ l₂ →
        bind (F _) (inord/cmp c) (λ l₃ →
          bind (F _) (inord/cmp r) (λ l₄ → 
            ret ((l₁ ++ x ∷ l₂ ++ y ∷ l₃) ++ z ∷ l₄))))) 
  ∎
  where 
    arithmetic : (l₁ l₂ l₃ l₄ : val (list nat)) → l₁ ++ l₂ ++ l₃ ++ l₄ ≡ (l₁ ++ l₂ ++ l₃) ++ l₄
    arithmetic l₁ l₂ l₃ l₄ = 
      let open Eq.≡-Reasoning in 
      begin 
        l₁ ++ l₂ ++ l₃ ++ l₄
      ≡⟨ ++-assoc l₁ l₂ (l₃ ++ l₄) ⟨ 
        (l₁ ++ l₂) ++ l₃ ++ l₄
      ≡⟨ ++-assoc (l₁ ++ l₂) l₃ l₄ ⟨ 
        ((l₁ ++ l₂) ++ l₃) ++ l₄
      ≡⟨ Eq.cong (λ l → l ++ l₄) (++-assoc l₁ l₂ l₃) ⟩ 
        (l₁ ++ l₂ ++ l₃) ++ l₄
      ∎
<-splayHelper'/correct z r (zag a y b x c) {i} {i<l} = {!   !}

-- inord/splayed/correct : {n : val nat} {t : val (splayed n)} → length (inord/splayed t) ≡ n
-- inord/splayed/correct {n} {valid t} = inord/correct {t = t}
-- inord/splayed/correct {n} {zig {n₁₁} {n₁₂} {n₁₃} a x b y c} = let open ≡-Reasoning in
--   begin
--     length (inord a ++ (x ∷ inord b ++ y ∷ inord c))
--   ≡⟨ length-++ {A = val nat} (inord a) ⟩
--     length (inord a) + length (x ∷ inord b ++ y ∷ inord c)
--   ≡⟨ Eq.cong₂ _+_ (inord/correct {t = a}) (Eq.cong (1 +_) (inord/correct {t = node {n₁ = n₁₂} {n₂ = n₁₃} b y c})) ⟩
--     n₁₁ + (1 + (n₁₂ + 1 + n₁₃))
--   ≡⟨ +-assoc n₁₁ 1 (n₁₂ + 1 + n₁₃) ⟨
--     n₁₁ + 1 + ((n₁₂ + 1) + n₁₃)
--   ≡⟨ Eq.cong ((n₁₁ + 1) +_) (+-assoc n₁₂ 1 n₁₃) ⟩
--     n₁₁ + 1 + (n₁₂ + (1 + n₁₃))
--   ≡⟨ +-assoc (n₁₁ + 1) n₁₂ (1 + n₁₃) ⟨
--     (n₁₁ + 1 + n₁₂) + (1 + n₁₃)
--   ≡⟨ +-assoc (n₁₁ + 1 + n₁₂) 1 (n₁₃) ⟨
--     n₁₁ + 1 + n₁₂ + 1 + n₁₃
--   ∎
-- inord/splayed/correct {n} {zag {n₁₁} {n₁₂} {n₁₃} a y b x c} = let open ≡-Reasoning in
--   begin
--     length (inord a ++ (y ∷ inord b ++ x ∷ inord c))
--   ≡⟨ length-++ {A = val nat} (inord a) ⟩
--     length (inord a) + length (y ∷ inord b ++ x ∷ inord c)
--   ≡⟨ Eq.cong₂ _+_ (inord/correct {t = a}) (Eq.cong (1 +_) (inord/correct {t = node {n₁ = n₁₂} {n₂ = n₁₃} b x c})) ⟩
--     n₁₁ + (1 + (n₁₂ + 1 + n₁₃))
--   ≡⟨ +-assoc n₁₁ 1 (n₁₂ + 1 + n₁₃) ⟨
--     n₁₁ + 1 + (n₁₂ + 1 + n₁₃)
--   ∎

-- ++-assoc² : (a b c r : List ℕ) (x y z : ℕ) → a ++ x ∷ b ++ y ∷ c ++ z ∷ r ≡ (a ++ x ∷ b ++ y ∷ c) ++ z ∷ r
-- ++-assoc² a b c r x y z = 
--   let open ≡-Reasoning in
--   begin
--     a ++ (x ∷ b ++ (y ∷ c ++ z ∷ r))
--   ≡⟨ ++-assoc a (x ∷ b) (y ∷ c ++ z ∷ r) ⟨
--     (a ++ x ∷ b) ++ (y ∷ c ++ z ∷ r)
--   ≡⟨ ++-assoc (a ++ x ∷ b) (y ∷ c) (z ∷ r) ⟨
--     ((a ++ x ∷ b) ++ y ∷ c) ++ z ∷ r
--   ≡⟨ Eq.cong (_++ (z ∷ r)) (++-assoc a (x ∷ b) (y ∷ c)) ⟩
--     (a ++ x ∷ b ++ y ∷ c) ++ z ∷ r
--   ∎

-- ++-assoc³ : (a b c r : List ℕ) (x y z : ℕ) → (a ++ y ∷ b) ++ x ∷ c ++ z ∷ r ≡ (a ++ y ∷ b ++ x ∷ c) ++ z ∷ r
-- ++-assoc³ a b c r x y z = 
--   let open ≡-Reasoning in
--   begin
--     (a ++ y ∷ b) ++ (x ∷ c ++ z ∷ r)
--   ≡⟨ ++-assoc (a ++ y ∷ b) (x ∷ c) (z ∷ r) ⟨
--     ((a ++ y ∷ b) ++ x ∷ c) ++ z ∷ r
--   ≡⟨ Eq.cong (_++ (z ∷ r)) (++-assoc a (y ∷ b) (x ∷ c)) ⟩
--     (a ++ y ∷ b ++ x ∷ c) ++ z ∷ r
--   ∎

-- ++-assoc⁴ : (l a b c : List ℕ) (z x y : ℕ) → ((l ++ z ∷ a) ++ y ∷ b) ++ x ∷ c ≡ l ++ z ∷ a ++ y ∷ b ++ x ∷ c
-- ++-assoc⁴ l a b c z x y = 
--   let open ≡-Reasoning in
--   begin
--     ((l ++ z ∷ a) ++ (y ∷ b)) ++ (x ∷ c)
--   ≡⟨ ++-assoc (l ++ z ∷ a) (y ∷ b) (x ∷ c) ⟩
--     (l ++ (z ∷ a)) ++ (y ∷ b ++ x ∷ c)
--   ≡⟨ ++-assoc l (z ∷ a) (y ∷ b ++ x ∷ c) ⟩
--     l ++ (z ∷ a ++ (y ∷ b ++ x ∷ c))
--   ∎

-- <-splayHelper/correct : {n₁ n₂ i : val nat} {i<n₁ : i < n₁} (z : val nat) (r : Tree n₂) (l : Splayed n₁)→ 
--   bind (F (list nat)) (<-splayHelper {i = i} {i<n₁ = i<n₁} z r l) (inord/splayed/cmp {n = n₁ + 1 + n₂}) 
--   ≡
--   bind (F (list nat)) (inord/splayed/cmp {n = n₁} l) λ l' → bind (F _) (inord/cmp r) (λ r' → ret (l' ++ z ∷ [] ++ r'))
-- <-splayHelper/correct {n₁} {n₂} z r (valid (node a x b)) = 
--   let open ≡-Reasoning in
--   begin 
--      bind (F _) (inord/cmp a) (λ a' → 
--      bind (F _) (inord/cmp b) (λ b' → 
--      bind (F _) (inord/cmp r) λ c' → 
--        ret (a' ++ x ∷ [] ++ b' ++ z ∷ [] ++ c')))
--   ≡⟨ Eq.cong (λ e → bind (F _) (inord/cmp a) e) (funext (λ a' → Eq.cong (λ e → bind (F _) (inord/cmp b) e) (funext (λ b' → Eq.cong (λ e → bind (F _) (inord/cmp r) e) (funext λ c' → Eq.cong ret (++-assoc a' (x ∷ b') (z ∷ c'))))))) ⟨
--     bind (F (meta⁺ (List ℕ))) (inord/cmp a) (λ a' →
--      bind (F (meta⁺ (List ℕ))) (inord/cmp b) (λ b' →
--         bind (F (meta⁺ (List ℕ))) (inord/cmp r) (λ c' → 
--       ret ((a' ++ x ∷ b') ++ z ∷ c'))))
--   ≡⟨⟩ 
--     bind (F (list nat))
--       (bind (F (list nat)) (inord/cmp a) (λ l' →
--           bind (F (list nat)) (inord/cmp b) (λ r' → ret (l' ++ x ∷ r'))))
--       (λ l' →
--          bind (F (list nat)) (inord/cmp r) (λ r' → ret (l' ++ z ∷ r'))) 
--   ∎
-- <-splayHelper/correct {n₁} {n₂} {i} {i<n₁} z r (zig {n₁₁} {n₁₂} {n₁₃} a x b y c)      = 
--   let open ≡-Reasoning in
--   begin
--     bind {A = splayed (n₁₁ + 1 + n₁₂ + 1 + n₁₃ + 1 + n₂)} (F (list nat)) (<-splayHelper {i = i} {i<n₁ = i<n₁} z r (zig a x b y c)) inord/splayed/cmp
--   -- ≡⟨ Eq.cong (λ e → bind {A = splayed (n₁₁ + 1 + n₁₂ + 1 + n₁₃ + 1 + n₂)} (F (list nat)) e inord/splayed/cmp) refl ⟨
--   ≡⟨ {!  !} ⟩
--     bind {A = splayed (n₁₁ + 1 + (n₁₂ + 1 + (n₁₃ + 1 + n₂)))} (F (list nat))
--       (ret (valid (node a x (node b y (node c z r)))))
--       inord/splayed/cmp
--   ≡⟨⟩
--     bind (F _) (inord/cmp a) (λ a' →
--       bind (F _) (inord/cmp b) (λ b' →
--         bind (F _) (inord/cmp c) (λ c' →
--           bind (F _) (inord/cmp r) (λ r' → 
--             ret (a' ++ x ∷ b' ++ y ∷ c' ++ z ∷ r')))))
--   ≡⟨ Eq.cong (λ e → bind (F _) (inord/cmp a) e) (funext (λ a' →
--           Eq.cong (λ e → bind (F _) (inord/cmp b) e) (funext (λ b' →
--             Eq.cong (λ e → bind (F _) (inord/cmp c) e) (funext (λ c' → 
--               Eq.cong (λ e → bind (F _) (inord/cmp r) e) (funext (λ r' →
--                 Eq.cong ret (++-assoc² a' b' c' r' x y z))))))))) ⟩
--     bind (F _) (inord/cmp a) (λ a' →
--       bind (F _) (inord/cmp b) (λ b' →
--         bind (F _) (inord/cmp c) (λ c' →
--           bind (F _) (inord/cmp r) (λ r' → 
--             ret ((a' ++ x ∷ b' ++ y ∷ c') ++ z ∷ r'))))) 
--   ∎
-- <-splayHelper/correct {n₁} {n₂} {i} {i<n₁} z r (zag {n₁₁} {n₁₂} {n₁₃} a y b x c)      = 
--   let open ≡-Reasoning in
--   begin
--     bind (F (list nat)) (<-splayHelper {i = i} {i<n₁ = i<n₁} z r (zag a y b x c)) inord/splayed/cmp
--   -- ≡⟨ Eq.cong (λ e → bind (F (list nat)) e inord/splayed/cmp) refl ⟩ 
--   ≡⟨ {!   !} ⟩
--     bind {A = splayed ((n₁₁ + 1 + n₁₂) + 1 + (n₁₃ + 1 + n₂))} (F (list nat)) 
--       (ret ((valid (node (node a y b) x (node c z r))))) inord/splayed/cmp
--   ≡⟨⟩
--     bind (F _) (inord/cmp a) (λ a' →
--       bind (F _) (inord/cmp b) (λ b' →
--         bind (F _) (inord/cmp c) (λ c' →
--           bind (F _) (inord/cmp r) (λ r' → 
--             ret ((a' ++ y ∷ b') ++ x ∷ c' ++ z ∷ r')))))
--   ≡⟨ Eq.cong (λ e → bind (F _) (inord/cmp a) e) (funext (λ a' →
--           Eq.cong (λ e → bind (F _) (inord/cmp b) e) (funext (λ b' →
--             Eq.cong (λ e → bind (F _) (inord/cmp c) e) (funext (λ c' → 
--               Eq.cong (λ e → bind (F _) (inord/cmp r) e) (funext (λ r' →
--                 Eq.cong ret (++-assoc³ a' b' c' r' x y z))))))))) ⟩
--     bind (F _) (inord/cmp a) (λ a' →
--       bind (F _) (inord/cmp b) (λ b' →
--         bind (F _) (inord/cmp c) (λ c' →
--           bind (F _) (inord/cmp r) (λ r' → 
--             ret ((a' ++ y ∷ b' ++ x ∷ c') ++ z ∷ r')))))
--   ∎
-- >-splayHelper/correct : {n₁ n₂ i : val nat} {i<n₂ : i < n₂} (z : val nat) (l : Tree n₁) (r : Splayed n₂) → 
--   bind (F (list nat)) (>-splayHelper {i = i} {i<n₂ = i<n₂} z l r) (inord/splayed/cmp {n = n₁ + 1 + n₂}) 
--   ≡
--   bind (F (list nat)) (inord/cmp l) λ l' → bind (F _) (inord/splayed/cmp {n = n₂} r) (λ r' → ret (l' ++ z ∷ [] ++ r'))
-- >-splayHelper/correct {n₁} {n₂} {i} {i<n₂} z l (valid (node a x b)) = refl
-- >-splayHelper/correct {n₁} {n₂} {i} {i<n₂} z l (zig {n₁₁} {n₁₂} {n₁₃} a x b y c) = 
--   let open ≡-Reasoning in
--   begin
--     bind {A = splayed (n₁ + 1 + (n₁₁ + 1 + n₁₂ + 1 + n₁₃))}
--       (F (list nat)) (>-splayHelper {i = i} {i<n₂ = i<n₂} z l (zig {n₁₁} {n₁₂} {n₁₃} a x b y c)) inord/splayed/cmp
--   ≡⟨ {!   !} ⟩
--     bind {A = splayed (n₁ + 1 + n₁₁ + 1 + (n₁₂ + 1 + n₁₃))} (F _) 
--       (ret (valid (node (node l z a) x (node b y c)))) inord/splayed/cmp
--   ≡⟨⟩
--     bind (F _) (inord/cmp l) (λ l' →
--       bind (F _) (inord/cmp a) (λ a' →
--         bind (F _) (inord/cmp b) (λ b' →
--           bind (F _) (inord/cmp c) (λ c' → 
--             ret ((l' ++ z ∷ a') ++ x ∷ b' ++ y ∷ c')))))
--   ≡⟨ Eq.cong (λ e → bind (F _) (inord/cmp l) e) (funext (λ l' →
--           Eq.cong (λ e → bind (F _) (inord/cmp a) e) (funext (λ a' →
--             Eq.cong (λ e → bind (F _) (inord/cmp b) e) (funext (λ b' → 
--               Eq.cong (λ e → bind (F _) (inord/cmp c) e) (funext (λ c' →
--                 Eq.cong ret (++-assoc l' (z ∷ a') (x ∷ b' ++ y ∷ c')))))))))) ⟩
--     bind (F _) (inord/cmp l) (λ l' →
--       bind (F _) (inord/cmp a) (λ a' →
--         bind (F _) (inord/cmp b) (λ b' →
--           bind (F _) (inord/cmp c) (λ c' → 
--             ret (l' ++ z ∷ a' ++ x ∷ b' ++ y ∷ c')))))
--   ∎
-- >-splayHelper/correct {n₁} {n₂} {i} {i<n₂} z l (zag {n₁₁} {n₁₂} {n₁₃} a y b x c) = 
--   let open ≡-Reasoning in
--   begin
--     bind (F (list nat)) (>-splayHelper {i = i} {i<n₂ = i<n₂} z l (zag a y b x c)) inord/splayed/cmp
--   ≡⟨ {!   !} ⟩
--     bind {A = splayed (((n₁ + 1 + n₁₁) + 1 + n₁₂) + 1 + n₁₃)} (F _) 
--       (ret (valid ((node (node (node l z a) y b) x c)))) inord/splayed/cmp
--   ≡⟨⟩
--     bind (F (list nat)) (inord/cmp l) (λ l' →
--       bind (F (list nat)) (inord/cmp a) (λ a' →
--         bind (F (list nat)) (inord/cmp b) (λ b' →
--           bind (F (list nat)) (inord/cmp c) (λ c' → 
--             ret (((l' ++ z ∷ a') ++ y ∷ b') ++ x ∷ c')))))
--             -- ++-assoc⁴ l a b c z x y
--   ≡⟨ Eq.cong (λ e → bind (F _) (inord/cmp l) e) (funext (λ l' →
--           Eq.cong (λ e → bind (F _) (inord/cmp a) e) (funext (λ a' →
--             Eq.cong (λ e → bind (F _) (inord/cmp b) e) (funext (λ b' → 
--               Eq.cong (λ e → bind (F _) (inord/cmp c) e) (funext (λ c' →
--                 Eq.cong ret (++-assoc⁴ l' a' b' c' z x y))))))))) ⟩
--     bind (F (list nat)) (inord/cmp l) (λ l' →
--       bind (F (list nat)) (inord/cmp a) (λ a' →
--         bind (F (list nat)) (inord/cmp b) (λ b' →
--           bind (F (list nat)) (inord/cmp c) (λ c' → 
--             ret (l' ++ z ∷ a' ++ y ∷ b' ++ x ∷ c')))))
--   ∎

-- -- let
-- --   arithmetic : i ∸ (n₁ + 1) Nat.< n₂
-- --   arithmetic = let open Nat.≤-Reasoning in 
-- --     Nat.+-cancelˡ-< (n₁ + 1) (i ∸ (n₁ + 1)) n₂ (
-- --       begin-strict
-- --         (n₁ + 1) + (i ∸ (n₁ + 1))
-- --       ≡⟨ Nat.m+[n∸m]≡n (Eq.subst (i Nat.≥_) (Nat.+-comm 1 n₁) i≥n₁+1) ⟩ 
-- --         i
-- --       <⟨ i<n ⟩
-- --         n₁ + 1 + n₂
-- --       ∎
-- --     )
-- -- in bind (F (splayed _)) (splay r (i ∸ (n₁ + 1)) arithmetic) (>-splayHelper {i = i ∸ (n₁ + 1)} {i<n₂ = arithmetic} z l)

-- splay/correct : {n : val nat} → (t : Tree n) (i : val nat) (i<n : i < n) → 
--   bind (F (list nat)) (splay t i i<n) inord/splayed/cmp ≡ inord/cmp t
-- splay/correct {n} (node {n₁} {n₂} l z r) i i<n with <-cmp i n₁ 
-- ... | tri< i<n₁ _ _ = 
--   let open ≡-Reasoning in
--   begin 
--     bind (F _) (splay l i i<n₁) (λ l →
--          bind (F _) (<-splayHelper z r l) (inord/splayed/cmp))
--   ≡⟨ Eq.cong (bind (F _) (splay l i i<n₁)) (funext (λ l →  <-splayHelper/correct z r l)) ⟩ 
--     bind (F _) (splay l i i<n₁) (λ l →
--          bind (F (list nat)) (inord/splayed/cmp {n = n₁} l) λ l' → bind (F _) (inord/cmp r) (λ r' → ret (l' ++ z ∷ [] ++ r')))
--   ≡⟨⟩ 
--     bind (F _) (
--       bind (F _) (splay l i i<n₁) (inord/splayed/cmp {n = n₁})
--     )
--     (λ l' → bind (F _) (inord/cmp r) (λ r' → ret (l' ++ z ∷ [] ++ r')))
--   ≡⟨ Eq.cong (λ e → bind (F _) e (λ l' → bind (F _) (inord/cmp r) (λ r' → ret (l' ++ z ∷ [] ++ r')))) (splay/correct l i i<n₁) ⟩ 
--    bind (F _) (inord/cmp l) (λ l' → 
--     bind (F _) (inord/cmp r) (λ r' → 
--       ret (l' ++ z ∷ [] ++ r')))
--   ∎
-- ... | tri≈ ¬a b ¬c = refl
-- ... | tri> ¬a ¬b c = {!   !}

-- splayTopLevelHelper/correct : {n i : val nat} {i<n : i < n} {t : Splayed n} → 
--   bind (F _) (splayTopLevelHelper {n} {i} {i<n} t) (λ e → inord/cmp (proj₂ (proj₂ e)))
--   ≡ 
--   inord/splayed/cmp t 
-- splayTopLevelHelper/correct {n} {i} {i<n} {t = valid (node {n₁} {n₂} l z r)} = refl
-- splayTopLevelHelper/correct {t = zig {n₁₁} {n₁₂} {n₁₃} a x b y c} = 
--   let open ≡-Reasoning in
--   begin
--     inord/cmp (node (node a x b) y c)
--   ≡⟨⟩
--     bind (F _) (inord/cmp a) (λ a' →
--       bind (F _) (inord/cmp b) (λ b' →
--         bind (F _) (inord/cmp c) (λ c' → 
--           ret ((a' ++ x ∷ b') ++ y ∷ c'))))
--   ≡⟨ Eq.cong (λ e → bind (F _) (inord/cmp a) e) (funext (λ a' →
--           Eq.cong (λ e → bind (F _) (inord/cmp b) e) (funext (λ b' →
--             Eq.cong (λ e → bind (F _) (inord/cmp c) e) (funext (λ c' → 
--               Eq.cong ret (++-assoc a' (x ∷ b') (y ∷ c')))))))) ⟩
--     bind (F _) (inord/cmp a) (λ a' →
--       bind (F _) (inord/cmp b) (λ b' →
--         bind (F _) (inord/cmp c) (λ c' → 
--           ret (a' ++ x ∷ b' ++ y ∷ c'))))
--   ∎
-- splayTopLevelHelper/correct {t = zag {n₁₁} {n₁₂} {n₁₃} a y b x c} = refl

-- open BST renaming (splay to splay')

-- record BSTHom (bst bst' : BST) : Set where
--   field
--     ϕ : cmp (Π (bst .T) λ _ → F (bst' .T))
--     ϕ/splay : (t : val (bst .T)) (i : val nat) → 
--        bind (F _) (bst .splay' t i) (λ { (_ , t') → ϕ t'})
--       -- ≤⁻[ F (bst' .T) ]
--       ≡
--         ϕ t
        
-- open BSTHom

-- ST⇒LT : BSTHom SplayTree ListTree
-- ST⇒LT .ϕ (n , t) = inord/cmp t
-- ST⇒LT .ϕ/splay (n , t) i with <-cmp i n
-- ... | tri< a ¬b ¬c = {!   !}
-- ... | tri≈ ¬a b ¬c = {!   !}
-- ... | tri> ¬a ¬b c = {!   !}