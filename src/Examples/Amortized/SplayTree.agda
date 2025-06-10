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

ListTree : BST
ListTree .BST.T = list nat
ListTree .BST.splay l i with i <? length l 
... | yes p = let finIdx = fromℕ< p in ret (lookup l finIdx , l)
... | no _ = ret (0 , l)

variable
  n n' n₁ n₂ n₃ : val nat

data Tree : ℕ -> Set where
  leaf : Tree 0
  node : Tree n₁ → val nat → Tree n₂ → Tree (n₁ + 1 + n₂)

tree : tp⁺
tree = Σ⁺ nat (λ n → meta⁺ (Tree n))

data Splayed : ℕ → Set where
  valid : (t : Tree n) → Splayed n 
  zig :   (a : Tree n₁) (x : val nat) (b : Tree n₂) (y : val nat) (c : Tree n₃) → Splayed ((n₁ + 1 + n₂) + 1 + n₃)
  zag :   (a : Tree n₁) (y : val nat) (b : Tree n₂) (x : val nat) (c : Tree n₃) → Splayed (n₁ + 1 + (n₂ + 1 + n₃))

splayed : val nat → tp⁺
splayed n = meta⁺ (Splayed n)

test : (x y z : ℕ) → ((x + y) + z) ≡ (x + (y + z))
test x y z = Nat.+-assoc x y z

zig-arithmetic1 : (n₁₁ n₁₂ n₁₃ n₂ : val nat) → n₁₁ + 1 + (n₁₂ + 1 + (n₁₃ + 1 + n₂)) ≡ n₁₁ + 1 + n₁₂ + 1 + n₁₃ + 1 + n₂
zig-arithmetic1 n₁₁ n₁₂ n₁₃ n₂ = 
  let open ≡-Reasoning in
  begin
    (n₁₁ + 1) + ((n₁₂ + 1) + (n₁₃ + 1 + n₂)) 
  ≡⟨ Nat.+-assoc (n₁₁ + 1) (n₁₂ + 1) (n₁₃ + 1 + n₂) ⟨
    ((n₁₁ + 1) + (n₁₂ + 1)) + (n₁₃ + 1 + n₂)
  ≡⟨ Eq.cong (λ e → e + (n₁₃ + 1 + n₂)) (Nat.+-assoc (n₁₁ + 1) n₁₂ 1) ⟨
    (n₁₁ + 1 + n₁₂ + 1) + ((n₁₃ + 1) + n₂)
  ≡⟨ Nat.+-assoc (n₁₁ + 1 + n₁₂ + 1) (n₁₃ + 1) (n₂) ⟨
    ((n₁₁ + 1 + n₁₂ + 1) + (n₁₃ + 1)) + n₂
  ≡⟨ Eq.cong (λ e → e + n₂) (Nat.+-assoc (n₁₁ + 1 + n₁₂ + 1) n₁₃ 1) ⟨
    (n₁₁ + 1 + n₁₂ + 1 + n₁₃ + 1) + n₂
  ≡⟨⟩
    n₁₁ + 1 + n₁₂ + 1 + n₁₃ + 1 + n₂
  ∎

splayHelper : {n₁ n₂ i : val nat} {i<n₁ : i < n₁} (z : val nat) (r : Tree n₂) → Splayed n₁ → cmp (F (splayed (n₁ + 1 + n₂)))
splayHelper z r (valid (node a x b)) = ret (zig a x b z r)
splayHelper z r (zig {n₁₁} {n₁₂} {n₁₃} a x b y c) = 
  let
    arithmetic : n₁₁ + 1 + (n₁₂ + 1 + (n₁₃ + 1 + n₂)) ≡ n₁₁ + 1 + n₁₂ + 1 + n₁₃ + 1 + n₂
    arithmetic {n₂} = let open ≡-Reasoning in begin
          (n₁₁ + 1) + ((n₁₂ + 1) + (n₁₃ + 1 + n₂)) 
        ≡⟨ Nat.+-assoc (n₁₁ + 1) (n₁₂ + 1) (n₁₃ + 1 + n₂) ⟨
          ((n₁₁ + 1) + (n₁₂ + 1)) + (n₁₃ + 1 + n₂)
        ≡⟨ Eq.cong (λ e → e + (n₁₃ + 1 + n₂)) (Nat.+-assoc (n₁₁ + 1) n₁₂ 1) ⟨
          (n₁₁ + 1 + n₁₂ + 1) + ((n₁₃ + 1) + n₂)
        ≡⟨ Nat.+-assoc (n₁₁ + 1 + n₁₂ + 1) (n₁₃ + 1) (n₂) ⟨
          ((n₁₁ + 1 + n₁₂ + 1) + (n₁₃ + 1)) + n₂
        ≡⟨ Eq.cong (λ e → e + n₂) (Nat.+-assoc (n₁₁ + 1 + n₁₂ + 1) n₁₃ 1) ⟨
          (n₁₁ + 1 + n₁₂ + 1 + n₁₃ + 1) + n₂
        ≡⟨⟩
          n₁₁ + 1 + n₁₂ + 1 + n₁₃ + 1 + n₂
        ∎
  in
  ret (valid (Eq.subst Tree arithmetic (node a x (node b y (node c z r))))) 
splayHelper z r (zag {n₁₁} {n₁₂} {n₁₃} a y b x c) = 
  let
    arithmetic : n₁₁ + 1 + n₁₂ + 1 + (n₁₃ + 1 + n₂) ≡ n₁₁ + 1 + (n₁₂ + 1 + n₁₃) + 1 + n₂
    arithmetic = solve Nat.+-0-monoid
  in
  ret (valid (Eq.subst Tree arithmetic (node (node a y b) x (node c z r)))) 


splay : {n : ℕ} → Tree n → (i : val nat) → i < n → cmp (F (splayed n))
splay (node {n₁} {n₂} l z r) i i<n with <-cmp i n₁ 
... | tri< i<n₁ _ _ = bind (F (splayed _)) (splay l i i<n₁) (splayHelper {i = i} {i<n₁ = i<n₁} z r)
... | tri≈ _ i=n₁ _ = ret (valid (node l z r)) 
... | tri> _ _ i≥n₁+1 = 
  let
    arithmetic : i ∸ (n₁ + 1) Nat.< n₂
    arithmetic = let open Nat.≤-Reasoning in 
      Nat.+-cancelˡ-< (n₁ + 1) (i ∸ (n₁ + 1)) n₂ (
        begin-strict
          (n₁ + 1) + (i ∸ (n₁ + 1))
        ≡⟨ Nat.m+[n∸m]≡n (Eq.subst (i Nat.≥_) (Nat.+-comm 1 n₁) i≥n₁+1) ⟩ 
          i
        <⟨ i<n ⟩
          n₁ + 1 + n₂
        ∎
      )
  in
  bind ((F (splayed _))) (splay r (i ∸ (n₁ + 1)) arithmetic) λ 
    { (valid leaf) → Relation.Nullary.contradiction arithmetic Nat.n≮0
    ; (valid (node a x b)) → ret (zag l z a x b)
    ; (zig {n₁₁} {n₁₂} {n₁₃} a x b y c) → 
        let
          arithmetic : n₁ + 1 + n₁₁ + 1 + (n₁₂ + 1 + n₁₃) ≡ n₁ + 1 + (n₁₁ + 1 + n₁₂ + 1 + n₁₃)
          arithmetic = solve Nat.+-0-monoid
        in
        ret (valid (Eq.subst Tree arithmetic (node (node l z a) x (node b y c))))
    ; (zag {n₁₁} {n₁₂} {n₁₃} a y b x c) → 
      let
        arithmetic : n₁ + 1 + n₁₁ + 1 + n₁₂ + 1 + n₁₃ ≡ n₁ + 1 + (n₁₁ + 1 + (n₁₂ + 1 + n₁₃))
        arithmetic = solve Nat.+-0-monoid
      in
      ret (valid (Eq.subst Tree arithmetic (node (node (node l z a) y b) x c))) 
    }

splayTopLevelHelper : {n i : val nat} {i<n : i < n} → Splayed n → cmp (F (meta⁺ (Σ ℕ (λ x → Σ ℕ Tree))))
splayTopLevelHelper {n} (valid (node l z r)) = ret (z , (n , node l z r))
splayTopLevelHelper {n} (zig a x b y c) = ret (y , (n , node (node a x b) y c))
splayTopLevelHelper {n} (zag a y b x c) = ret (y , (n , node a y (node b x c)))


-- bind (F (meta⁺ (List ℕ))) (splay t i a)
--       (λ a₁ →
--          bind (F (meta⁺ (List ℕ))) (splayTopLevelHelper a₁)
--          (λ z →
--             -- inord/cmp (Agda.Builtin.Sigma.Σ.snd (Agda.Builtin.Sigma.Σ.snd z))))

SplayTree : BST
SplayTree .BST.T = tree
SplayTree .BST.splay (n , t) i with <-cmp i n
... | tri< i<n _ _ = bind (F _) (splay t i i<n) (splayTopLevelHelper {n} {i} {i<n})
... | tri≈ _ _ _ = ret (0 , (0 , leaf))
... | tri> _ _ _ = ret (0 , (0 , leaf))

open BST renaming (splay to splay')

record BSTHom (bst bst' : BST) : Set where
  field
    ϕ : cmp (Π (bst .T) λ _ → F (bst' .T))
    ϕ/splay : (t : val (bst .T)) (i : val nat) → 
       bind (F _) (bst .splay' t i) (λ { (_ , t') → ϕ t'})
      -- ≤⁻[ F (bst' .T) ]
      ≡
        ϕ t
      

open BSTHom

inord : {n : ℕ} → Tree n → val (list nat)
inord leaf = []
inord (node l z r) = (inord l) ++ (z ∷ []) ++ (inord r)

inord/cmp : {n : val nat} → cmp (Π (meta⁺ (Tree n)) λ _ → F (list nat))
inord/cmp {n} leaf = ret []
inord/cmp {n} (node l z r) = 
  bind (F _) (inord/cmp l) (λ l' → 
  bind (F _) (inord/cmp r) (λ r' → ret (l' ++ z ∷ [] ++ r')))

inord/correct : {n : val nat} {t : Tree n} → length (inord t) ≡ n
inord/correct {n} {leaf} = refl
inord/correct {n} {node {n₁} {n₂} t₁ x t₂} = 
  let open ≡-Reasoning in
  begin 
    length (inord t₁ ++ x ∷ inord t₂)
  ≡⟨ length-++ {A = val nat} (inord t₁) ⟩ 
    length (inord t₁) + length (x ∷ inord t₂)
  ≡⟨⟩ 
    length (inord t₁) + (1 + length (inord t₂))
  ≡⟨ Eq.cong₂ _+_ (inord/correct {t = t₁}) (Eq.cong (1 +_) (inord/correct {t = t₂})) ⟩ 
    n₁ + (1 + n₂)
  ≡⟨ +-assoc n₁ 1 n₂ ⟨ 
    n₁ + 1 + n₂
  ∎

inord/splayed : {n : val nat} → val (splayed n) → val (list nat)
inord/splayed (valid t)       = inord t
inord/splayed (zig a x b y c) = inord a ++ x ∷ [] ++ inord b ++ y ∷ [] ++ inord c
inord/splayed (zag a y b x c) = inord a ++ y ∷ [] ++ inord b ++ x ∷ [] ++ inord c

inord/splayed/cmp : {n : val nat} → cmp (Π (splayed n) λ _ → F (list nat))
inord/splayed/cmp {n} (valid t)       = inord/cmp t
inord/splayed/cmp {n} (zig a x b y c) = 
  bind (F _) (inord/cmp a) (λ a' → 
  bind (F _) (inord/cmp b) (λ b' → 
  bind (F _) (inord/cmp c) λ c' → 
    ret (a' ++ x ∷ [] ++ b' ++ y ∷ [] ++ c')))
inord/splayed/cmp {n} (zag a y b x c) = 
  bind (F _) (inord/cmp a) (λ a' → 
  bind (F _) (inord/cmp b) (λ b' → 
  bind (F _) (inord/cmp c) λ c' → 
    ret (a' ++ y ∷ [] ++ b' ++ x ∷ [] ++ c')))

-- inord/splayed/correct : {n : val nat} {t : val (splayed n)} → length (inord/splayed t) ≡ n
-- inord/splayed/correct {n} {valid t} = inord/correct {t = t}
-- inord/splayed/correct {n} {zig {n₁₁} {n₁₂} {n₁₃} a x b y c} = inord/correct {n = n} {t = {!   !}}
-- inord/splayed/correct {n} {zag a y b x c} = {!   !}


splayHelper/correct : {n₁ n₂ i : val nat} {i<n₁ : i < n₁} (z : val nat) (r : Tree n₂) (l : Splayed n₁)→ 
  bind (F (list nat)) (splayHelper {i = i} {i<n₁ = i<n₁} z r l) (inord/splayed/cmp {n = n₁ + 1 + n₂}) 
  ≡
  bind (F (list nat)) (inord/splayed/cmp {n = n₁} l) λ l' → bind (F _) (inord/cmp r) (λ r' → ret (l' ++ z ∷ [] ++ r'))
splayHelper/correct {n₁} {n₂} z r (valid (node a x b)) = 
  let open ≡-Reasoning in
  begin 
     bind (F _) (inord/cmp a) (λ a' → 
     bind (F _) (inord/cmp b) (λ b' → 
     bind (F _) (inord/cmp r) λ c' → 
       ret (a' ++ x ∷ [] ++ b' ++ z ∷ [] ++ c')))
  ≡⟨ Eq.cong (λ e → bind (F _) (inord/cmp a) e) (funext (λ a' → Eq.cong (λ e → bind (F _) (inord/cmp b) e) (funext (λ b' → Eq.cong (λ e → bind (F _) (inord/cmp r) e) (funext λ c' → Eq.cong ret (++-assoc a' (x ∷ b') (z ∷ c'))))))) ⟨
    bind (F (meta⁺ (List ℕ))) (inord/cmp a) (λ a' →
     bind (F (meta⁺ (List ℕ))) (inord/cmp b) (λ b' →
        bind (F (meta⁺ (List ℕ))) (inord/cmp r) (λ c' → 
      ret ((a' ++ x ∷ b') ++ z ∷ c'))))
  ≡⟨⟩ 
    bind (F (list nat))
      (bind (F (list nat)) (inord/cmp a) (λ l' →
          bind (F (list nat)) (inord/cmp b) (λ r' → ret (l' ++ x ∷ r'))))
      (λ l' →
         bind (F (list nat)) (inord/cmp r) (λ r' → ret (l' ++ z ∷ r'))) 
  ∎
splayHelper/correct {n₁} {n₂} {i} {i<n₁} z r (zig {n₁₁} {n₁₂} {n₁₃} a x b y c)      = 
  let open ≡-Reasoning in
  begin
    bind (F (list nat)) (splayHelper {i = i} {i<n₁ = i<n₁} z r (zig a x b y c)) inord/splayed/cmp
  ≡⟨ Eq.cong (λ t → bind {A = splayed _} (F (list nat)) (ret (valid t)) inord/splayed/cmp) {!   !} ⟩
    bind {A = splayed _} (F (list nat))
      (ret (valid (node a x (node b y (node c z r)))))
      inord/splayed/cmp
  ≡⟨ {!   !} ⟩
      bind (F (list nat))
      (bind (F (list nat)) (inord/cmp a)
       (λ a' →
          bind (F (list nat)) (inord/cmp b)
          (λ b' →
             bind (F (list nat)) (inord/cmp c)
             (λ c' → ret (a' ++ x ∷ b' ++ y ∷ c')))))
      (λ l' →
         bind (F (list nat)) (inord/cmp r) (λ r' → ret (l' ++ z ∷ r')))
  ∎
  -- let open ≡-Reasoning in
  -- begin
  --   bind (F (list nat)) (splayHelper {i = i} {i<n₁ = i<n₁} z r (zig a x b y c)) inord/splayed/cmp
  -- ≡⟨⟩
  --   bind (F _) (inord/cmp a)
  --     (λ a' →
  --        bind (F _) (inord/cmp b)
  --        (λ b' →
  --           bind (F _) (inord/cmp c)
  --           (λ c' →
  --              bind (F _) (inord/cmp r)
  --              (λ r' → ret (a' ++ x ∷ b' ++ y ∷ c' ++ z ∷ r')))))
  -- ≡⟨ Eq.cong (λ e → bind (F _) (inord/cmp a) e) (funext (λ a' →
  --         Eq.cong (λ e → bind (F _) (inord/cmp b) e) (funext (λ b' →
  --           Eq.cong (λ e → bind (F _) (inord/cmp c) e) (funext (λ c' → 
  --             Eq.cong (λ e → bind (F _) (inord/cmp r) e) (funext (λ r' →
  --               Eq.cong ret {x = {! !}} {!   !})))))))) ⟨
  --   bind (F _) (inord/cmp a)
  --     (λ a' →
  --        bind (F (meta⁺ (List ℕ))) (inord/cmp b)
  --        (λ b' →
  --           bind (F (meta⁺ (List ℕ))) (inord/cmp c)
  --           (λ c' →
  --              bind (F (meta⁺ (List ℕ))) (inord/cmp r)
  --              (λ r' → ret ((a' ++ x ∷ b' ++ y ∷ c') ++ z ∷ r')))))
  -- ∎
splayHelper/correct {n₁} {n₂} z r (zag a y b x c)      = {!   !}

splay/correct : {n : val nat} → (t : Tree n) (i : val nat) (i<n : i < n) → 
  bind (F (list nat)) (splay t i i<n) inord/splayed/cmp ≡ inord/cmp t
splay/correct {n} (node {n₁} {n₂} l z r) i i<n with <-cmp i n₁ 
... | tri< i<n₁ _ _ = 
  let open ≡-Reasoning in
  begin 
    bind (F _) (splay l i i<n₁) (λ l →
         bind (F _) (splayHelper z r l) (inord/splayed/cmp))
  ≡⟨ Eq.cong (bind (F _) (splay l i i<n₁)) (funext (λ l →  splayHelper/correct z r l)) ⟩ 
    bind (F _) (splay l i i<n₁) (λ l →
         bind (F (list nat)) (inord/splayed/cmp {n = n₁} l) λ l' → bind (F _) (inord/cmp r) (λ r' → ret (l' ++ z ∷ [] ++ r')))
  ≡⟨⟩ 
    bind (F _) (
      bind (F _) (splay l i i<n₁) (inord/splayed/cmp {n = n₁})
    )
    (λ l' → bind (F _) (inord/cmp r) (λ r' → ret (l' ++ z ∷ [] ++ r')))
  ≡⟨ Eq.cong (λ e → bind (F _) e (λ l' → bind (F _) (inord/cmp r) (λ r' → ret (l' ++ z ∷ [] ++ r')))) (splay/correct l i i<n₁) ⟩ 
   bind (F _) (inord/cmp l) (λ l' → 
    bind (F _) (inord/cmp r) (λ r' → 
      ret (l' ++ z ∷ [] ++ r')))
  ∎
... | tri≈ ¬a b ¬c = {!   !}
... | tri> ¬a ¬b c = {!   !}

splayTopLevelHelper/correct : {n i : val nat} {i<n : i < n} {t : Splayed n} → 
  bind (F _) (splayTopLevelHelper {n} {i} {i<n} t) (λ z → inord/cmp (proj₂ (proj₂ z)))
  ≡ 
  inord/splayed/cmp t 
splayTopLevelHelper/correct = {!   !}

ST⇒LT : BSTHom SplayTree ListTree
ST⇒LT .ϕ (n , t) = inord/cmp t
ST⇒LT .ϕ/splay (n , t) i with <-cmp i n
... | tri< a ¬b ¬c = {!   !}
... | tri≈ ¬a b ¬c = {!   !}
... | tri> ¬a ¬b c = {!   !}