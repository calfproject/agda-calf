{-# OPTIONS --rewriting --allow-unsolved-metas #-}

module Examples.Amortized.SplayTree.LaxHom where

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

open import Relation.Binary 
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≢_; refl; module ≡-Reasoning)

open import Data.Nat.Logarithm
open import Data.Empty using (⊥; ⊥-elim)

open import Examples.Amortized.SplayTree.Prelude
open import Examples.Amortized.SplayTree.SplayTree
open import Examples.Amortized.SplayTree.AccessPrepare
open import Examples.Amortized.SplayTree.Access

open BST

record BSTHom (bst bst' : BST) : Set where
  field 
    ϕ : cmp (Π (bst .T) λ _ → F (bst' .T))
    ϕ/fromList : (l : val (list nat)) → 
        bind (F _) (bst .fromList l) ϕ
      ≤⁻[ F (bst' .T) ]
        bst' .fromList l
    ϕ/size : (t : val (bst .T)) → 
        bind (F _) (bst .size t) ret
      ≤⁻[ F (nat) ]
        bind (F _) (ϕ t) (λ t' → bst' .size t')
    ϕ/find : (t : val (bst .T)) (k : val nat) → 
        bind (F _) (bst .find t k) (λ (_ , t') → ϕ t')
      ≤⁻[ F (bst' .T) ]
        bind (F _) (ϕ t) (λ t' → bind (F _) (bst' .find t' k) (λ (_ , t'') → ret t''))
    ϕ/total : (t : val (bst .T)) →
        ret triv
      ≤⁻[ F unit ]
        bind (F _) (ϕ t) (λ _ → ret triv)

open BSTHom

ST⇒LT : BSTHom SplayTree ListTree
ST⇒LT .ϕ = φ
ST⇒LT .ϕ/fromList l = 
  let 
    l' = sort/val (deduplicate Nat._≟_ l)
    t  = makeTree/nodups/sorted leaf l'
  in
  let open ≤⁻-Reasoning (F _) in
  begin
    bind (F _) (ret {A = tree} t) φ
  ≡⟨⟩ 
    step (F _) (sum-of-ranks t) (ret (inord t))
  ≲⟨ step-monoˡ-≤⁻ (ret (inord t)) (sum-of-ranks/bound t) ⟩
    step (F _) (tree-size t * ⌊log₂ (tree-size t) ⌋) (ret (inord t))
  ≡⟨ Eq.cong (λ e → step (F _) (e * ⌊log₂ e ⌋) (ret (inord t))) (tree-size/inord/lemma t) ⟩
    step (F _) ((length (inord t)) * ⌊log₂ (length (inord t)) ⌋) (ret (inord t))
  ≡⟨ Eq.cong (λ e → step (F _) ((length e) * ⌊log₂ (length e) ⌋) (ret e)) (makeTree/inord/lemma leaf l') ⟩
    step (F _) (length l' * ⌊log₂ (length l') ⌋) (ret l')
  ∎
ST⇒LT .ϕ/size t = 
  let open ≤⁻-Reasoning (F _) in
  begin
    ret (tree-size t)
  ≡⟨ Eq.cong (λ e → ret e) (tree-size/inord/lemma t) ⟩
    ret (length (inord t))
  ≡⟨⟩
    step (F (nat)) 0 (ret (length (inord t))) 
  ≲⟨ step-monoˡ-≤⁻ {c' = sum-of-ranks t} (ret (length (inord t))) z≤n ⟩
    step (F (nat)) (sum-of-ranks t) (ret (length (inord t)))
  ∎
ST⇒LT .ϕ/find t k with (search t k []) 
... | ((false , t' , anc) , _ , _ , _) = 
  let open ≤⁻-Reasoning (F _) in
  begin
    step (F _) (sum-of-ranks t) (ret (inord t))
  ≲⟨ step-monoˡ-≤⁻ (ret (inord t)) (Nat.m≤n+m (sum-of-ranks t) ((3 * ⌊log₂ (length (inord t))⌋) + 1)) ⟩
    step (F _) (((3 * ⌊log₂ (length (inord t))⌋) + 1) + sum-of-ranks t) 
      (ret (inord t))
  ≡⟨ Eq.cong (λ e → step (F _) e (ret (inord t))) (Nat.+-comm ((3 * ⌊log₂ (length (inord t))⌋) + 1) (sum-of-ranks t)) ⟩
    step (F _) (sum-of-ranks t + ((3 * ⌊log₂ (length (inord t))⌋) + 1)) 
      (ret (inord t))
  ≡⟨ Eq.cong (λ e → step (F _) (sum-of-ranks t + ((3 * ⌊log₂ (length (inord t))⌋) + 1)) e) (list/find/bind/lemma (inord t) k) ⟨
    step (F _) (sum-of-ranks t + ((3 * ⌊log₂ (length (inord t))⌋) + 1)) 
      (bind (F _) (listFind (inord t) k) (λ _ → ret (inord t)))
  ∎
... | ((true , leaf , anc) , _ , 0<0 , _) = ⊥-elim (Nat.<-irrefl refl (0<0 refl))
... | ((true , node l x r , anc) , t≡recon , _ , x≡k) = 
  let open ≤⁻-Reasoning (F _) in
  begin
    bind (F (list nat)) (bind (F (bool ×⁺ tree)) (splay' l r anc k) (λ ((l' , r') , _) → 
      ret (true , node l' x r'))) (λ (_ , t') → ST⇒LT .ϕ t')
  ≡⟨⟩
    bind (F _) (splay' l r anc k) (λ ((l' , r') , _) → ST⇒LT .ϕ (node l' x r'))
  ≡⟨ Eq.cong (λ e → bind (F _) (splay' l r anc k) e) (funext λ ((l' , r') , _) → 
      Eq.cong (λ e → ST⇒LT .ϕ (node l' e r')) (x≡k refl)) ⟩
    bind (F _) (splay' l r anc k) (λ ((l' , r') , _) → ST⇒LT .ϕ (node l' k r'))
  ≲⟨ splay'/amortized l r anc k ⟩
    step (F _) (1 + 3 * (rank (reconstruct (node l k r) anc) ∸ rank (node l k r))) (φ (reconstruct (node l k r) anc))
  ≲⟨ step-monoˡ-≤⁻ (φ (reconstruct (node l k r) anc)) (Nat.+-monoʳ-≤ 1 (Nat.*-monoʳ-≤ 3 
      (Nat.m∸n≤m (rank (reconstruct (node l k r) anc)) (rank (node l k r))))) ⟩
    step (F _) (1 + 3 * (rank (reconstruct (node l k r) anc))) (φ (reconstruct (node l k r) anc))
  ≡⟨ Eq.cong₂ (λ e₁ → λ e₂ → step (F _) e₁ e₂) 
      (Eq.cong (λ e → 1 + 3 * (rank (reconstruct (node l e r) anc))) (x≡k refl)) 
        (Eq.cong (λ e → φ (reconstruct (node l e r) anc)) (x≡k refl)) ⟨
    step (F _) (1 + 3 * (rank (reconstruct (node l x r) anc))) (φ (reconstruct (node l x r) anc))
  ≡⟨ Eq.cong₂ (λ e₁ → λ e₂ → step (F _) e₁ e₂) 
      (Eq.cong (λ e → 1 + 3 * (rank e)) t≡recon) 
        (Eq.cong (λ e → φ e) t≡recon) ⟨
    step (F _) (1 + 3 * (rank t)) (φ t)
  ≡⟨⟩
    step (F _) (1 + 3 * (rank t)) (step (F _) (sum-of-ranks t) (ret (inord t)))
  ≡⟨⟩
    step (F _) ((1 + 3 * (rank t)) + sum-of-ranks t) (ret (inord t))
  ≡⟨ Eq.cong (λ e → step (F _) e (ret (inord t))) (Nat.+-comm (1 + 3 * (rank t)) (sum-of-ranks t)) ⟩
    step (F _) (sum-of-ranks t + (1 + 3 * (rank t))) (ret (inord t))
  ≡⟨ Eq.cong (λ e → step (F _) (sum-of-ranks t + e) (ret (inord t))) (Nat.+-comm 1 (3 * (rank t))) ⟩
    step (F _) (sum-of-ranks t + ((3 * (rank t)) + 1)) (ret (inord t))
  ≡⟨⟩
    step (F _) (sum-of-ranks t + ((3 * ⌊log₂ (tree-size t)⌋) + 1)) 
      (ret (inord t))
  ≡⟨ Eq.cong (λ e → step (F _) (sum-of-ranks t + ((3 * ⌊log₂ e ⌋) + 1)) (ret (inord t))) 
      (tree-size/inord/lemma t) ⟩
    step (F _) (sum-of-ranks t + ((3 * ⌊log₂ (length (inord t))⌋) + 1)) 
      (ret (inord t))
  ≡⟨ Eq.cong (λ e → step (F _) (sum-of-ranks t + ((3 * ⌊log₂ (length (inord t))⌋) + 1)) e) (list/find/bind/lemma (inord t) k) ⟨
    step (F _) (sum-of-ranks t + ((3 * ⌊log₂ (length (inord t))⌋) + 1)) 
      (bind (F _) (listFind (inord t) k) (λ _ → ret (inord t)))
  ∎
ST⇒LT .ϕ/total t = step-monoˡ-≤⁻ {c' = sum-of-ranks t} (ret triv) z≤n

data BSTOperation : Set where
  findKey : val nat → BSTOperation

apply : BSTOperation → (t : BST) → val (t .T) → cmp (F (t .T))
apply (findKey k) bst t = bind (F _) (bst .find t k) (λ (_ , t') → ret t')

fold-apply : (ops : List BSTOperation) → (bst : BST) → (t : val (bst .T)) → cmp (F (bst .T))
fold-apply [] bst t = ret t
fold-apply (op ∷ ops) bst t = 
  bind (F _) (fold-apply ops bst t) (λ t' → 
    bind (F _) (apply op bst t') ret)

commutes : (ops : List BSTOperation) → (t : val (SplayTree .T)) → 
    bind (F _) (fold-apply ops SplayTree t) (ST⇒LT .ϕ)
  ≤⁻[ F (ListTree .T) ]
    bind (F _) (ST⇒LT .ϕ t) (λ t' → fold-apply ops ListTree t')
commutes [] t = ≤⁻-refl
commutes (findKey k ∷ ops) t = 
  let open ≤⁻-Reasoning (F _) in 
  begin 
    bind (F _) (fold-apply ops SplayTree t) (λ t' → 
      bind (F _) (SplayTree .find t' k) (λ (_ , t'') → ST⇒LT .ϕ t''))
  ≲⟨ bind-monoʳ-≤⁻ (fold-apply ops SplayTree t) (λ t' → ST⇒LT .ϕ/find t' k) ⟩
    bind (F _) (fold-apply ops SplayTree t) (λ t' → 
      bind (F _) (ST⇒LT .ϕ t') (λ t'' → 
        bind (F _) (ListTree .find t'' k) (λ (_ , t''') → ret t''')))
  ≡⟨⟩
    bind (F _) (bind (F _) (fold-apply ops SplayTree t) (ST⇒LT .ϕ)) (λ t' → 
      bind (F _) (ListTree .find t' k) (λ (_ , t'') → ret t''))
  ≲⟨ bind-monoˡ-≤⁻ (λ t' → bind (F _) (ListTree .find t' k) (λ (_ , t'') → ret t'')) (commutes ops t) ⟩
    bind (F _) (bind (F _) (ST⇒LT .ϕ t) (λ t' → fold-apply ops ListTree t')) (λ t' → 
      bind (F _) (ListTree .find t' k) (λ (_ , t'') → ret t''))
  ∎

thm : (keys : val (list nat)) → (ops : List BSTOperation) → 
  IsBounded (SplayTree .T) (bind (F _) (SplayTree .fromList keys) (λ t → 
    fold-apply ops SplayTree t))
      (((length ops) * ((3 * ⌊log₂ length (sort/val (deduplicate {R = _≡_} Nat._≟_ keys)) ⌋) + 1)) + 
          (length (sort/val (deduplicate {R = _≡_} Nat._≟_ keys)) * 
          ⌊log₂ length (sort/val (deduplicate {R = _≡_} Nat._≟_ keys)) ⌋))
thm keys ops = ST/bound keys ops
  where 
    LT/bound : (keys : val (list nat)) → (ops : List BSTOperation) →
        fold-apply ops ListTree keys
      ≤⁻[ F _ ] 
        step (F _) ((length (ops)) * ((3 * ⌊log₂ (length keys) ⌋) + 1)) (ret keys)
    LT/bound keys [] = ≤⁻-refl
    LT/bound keys (findKey k ∷ ops) with LT/bound keys ops
    ... | leq = 
      let open ≤⁻-Reasoning (F _) in
      begin
        bind (F _) (fold-apply ops ListTree keys) (λ l' → 
          step (F _) ((3 * ⌊log₂ (length l') ⌋) + 1) 
            (bind (F _) (listFind l' k) (λ _ → ret l')))
      ≡⟨ Eq.cong (λ e → bind (F _) (fold-apply ops ListTree keys) e) (funext λ l' → 
          Eq.cong (λ e → step (F _) ((3 * ⌊log₂ (length l') ⌋) + 1) e) (list/find/bind/lemma l' k)) ⟩
        bind (F _) (fold-apply ops ListTree keys) (λ l' → 
          step (F _) ((3 * ⌊log₂ (length l') ⌋) + 1) (ret l'))
      ≲⟨ bind-monoˡ-≤⁻ (((λ l' → step (F _) ((3 * ⌊log₂ (length l') ⌋) + 1) (ret l')))) leq ⟩
        step (F _) (((length (ops)) * ((3 * ⌊log₂ (length keys) ⌋) + 1)) + ((3 * ⌊log₂ (length keys) ⌋) + 1)) (ret keys)
      ≡⟨ Eq.cong (λ e → step (F _) e (ret keys)) 
          (Nat.+-comm ((length (ops)) * ((3 * ⌊log₂ (length keys) ⌋) + 1)) 
            ((3 * ⌊log₂ (length keys) ⌋) + 1)) ⟩
        step (F _) (((1 + length ops) * ((3 * ⌊log₂ (length keys) ⌋) + 1))) (ret keys)
      ∎
    
    ST/bound : (keys : val (list nat)) → (ops : List BSTOperation) →
      IsBounded (SplayTree .T) (bind (F _) (SplayTree .fromList keys) (λ t → 
        fold-apply ops SplayTree t))
          (((length ops) * ((3 * ⌊log₂ length (sort/val (deduplicate {R = _≡_} Nat._≟_ keys)) ⌋) + 1)) + 
              (length (sort/val (deduplicate {R = _≡_} Nat._≟_ keys)) * 
              ⌊log₂ length (sort/val (deduplicate {R = _≡_} Nat._≟_ keys)) ⌋))
    ST/bound keys ops with LT/bound (sort/val (deduplicate {R = _≡_} Nat._≟_ keys)) ops
    ... | leq = 
      let
        key-set = (sort/val (deduplicate {R = _≡_} Nat._≟_ keys))
        N = length (key-set)
        M = length (ops)
      in
      let open ≤⁻-Reasoning (F _) in
      begin
        bind (F _) (SplayTree .fromList keys) (λ t → 
          bind (F _) (fold-apply ops SplayTree t) (λ _ → ret triv))
      ≲⟨ bind-monoʳ-≤⁻ (SplayTree .fromList keys) (λ t → 
          bind-monoʳ-≤⁻ (fold-apply ops SplayTree t) (λ t' → 
            ST⇒LT .ϕ/total t')) ⟩
        bind (F _) (SplayTree .fromList keys) (λ t → 
          bind (F _) (fold-apply ops SplayTree t) (λ t' → 
            bind (F _) (ST⇒LT .ϕ t') (λ _ → ret triv)))
      ≡⟨⟩
        bind (F _) (SplayTree .fromList keys) (λ t → 
          bind (F _) (bind (F _) (fold-apply ops SplayTree t) (ST⇒LT .ϕ)) (λ _ →
            ret triv))
      ≲⟨ bind-monoʳ-≤⁻ (SplayTree .fromList keys) (λ t → 
          bind-monoˡ-≤⁻ (λ _ → ret triv) (commutes ops t)) ⟩
        bind (F _) (SplayTree .fromList keys) (λ t → 
          bind (F _) (bind (F _) (ST⇒LT .ϕ t) (λ t' → fold-apply ops ListTree t')) (λ _ →
            ret triv))
      ≡⟨⟩
        bind (F _) (SplayTree .fromList keys) (λ t → 
          bind (F _) (ST⇒LT .ϕ t) (λ t' → 
            bind (F _) (fold-apply ops ListTree t') (λ _ →
              ret triv)))
      ≡⟨⟩
        bind (F _) (bind (F _) (SplayTree .fromList keys) (ST⇒LT .ϕ)) (λ t →
          bind (F _) (fold-apply ops ListTree t) (λ _ → ret triv))
      ≲⟨ bind-monoˡ-≤⁻ (λ t → bind (F _) (fold-apply ops ListTree t) (λ _ → ret triv)) 
          (ST⇒LT .ϕ/fromList keys) ⟩
        bind (F _) (ListTree .fromList keys) (λ l → 
          bind (F _) (fold-apply ops ListTree l) (λ _ → 
            ret triv))
      ≡⟨⟩
        step (F _) (N * ⌊log₂ N ⌋) (
          bind (F _) (fold-apply ops ListTree key-set) 
            (λ _ → ret triv))
      ≲⟨ step-monoʳ-≤⁻ (N * ⌊log₂ N ⌋) 
          (bind-monoˡ-≤⁻ (λ _ → ret triv) leq) ⟩
        step (F _) (N * ⌊log₂ N ⌋) (
          bind {A = list nat} (F _) (step (F _) (M * ((3 * ⌊log₂ N ⌋) + 1)) (ret key-set)) (λ _ →
            ret triv))
      ≡⟨⟩
        step (F _) ((N * ⌊log₂ N ⌋) + (M * ((3 * ⌊log₂ N ⌋) + 1))) (ret triv)
      ≡⟨ Eq.cong (λ e → step (F _) e (ret triv)) 
          (Nat.+-comm (N * ⌊log₂ N ⌋) ((M * ((3 * ⌊log₂ N ⌋) + 1)))) ⟩
        step (F _) ((M * ((3 * ⌊log₂ N ⌋) + 1)) + (N * ⌊log₂ N ⌋)) (ret triv)
      ∎
