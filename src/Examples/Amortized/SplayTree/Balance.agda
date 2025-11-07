{-# OPTIONS --rewriting #-}

module Examples.Amortized.SplayTree.Balance where

open import Algebra.Cost

costMonoid = ℕ-CostMonoid
open CostMonoid costMonoid renaming (_+_ to _⊕_)

open import Calf costMonoid 
open import Calf.Data.Nat 
open import Calf.Data.List hiding (find)
open import Calf.Data.IsBounded costMonoid

open import Data.Nat as Nat using (ℕ; _<_; _≤?_; _<?_; zero)
open import Data.Nat.Properties as Nat using (module ≤-Reasoning; _≟_)

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≢_; refl; module ≡-Reasoning)

open import Data.Nat.Logarithm

open import Examples.Amortized.SplayTree.Prelude
open import Examples.Amortized.SplayTree.SplayTree
open import Examples.Amortized.SplayTree.LaxHomomorphism 

open BST
open BSTHom 

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

balance : (keys : val (list nat)) (ops : List BSTOperation) → 
  let 
    n = length (sort/val (deduplicate {R = _≡_} Nat._≟_ keys)) 
    m = length ops
  in 
  IsBounded (SplayTree .T) 
    (bind (F _) (SplayTree .fromList keys) (λ t → fold-apply ops SplayTree t))
      ((m * ((3 * ⌊log₂ n ⌋) + 1)) + (n * ⌊log₂ n ⌋))
balance keys ops = ST/bound keys ops
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
