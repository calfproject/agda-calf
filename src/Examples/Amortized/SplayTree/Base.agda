{-# OPTIONS --rewriting #-}

module Examples.Amortized.SplayTree.Base where

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

open import Relation.Binary 
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; module ≡-Reasoning)

open import Data.Nat.Logarithm

record BST : Set where
  field 
    T : tp⁺
    fromList : cmp (Π (list nat) (λ _ → F (T)))
    size : cmp (Π T (λ _ → F (nat)))
    find : cmp (Π T (λ _ → Π nat (λ _ → F (bool ×⁺ T))))

insert/val : (x : val nat) → (sorted-xs : val (list nat)) → val (list nat)
insert/val x [] = x ∷ []
insert/val x (y ∷ ys) with Nat.<-cmp x y
... | tri< _ _ _ = x ∷ (y ∷ ys)
... | tri≈ _ _ _ = x ∷ (y ∷ ys)
... | tri> _ _ _ = y ∷ (insert/val x ys)

sort/val : val (list nat) → val (list nat) 
sort/val [] = []
sort/val (x ∷ xs) = insert/val x (sort/val xs)

listFind : (l : val (list nat)) (k : val nat) → cmp (F (bool))
listFind [] k = ret (false)
listFind (x ∷ xs) k with Nat.<-cmp x k 
... | tri< _ _ _ = bind (F _) (listFind xs k) ret
... | tri≈ _ _ _ = ret (true)
... | tri> _ _ _ = bind (F _) (listFind xs k) ret

deduplicate/cmp : cmp (Π (list nat) λ _ → F (list nat))
deduplicate/cmp l = ret (deduplicate {R = _≡_} Nat._≟_ l)

ListTree : BST
ListTree .BST.T = list nat
ListTree .BST.fromList l = 
  step (F _) (length (sort/val (deduplicate {R = _≡_} Nat._≟_ l)) * ⌊log₂ (length (sort/val (deduplicate {R = _≡_} Nat._≟_ l))) ⌋) 
    (ret (sort/val (deduplicate {R = _≡_} Nat._≟_ l)))
ListTree .BST.size l = ret (length l)
ListTree .BST.find l k = 
  step (F _) ((3 * ⌊log₂ (length l)⌋) + 1) (
    bind (F _) (listFind l k) (λ b → ret (b , l)))
    
list/find/lemma : ∀ (l : val (list nat)) (k : val nat) → ∃[ b ] (listFind l k ≡ ret b)
list/find/lemma [] k = false , refl
list/find/lemma (x ∷ xs) k with Nat.<-cmp x k 
... | tri< _ _ _ = list/find/lemma xs k
... | tri≈ _ _ _ = true , refl
... | tri> _ _ _ = list/find/lemma xs k

list/find/bind/lemma : (l : val (list nat)) → (k : val nat) → 
  bind (F (list nat)) (listFind l k) (λ _ → ret l) ≡ ret l
list/find/bind/lemma l k with (list/find/lemma l k)
... | b , eq = 
  let open ≡-Reasoning in
  begin
    bind (F (list nat)) (listFind l k) (λ _ → ret l)
  ≡⟨ Eq.cong (λ e → bind (F _) e (λ _ → ret l)) eq ⟩
    bind {A = bool} (F (list nat)) (ret b) (λ _ → ret l)
  ≡⟨⟩
    ret l
  ∎
  