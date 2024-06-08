{-# OPTIONS --cubical #-}

module Examples.Specification.Treap where

open import Cubical.Data.List
open import Cubical.Data.Nat using (ℕ)
open import Data.Product
open import Cubical.Foundations.Everything using (_≡_; _≃_; equiv-proof; isContr;  i0; i1; isoToEquiv; section; retract; cong; _∙_ ; sym)
open import Cubical.Data.List.Properties using (++-assoc)
open import Agda.Builtin.Cubical.HCompU
  
postulate
  ext : Prop

module _ (A : Set) where
  data Tree : Set where
    empty : Tree
    node  : Tree → A → Tree → Tree
    assoc : {t₁ t₂ t₃ : Tree} {a a' : A} → ext → node (node t₁ a t₂) a' t₃ ≡ node t₁ a (node t₂ a' t₃)

  inord : Tree → List A
  inord empty = []
  inord (node t₁ a t₂) = inord t₁ ++ [ a ] ++ inord t₂
  inord (assoc {t₁} {t₂} {t₃} {a} {a'} u i) = ++-assoc (inord t₁) (a ∷ inord t₂) (a' ∷ inord t₃) i

  right-spine : List A → Tree  
  right-spine [] = empty
  right-spine (x ∷ l) = node empty x (right-spine l)
  
  inord-right-spine : (l : List A) → inord (right-spine l) ≡ l 
  inord-right-spine [] = λ _ → []
  inord-right-spine (x ∷ xs) = λ i → x ∷ (inord-right-spine xs) i

  tree-append : (t₁ t₂ : Tree) → Tree 
  tree-append empty t₂ = t₂
  tree-append (node t₁ x t₂) t₃ = node t₁ x (tree-append t₂ t₃)
  tree-append (assoc {t₁} {t₂} {t₃} {a} {a'} u i) t₄ = lemma i
    where
    lemma : node (node t₁ a t₂) a' (tree-append t₃ t₄) ≡ node t₁ a (node t₂ a' (tree-append t₃ t₄))
    lemma = assoc u

  right-spine-lemma : (l₁ l₂ : List A) → right-spine (l₁ ++ l₂) ≡ tree-append (right-spine l₁) (right-spine l₂)
  right-spine-lemma [] l₂ = λ _ → right-spine l₂
  right-spine-lemma (x ∷ l₁) l₂ = cong (λ t → node empty x t) (right-spine-lemma l₁ l₂)

  tree-append-lemma : (u : ext) → (t₁ t₂ : Tree) →  (x : A) → tree-append t₁ (node empty x t₂) ≡ node t₁ x t₂ 
  tree-append-lemma u empty t₂ x i = node empty x t₂
  tree-append-lemma u (node t₁ x₁ t₂) t₃ x i = (cong (λ t → node t₁ x₁ t) (tree-append-lemma u t₂ t₃ x) ∙ sym (assoc u)) i 
  tree-append-lemma u (assoc x₁ i₁) t₂ x i = {!   !}
  
  ext-right-spine-inord : (u : ext) → (t : Tree) → right-spine (inord t) ≡ t
  ext-right-spine-inord u empty = λ _ → empty
  ext-right-spine-inord u (node t₁ x t₂) = right-spine-lemma (inord t₁) (x ∷ (inord t₂)) 
                                        ∙ cong (λ t → tree-append t (node empty x (right-spine (inord t₂)))) (ext-right-spine-inord u t₁)
                                        ∙ cong (λ t → tree-append t₁ (node empty x t)) (ext-right-spine-inord u t₂)
                                        ∙ tree-append-lemma u t₁ t₂ x
  ext-right-spine-inord u (assoc _ i) = {!   !}


  sec-inord-spine : section inord right-spine 
  sec-inord-spine = λ l i → inord-right-spine l i

  ret-inord-spine : (u : ext) → retract inord right-spine 
  ret-inord-spine u empty i = empty
  ret-inord-spine u (node t x t₁) i = lemma i
    where 
    lemma : right-spine (inord t ++ x ∷ inord t₁) ≡ node t x t₁
    lemma = (λ _ → right-spine (inord t ++ x ∷ inord t₁)) ∙ ext-right-spine-inord u (node t x t₁)
  ret-inord-spine u (assoc x i₁) i = {!   !}
           
  theorem : ext → Tree ≃ List A 
  theorem u = isoToEquiv (Cubical.Foundations.Everything.iso inord right-spine (sec-inord-spine) (ret-inord-spine u))  