{-# OPTIONS --cubical #-}

module Examples.Specification.Treap where

open import Cubical.Data.List
open import Cubical.Data.Nat using (ℕ)
open import Data.Product
open import Cubical.Foundations.Everything using (_≡_; _≃_; equiv-proof; isContr;  i0; i1; isoToEquiv; section; retract; cong; cong₂; _∙_ ; sym; refl)
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


  sec-inord-spine : section inord right-spine
  sec-inord-spine [] = refl
  sec-inord-spine (x ∷ xs) = cong (x ∷_) (sec-inord-spine xs)


  -- tree-append : (t₁ t₂ : Tree) → Tree
  -- tree-append empty t₂ = t₂
  -- tree-append (node t₁ x t₂) t₃ = node t₁ x (tree-append t₂ t₃)
  -- tree-append (assoc {t₁} {t₂} {t₃} {a} {a'} u i) t₄ = assoc {t₁} {t₂} {tree-append t₃ t₄} {a} {a'} u i

  -- right-spine-lemma : (l₁ l₂ : List A) → right-spine (l₁ ++ l₂) ≡ tree-append (right-spine l₁) (right-spine l₂)
  -- right-spine-lemma [] l₂ = refl
  -- right-spine-lemma (x ∷ l₁) l₂ = cong (λ t → node empty x t) (right-spine-lemma l₁ l₂)

  -- tree-append-lemma : (u : ext) → (t₁ t₂ : Tree) → (x : A) → tree-append t₁ (node empty x t₂) ≡ node t₁ x t₂
  -- tree-append-lemma u empty t₂ x = refl
  -- tree-append-lemma u (node t₁ x₁ t₂) t₃ x = cong (λ t → node t₁ x₁ t) (tree-append-lemma u t₂ t₃ x) ∙ sym (assoc u)
  -- tree-append-lemma u (assoc x₁ i₁) t₂ x = {!   !}

  -- ext-right-spine-inord u empty = λ _ → empty
  -- ext-right-spine-inord u (node t₁ x t₂) = right-spine-lemma (inord t₁) (x ∷ (inord t₂))
  --                                       ∙ cong (λ t → tree-append t (node empty x (right-spine (inord t₂)))) (ext-right-spine-inord u t₁)
  --                                       ∙ cong (λ t → tree-append t₁ (node empty x t)) (ext-right-spine-inord u t₂)
  --                                       ∙ tree-append-lemma u t₁ t₂ x
  -- ext-right-spine-inord u (assoc _ i) = {!   !}

  right-spine-lemma : ∀ l₁ y l₂ → ext → right-spine (l₁ ++ y ∷ l₂) ≡ node (right-spine l₁) y (right-spine l₂)
  right-spine-lemma [] y l₂ u = refl
  right-spine-lemma (x ∷ l₁) y l₂ u = cong (node empty x) (right-spine-lemma l₁ y l₂ u) ∙ sym (assoc u)

  ret-inord-spine : ext → retract inord right-spine
  ret-inord-spine u empty = refl
  ret-inord-spine u (node t₁ x t₂) =
    right-spine-lemma (inord t₁) x (inord t₂) u
    ∙ cong₂ (λ t₁ t₂ → node t₁ x t₂) (ret-inord-spine u t₁) (ret-inord-spine u t₂)
  ret-inord-spine u (assoc u i) = {!   !}

  theorem : ext → Tree ≃ List A
  theorem u = isoToEquiv (Cubical.Foundations.Everything.iso inord right-spine sec-inord-spine (ret-inord-spine u))
