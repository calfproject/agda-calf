{-# OPTIONS --cubical #-}

module Examples.Specification.Treap where

open import Data.List
open import Data.Product
open import Cubical.Foundations.Everything using (_≡_; _≃_; equiv-proof; isContr; fiber)

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
  inord (assoc u i) = {!   !}

  theorem : ext → Tree ≃ List A
  proj₁ (theorem _) = inord
  equiv-proof (proj₂ (theorem u)) l = {!   !} , {!   !}
