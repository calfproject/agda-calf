{-# OPTIONS --type-in-type #-}

module Examples.SequenceV where

open import Cubical.Foundations.Function
open import Cubical.Foundations.Path
open import Cubical.Foundations.Univalence
import Cubical.Data.List.Properties as List
import Cubical.Data.Nat.Properties as Nat
import Cubical.Data.Bool.Properties as Bool

open import Cubical.Data.Sigma using (map-snd; ΣPathP; Σ-contractFst; Σ-cong-snd)

open import Calf.Core.Abstract
open import Calf.Value hiding (empty)
open import Calf.Value.Abstraction
open import Calf.Value.Glue using (fracture-isEquiv)
open import Calf.Value.List
open import Calf.Value.Nat
open import Calf.Value.Bool
open import Calf.Value.Product
open import Calf.Value.Sigma
open import Calf.Value.Open
open import Calf.Value.Closed as ●

_≗_ : X → X → 𝒱
x ≗ x' = ◯ (x ≡ x')

isContr◦ : 𝒱 → 𝒱
isContr◦ X = Σ[ x ∈ X ] (∀ x' → x ≗ x')

module _ (E : 𝒱) where

  record MonoidOn : 𝒱 where
    field
      Carrier : 𝒱
      empty : Carrier
      append : Carrier → Carrier → Carrier
      identityˡ : (x : Carrier) → append empty x ≗ x
      identityʳ : (x : Carrier) → append x empty ≗ x
      assoc : (x y z : Carrier) → append (append x y) z ≗ append x (append y z)

    field
      singleton : E → Carrier
  open MonoidOn

  record Hom (M N : MonoidOn) : 𝒱 where
    field
      Carrier : M .Carrier → N .Carrier
      empty : Carrier (M .empty) ≗ N .empty
      append : ∀ m m' → Carrier (M .append m m') ≗ N .append (Carrier m) (Carrier m')
      singleton : ∀ e → Carrier (M .singleton e) ≗ N .singleton e
  open Hom

  record Sequence : 𝒱 where
    field
      monoid-on : MonoidOn
      mapreduce : (M : MonoidOn) → isContr◦ (Hom monoid-on M)
  open Sequence

  list-sequence : Sequence
  list-sequence .monoid-on .Carrier = List E
  list-sequence .monoid-on .empty = []
  list-sequence .monoid-on .append = _++_
  list-sequence .monoid-on .identityˡ _ abs = refl
  list-sequence .monoid-on .identityʳ _ abs = List.++-unit-r _
  list-sequence .monoid-on .assoc l _ _ abs = List.++-assoc l _ _
  list-sequence .monoid-on .singleton = [_]
  list-sequence .mapreduce M .fst .Carrier =
    foldr
      (λ e m → M .append (M .singleton e) m)
      (M .empty)
  list-sequence .mapreduce M .fst .empty = {!   !}
  list-sequence .mapreduce M .fst .append = {!   !}
  list-sequence .mapreduce M .fst .singleton = {!   !}
  list-sequence .mapreduce M .snd f abs = {!   !}


  module RedBlackTree where
    data Color : 𝒱 where
      red black : Color

    variable
      c₁ c₂ c : Color
      n₁ n₂ n : ℕ

    data LeafInvariant : Color → ℕ → 𝒱 where
      black : LeafInvariant black zero

    data Invariant : (c₁ c₂ c : Color) (n₁ n₂ n : ℕ) → 𝒱 where
      black : Invariant c₁ c₂ black n n (suc n)
      red : Invariant black black red n n n

    module Abstraction where
      data IRBT : Color → ℕ → 𝒱 where
        leaf : LeafInvariant c n → E → IRBT c n
        null : LeafInvariant c n → IRBT c n
        node :
            Invariant c₁ c₂ c n₁ n₂ n
          → IRBT c₁ n₁ → IRBT c₂ n₂ → IRBT c n

      RBT : 𝒱
      RBT = Σ[ c ∈ Color ] Σ[ n ∈ ℕ ] IRBT c n

      χ : RBT → List ℕ
      χ = {!   !}

      rbt-sequence : Sequence
      rbt-sequence .monoid-on .Carrier = Abstraction χ
      rbt-sequence .monoid-on .empty = {!   !}
      rbt-sequence .monoid-on .append = {!   !}
      rbt-sequence .monoid-on .identityˡ = {!   !}
      rbt-sequence .monoid-on .identityʳ = {!   !}
      rbt-sequence .monoid-on .assoc = {!   !}
      rbt-sequence .monoid-on .singleton = {!   !}
      rbt-sequence .mapreduce = {!   !}

    module Quotient where
      LeafInvariant• : ● Color → ● ℕ → 𝒱
      LeafInvariant• c• n• = {!   !}

      Invariant• : (c₁• c₂• c• : ● Color) (n₁• n₂• n• : ● ℕ) → 𝒱
      Invariant• = {!   !}

      variable
        c₁• c₂• c• : ● Color
        n₁• n₂• n• : ● ℕ

      data IRBT• : ● Color → ● ℕ → 𝒱 where
        leaf : LeafInvariant• c• n• → E → IRBT• c• n•
        null : LeafInvariant• c• n• → IRBT• c• n•
        node :
            Invariant• c₁• c₂• c• n₁• n₂• n•
          → IRBT• c₁• n₁• → IRBT• c₂• n₂• → IRBT• c• n•
        identityˡ• : ◯ (∀ inv linv t
          → node {c₁•} {c•} {c•} {n₁•} {n•} {n•} inv (null linv) t ≡ t)
        identityʳ• : {!   !}
        assoc• : {!   !}

      RBT• : 𝒱
      RBT• = Σ[ c• ∈ ● Color ] Σ[ n• ∈ ● ℕ ] IRBT• c• n•

      rbt-sequence : Sequence
      rbt-sequence .monoid-on .Carrier = RBT•
      rbt-sequence .monoid-on .empty = η• black , η• zero , null {!   !}
      rbt-sequence .monoid-on .append = {!   !}
      rbt-sequence .monoid-on .identityˡ = {!   !}
      rbt-sequence .monoid-on .identityʳ = {!   !}
      rbt-sequence .monoid-on .assoc = {!   !}
      rbt-sequence .monoid-on .singleton = {!   !}
      rbt-sequence .mapreduce = {!   !}
