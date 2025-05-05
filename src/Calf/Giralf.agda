{-# OPTIONS --rewriting --allow-unsolved-metas #-}

open import Algebra.Cost

module Calf.Giralf (costMonoid : CostMonoid) where

open CostMonoid costMonoid


open import Calf.Prelude
open import Calf.CBPV
open import Calf.Directed
open import Calf.Step costMonoid
open import Relation.Binary.PropositionalEquality

open import Relation.Binary.Core
open import Relation.Binary.Definitions
open import Relation.Binary.Structures


record Giralf : Set₁ where
  field
    𝓒 : Set
    _⨾_⊢_ : 𝓒 → ℂ → 𝓒 → Set

    charge : {Δ A : 𝓒} {q : ℂ} (p : ℂ) → Δ ⨾ q ⊢ A → Δ ⨾ p + q ⊢ A

    _g⋊_ : ℂ → 𝓒 → 𝓒
    store : {!   !}
    release : {!   !}
open Giralf

_⊸F_ : tp⁺ → tp⁺ → Set
X ⊸F Y = cmp (X ⇀ F Y)

record PotentialFunction : Set where
  field
    X : tp⁺
    Φ : X ⊸F X
open PotentialFunction

record Square (Δ : PotentialFunction) (p : ℂ) (A : PotentialFunction) : Set where
  field
    top : Δ .X ⊸F A .X
    bot : Δ .X ⊸F A .X
    square :
      (δ : val (Δ .X)) →
        bind (F _) (top δ) (A .Φ) ≤⁻[ F _ ] bind (F _) (Δ .Φ δ) bot
open Square

giralf : Giralf
giralf .𝓒 = PotentialFunction
giralf ._⨾_⊢_ = Square
giralf .charge p e .top δ = step (F _) p (e .top δ)
giralf .charge p e .bot = e .bot
giralf .charge p e .square δ = {!   !}
giralf ._g⋊_ = {!   !}
giralf .store = {!   !}
giralf .release = {!   !}
