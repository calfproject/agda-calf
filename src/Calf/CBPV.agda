{-# OPTIONS --rewriting #-}

-- The basic CBPV metalanguage.

module Calf.CBPV where

open import Calf.Prelude
open import Relation.Binary.PropositionalEquality
open import Data.Unit using () renaming (tt to triv) public
open import Data.Unit renaming (⊤ to Unit)
open import Data.Product using (_,_; proj₁; proj₂) public
open import Data.Product using (Σ; _×_)

postulate
  tp⁺ : □
  tp⁻ : □
  val : tp⁺ → □

  F : tp⁺ → tp⁻
  U : tp⁻ → tp⁺

{-# POLARITY val ++ #-}
{-# POLARITY F ++ #-}
{-# POLARITY U ++ #-}

-- This is equivalent to adding "thunk / force" operations but less bureaucratic.
cmp : tp⁻ → □
cmp X = val (U X)

private
  variable
    A B C : tp⁺
    X Y Z : tp⁻


-- Value types

postulate
  meta⁺ : Set → tp⁺
  meta⁺/decode : {𝕊 : Set} → val (meta⁺ 𝕊) ≡ 𝕊
  {-# REWRITE meta⁺/decode #-}
{-# POLARITY meta⁺ ++ #-}

Σ⁺ : (A : tp⁺) (B : val A → tp⁺) → tp⁺
Σ⁺ A B = meta⁺ (Σ (val A) λ a → val (B a))


-- Computation types

postulate
  ret : val A → cmp (F A)
  bind : (X : tp⁻) → cmp (F A) → (val A → cmp X) → cmp X

  bind/β : {a : val A} {f : val A → cmp X} → bind X (ret {A} a) f ≡ f a
  bind/η : {e : cmp (F A)} → bind (F A) e ret ≡ e
  bind/assoc : {e : cmp (F A)} {f : val A → cmp (F B)} {g : val B → cmp X} →
    bind X (bind (F B) e f) g ≡ bind X e (λ a → bind X (f a) g)
  {-# REWRITE bind/β bind/η bind/assoc #-}

  Π : (A : tp⁺) (X : val A → tp⁻) → tp⁻
  Π/decode : {X : val A → tp⁻} → val (U (Π A X)) ≡ ((a : val A) → cmp (X a))
  {-# REWRITE Π/decode #-}

  prod⁻ : tp⁻ → tp⁻ → tp⁻
  prod⁻/decode : val (U (prod⁻ X Y)) ≡ (cmp X × cmp Y)
  {-# REWRITE prod⁻/decode #-}

  unit⁻ : tp⁻
  unit⁻/decode : val (U unit⁻) ≡ Unit
  {-# REWRITE unit⁻/decode #-}

  Σ⁻ : (A : tp⁺) (X : val A → tp⁻) → tp⁻
  Σ⁻/decode : {X : val A → tp⁻} → val (U (Σ⁻ A X)) ≡ Σ (val A) λ a → cmp (X a)
  {-# REWRITE Σ⁻/decode #-}

_⇀_ : tp⁺ → tp⁻ → tp⁻
A ⇀ X = Π A λ _ → X

_⋉_ : tp⁺ → tp⁻ → tp⁻
A ⋉ X = Σ⁻ A λ _ → X
