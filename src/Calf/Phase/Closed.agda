{-# OPTIONS --rewriting #-}

-- Closed/intensional modality.

module Calf.Phase.Closed where

open import Calf.Prelude
open import Calf.CBPV
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Calf.Phase.Core

private
  variable
    A B C : tp⁺
    X Y Z : tp⁻

-- data ● (A : tp⁺) : tp⁺ where
--   η : A → ● A
--   ∗ : ext → ● A
--   η≡∗ : (a : A) (u : ext) → η a ≡ ∗ u

postulate
  ● : tp⁺ → tp⁺

  η : val A → val (● A)
  ∗ : ext → val (● A)
  η≡∗ : (a : val A) (u : ext) → η {A} a ≡ ∗ u
  η≡∗/uni : {x x' : val (● A)} (p p' : x ≡ x') → p ≡ p'

  ●/ind : (a : val (● A)) (𝕁 : val (● A) → □)
    (x0 : (a : val A) → 𝕁 (η a)) →
    (x1 : (u : ext) → 𝕁 (∗ u)) →
    ((a : val A) → (u : ext) → subst (λ a → 𝕁 a) (η≡∗ a u) (x0 a) ≡ x1 u) →
    𝕁 a
  ●/ind/β₁ : (a : val A) (𝕁 : val (● A) → □)
    (x0 : (a : val A) → 𝕁 (η a)) →
    (x1 : (u : ext) → 𝕁 (∗ u)) →
    (h : (a : val A) → (u : ext) → subst (λ a → 𝕁 a) (η≡∗ a u) (x0 a) ≡ x1 u) →
    ●/ind (η a) 𝕁 x0 x1 h ≡ x0 a
  {-# REWRITE ●/ind/β₁ #-}
  ●/ind/β₂ : (u : ext) (𝕁 : val (● A) → □)
    (x0 : (a : val A) → 𝕁 (η a)) →
    (x1 : (u : ext) → 𝕁 (∗ u)) →
    (h : (a : val A) → (u : ext) → subst (λ a → 𝕁 a) (η≡∗ a u) (x0 a) ≡ x1 u) →
    ●/ind (∗ u) 𝕁 x0 x1 h ≡ x1 u
  {-# REWRITE ●/ind/β₂ #-}
