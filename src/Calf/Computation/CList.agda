open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure

module Calf.Computation.CList where

open import Calf.Value
open import Calf.Value.Nat
open import Calf.Value.Sigma
open import Calf.Computation
open import Calf.Computation.Copower
open import Calf.Computation.Tensor
open import Calf.Computation.Copower
open import Calf.Computation.Power


-- inductively changing computation list
opaque
  unfolding ⊗ᵏ

  CList' : (X → 𝒞) → (X → X) → X → 𝒞
  CList' Af xf x₀ = [ n ∈ ℕₛ ] ⋊ ⊗ᵏ Af xf x₀ n

  variable
    Af : X → 𝒞
    xf : X → X
    x₀ : X

  cnil' : U (CList' Af xf x₀)
  cnil' = 0 , trivᶜ

  ccons' : Af x₀ ⊗ CList' Af xf (xf x₀) ⊸ CList' Af xf x₀
  ccons' {Af = Af} {x₀ = x₀} {xf = xf} = subst (_⊸ CList' Af xf x₀) (sym (A⊗[X⋊B]≡X⋊[A⊗B] {X = ℕₛ})) ccons''
    where
      ccons'' : [ n ∈ ℕₛ ] ⋊ (Af x₀ ⊗ ⊗ᵏ Af xf (xf x₀) n) ⊸ CList' Af xf x₀
      ccons'' .U (n , as) = suc n , as
      ccons'' .charge c (n , as) = refl

  cfoldr' :
    (B : (x : X) → 𝒞)
    → (∀ x → U (B x))
    → (∀ x → (Af x ⊗ B (xf x) ⊸ B x))
    → CList' Af xf x₀ ⊸ B x₀
  cfoldr' {X = X} {Af = Af} {xf = xf} {x₀ = x₀} B e[] e∷ = ⋊-splitᶜ {X = ℕₛ} (⊗foldr' x₀)
    where
      ⊗foldr' : (x : X) → (n : ℕ) → ⊗ᵏ Af xf x n ⊸ B x
      ⊗foldr' x zero = U→cmp (e[] x)
      ⊗foldr' x (suc n') = map₂ idᶜ (⊗foldr' (xf x) n') ⨾ᶜ e∷ x


-- computation list
opaque
  open import Calf.Value.Unit using (tt)

  CList : 𝒞 → 𝒞
  CList A = CList' (λ _ → A) (λ _ → tt) tt

  cnil : U (CList A)
  cnil = cnil'

  ccons : A ⊗ CList A ⊸ CList A
  ccons = ccons'

  cfoldr : U B
    → (A ⊗ B ⊸ B)
    → CList A ⊸ B
  cfoldr {B} {A} e[] e∷ = cfoldr' (λ _ → B) (λ _ → e[]) (λ _ → e∷)

opaque
  unfolding CList
  unfolding CList'
  open import Calf.Computation.Free

  clength : CList A ⊸ ℕₛ ⋊ CList A
  clength {A} =
    ⋊-splitᶜ {X = ℕₛ} (λ n → ⋊-pairᶜ {X = ℕₛ} {A = λ n → ⊗ᵏ _ _ _ n}  n ⨾ᶜ ⋊-pairᶜ {X = ℕₛ} n)
