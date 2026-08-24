open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure

module Calf.Computation.List where

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

  Listᶜ' : (X → 𝒞) → (X → X) → X → 𝒞
  Listᶜ' Af xf x₀ = [ n ∈ ℕₛ ] ⋊ ⊗ᵏ Af xf x₀ n

  private variable
    Af : X → 𝒞
    xf : X → X
    x₀ : X

  nil' : U (Listᶜ' Af xf x₀)
  nil' = 0 , trivᶜ

  cons' : Af x₀ ⊗ Listᶜ' Af xf (xf x₀) ⊸ Listᶜ' Af xf x₀
  cons' {Af = Af} {x₀ = x₀} {xf = xf} = subst (_⊸ Listᶜ' Af xf x₀) (sym (A⊗[X⋊B]≡X⋊[A⊗B] {X = ℕₛ})) cons''
    where
      cons'' : [ n ∈ ℕₛ ] ⋊ (Af x₀ ⊗ ⊗ᵏ Af xf (xf x₀) n) ⊸ Listᶜ' Af xf x₀
      cons'' .U (n , as) = suc n , as
      cons'' .charge c (n , as) = refl

  foldr' :
    (B : (x : X) → 𝒞)
    → (∀ x → U (B x))
    → (∀ x → (Af x ⊗ B (xf x) ⊸ B x))
    → Listᶜ' Af xf x₀ ⊸ B x₀
  foldr' {X = X} {Af = Af} {xf = xf} {x₀ = x₀} B e[] e∷ = ⋊-splitᶜ {X = ℕₛ} (⊗foldr' x₀)
    where
      ⊗foldr' : (x : X) → (n : ℕ) → ⊗ᵏ Af xf x n ⊸ B x
      ⊗foldr' x zero = U→cmp (e[] x)
      ⊗foldr' x (suc n') = map₂ idᶜ (⊗foldr' (xf x) n') ⨾ᶜ e∷ x


-- computation list
opaque
  open import Calf.Value.Unit using (tt)

  Listᶜ : 𝒞 → 𝒞
  Listᶜ A = Listᶜ' (λ _ → A) (λ _ → tt) tt

  nil : U (Listᶜ A)
  nil = nil'

  cons : A ⊗ Listᶜ A ⊸ Listᶜ A
  cons = cons'

  foldr : U B
    → (A ⊗ B ⊸ B)
    → Listᶜ A ⊸ B
  foldr {B} {A} e[] e∷ = foldr' (λ _ → B) (λ _ → e[]) (λ _ → e∷)

opaque
  unfolding Listᶜ
  unfolding Listᶜ'
  open import Calf.Computation.Free

  clength : Listᶜ A ⊸ ℕₛ ⋊ Listᶜ A
  clength {A} =
    ⋊-splitᶜ {X = ℕₛ} (λ n → ⋊-pairᶜ {X = ℕₛ} {A = λ n → ⊗ᵏ _ _ _ n}  n ⨾ᶜ ⋊-pairᶜ {X = ℕₛ} n)
