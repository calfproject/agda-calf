open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure

module Calf.Computation.CList where

open import Calf.Value.Nat
open import Calf.Value.Sigma
open import Calf.Computation
open import Calf.Computation.Copower
open import Calf.Computation.Tensor
open import Calf.Computation.Copower
open import Calf.Computation.Power


-- inductively changing computation list
opaque
  CList' : 𝒞 → (𝒞 → 𝒞) → 𝒞
  CList' A₀ Af = [ n ∈ ℕₛ ] ⋊ ⊗ᵏ' n A₀ Af

  variable
    A₀ : 𝒞
    Af : 𝒞 → 𝒞

  cnil' : U (CList' A₀ Af)
  cnil' = 0 , trivᶜ

  ccons' : A₀ ⊗ CList' (Af A₀) Af ⊸ CList' A₀ Af
  ccons' {A₀} {Af} = subst (_⊸ CList' A₀ Af) (sym (A⊗[X⋊B]≡X⋊[A⊗B] {X = ℕₛ})) ccons''
    where
      ccons'' : [ n ∈ ℕₛ ] ⋊ (A₀ ⊗ ⊗ᵏ' n (Af A₀) Af) ⊸ CList' A₀ Af
      ccons'' .U (n , as) = suc n , as
      ccons'' .charge c (n , as) = refl

  cfoldr' :
    (Ap : 𝒞 → Type₁)
    → (B : (A : 𝒞) → Ap A → 𝒞)
    → (∀ A → (ap : Ap A) → U (B A ap))
    → (∀ A → (ap : Ap A) → Σ[ ap' ∈ Ap (Af A) ] (A ⊗ B (Af A) ap' ⊸ B A ap))
    → (ap₀ : Ap A₀)
    → CList' A₀ Af ⊸ B A₀ ap₀
  cfoldr' {Af} {A₀} Ap B e[] e∷ ap₀ = ⋊-splitᶜ {X = ℕₛ} (⊗foldr' A₀ ap₀)
    where
      ⊗foldr' : (A : 𝒞) → (ap : Ap A) → (n : ℕ) → ⊗ᵏ' n A Af ⊸ B A ap
      ⊗foldr' A ap zero = U→cmp (e[] A ap)
      ⊗foldr' A ap (suc n') =
        let (ap' , e∷') = e∷ A ap in
        map₂ idᶜ (⊗foldr' (Af A) ap' n') ⨾ᶜ e∷'


-- computation list
opaque
  unfolding CList'

  CList : 𝒞 → 𝒞
  CList A = CList' A (idfun 𝒞)

  cnil : U (CList A)
  cnil = cnil'

  ccons : A ⊗ CList A ⊸ CList A
  ccons = ccons'

  cfoldr : U B
    → (A ⊗ B ⊸ B)
    → CList A ⊸ B
  cfoldr {B} {A} e[] e∷ =
    cfoldr' (A ≡_) (λ _ _ → B)
      (λ A' ap' → e[])
      (λ A' ap' → ap' , subst (λ C → (C ⊗ B) ⊸ _) ap' e∷)
      refl
