open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

module Calf.Computation.CList1 where

open import Calf.Core.Cost
open import Calf.Value
open import Calf.Value.List
open import Calf.Value.Nat
open import Calf.Computation
open import Calf.Computation.Copower
open import Calf.Computation.Credit
open import Calf.Computation.Tensor
open import Calf.Computation.Potential using (▷-Σᶜ)

opaque
  CList₁ : ℂ → 𝒱ₛ → 𝒞
  CList₁ c Xₛ = [ l ∈ Listₛ Xₛ ] ⋊ ▷[ length l ⊙ c ] ⊤

  cnil₁ : ∀ {c} → U (CList₁ c Xₛ)
  cnil₁ = [] , subst U (sym ▷/0) 0ℂ

  ccons₁ : ∀ {c} → ⟨ Xₛ ⟩ → ▷[ c ] CList₁ c Xₛ ⊸ CList₁ c Xₛ
  ccons₁ {X} {c} x =
    transport (cong (_⊸ CList₁ c X) (sym (▷-Σᶜ c))) $
    Σᶜ-rec λ l → transport (cong (_⊸ CList₁ c X) ▷/+) (Σᶜ-in (x ∷ l))

  cfoldr₁ : ∀ {c} → U A → (⟨ Xₛ ⟩ → ▷[ c ] A ⊸ A) → CList₁ c Xₛ ⊸ A
  cfoldr₁ {A} {X} {c} e-nil e-cons = Σᶜ-rec go
    where
      go : (l : List ⟨ X ⟩) → ▷[ length l ⊙ c ] ⊤ ⊸ A
      go [] = ▷⊤-rec e-nil
      go (x ∷ l) = transport (cong (_⊸ A) (sym ▷/+)) (▷-map (go l) ⨾ᶜ e-cons x)
