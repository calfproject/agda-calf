{-# OPTIONS --rewriting --allow-unsolved-metas #-}

open import Algebra.Cost

module Calf.Giralf (costMonoid : CostMonoid) where

open CostMonoid costMonoid


open import Calf.Prelude
open import Calf.CBPV
open import Calf.Directed
open import Calf.Step costMonoid
open import Calf.Data.Product
open import Calf.Data.List


record Giralf : Set₁ where
  field
    𝓒 : Set
    _⨾_⊢_ : 𝓒 → ℂ → 𝓒 → Set

    charge : ∀ {Δ q A} (p : ℂ) → Δ ⨾ q ⊢ A → Δ ⨾ p + q ⊢ A

    _⋊ᵍ_ : ℂ → 𝓒 → 𝓒
    store : {!   !}
    release : {!   !}

    ⊤ : 𝓒

    _⊗_ : 𝓒 → 𝓒 → 𝓒
    tensor : ∀ {Δ₁ Δ₂ q₁ q₂ A₁ A₂}
      → Δ₁ ⨾ q₁ ⊢ A₁
      → Δ₂ ⨾ q₂ ⊢ A₂
      → (Δ₁ ⊗ Δ₂) ⨾ (q₁ + q₂) ⊢ (A₁ ⊗ A₂)
    split : {!   !}

    listᵍ : 𝓒 → 𝓒
    nil : ∀ {A} → ⊤ ⨾ zero ⊢ listᵍ A
    cons : ∀ {Δ₁ Δ₂ q₁ q₂ A}
      → Δ₁ ⨾ q₁ ⊢ A
      → Δ₂ ⨾ q₂ ⊢ (listᵍ A)
      → (Δ₁ ⊗ Δ₂) ⨾ (q₁ + q₂) ⊢ (listᵍ A)
    foldrᵍ : ∀ {Δ q A B}
      → Δ ⨾ q ⊢ listᵍ A
      → ⊤ ⨾ zero ⊢ B
      → (A ⊗ B) ⨾ zero ⊢ B
      → Δ ⨾ q ⊢ B
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
giralf ._⋊ᵍ_ p A = {!   !}
giralf .store = {!   !}
giralf .release = {!   !}
giralf .⊤ .X = unit
giralf .⊤ .Φ triv = ret triv
giralf ._⊗_ A B .X = A .X ×⁺ B .X
giralf ._⊗_ A B .Φ (a , b) =
  bind (F _) (A .Φ a) λ a' →
  bind (F _) (B .Φ b) λ b' →
  ret (a' , b')
giralf .tensor e₁ e₂ .top (δ₁ , δ₂) =
  bind (F _) (e₁ .top δ₁) λ a₁ →
  bind (F _) (e₂ .top δ₂) λ a₂ →
  ret (a₁ , a₂)
giralf .tensor e₁ e₂ .bot (δ₁ , δ₂) =
  bind (F _) (e₁ .bot δ₁) λ a₁ →
  bind (F _) (e₂ .bot δ₂) λ a₂ →
  ret (a₁ , a₂)
giralf .tensor {Δ₁ = Δ₁} {Δ₂} {A₁ = A₁} {A₂} e₁ e₂ .square (δ₁ , δ₂) =
  let open ≤⁻-Reasoning (F _) in
  begin
    ( bind (F _) (e₁ .top δ₁) λ a₁ →
      bind (F _) (e₂ .top δ₂) λ a₂ →
      bind (F _) (A₁ .Φ a₁) λ a₁' →
      bind (F _) (A₂ .Φ a₂) λ a₂' →
      ret (a₁' , a₂')
    )
  ≡⟨ {! commutativity of effects  !} ⟩
    ( bind (F _) (e₁ .top δ₁) λ a₁ →
      bind (F _) (A₁ .Φ a₁) λ a₁' →
      bind (F _) (e₂ .top δ₂) λ a₂ →
      bind (F _) (A₂ .Φ a₂) λ a₂' →
      ret (a₁' , a₂')
    )
  ≡⟨⟩
    ( bind (F _) (bind (F _) (e₁ .top δ₁) (A₁ .Φ)) λ a₁' →
      bind (F _) (bind (F _) (e₂ .top δ₂) (A₂ .Φ)) λ a₂' →
      ret (a₁' , a₂')
    )
  ≲⟨ ≤⁻-mono
      (λ e →
        bind (F _) e λ a₁' →
        bind (F _) (bind (F _) (e₂ .top δ₂) (A₂ .Φ)) λ a₂' →
        ret (a₁' , a₂')
      )
      (e₁ .square δ₁)
  ⟩
    ( bind (F _) (bind (F _) (Δ₁ .Φ δ₁) (e₁ .bot)) λ a₁' →
      bind (F _) (bind (F _) (e₂ .top δ₂) (A₂ .Φ)) λ a₂' →
      ret (a₁' , a₂')
    )
  ≲⟨
    ≤⁻-mono {X = A₁ .X ⇀ F _} (bind (F _) (bind (F _) (Δ₁ .Φ δ₁) (e₁ .bot))) (λ-mono-≤⁻ λ a₁' →
    ≤⁻-mono (λ e → bind (F _) e λ a₂' → ret (a₁' , a₂')) (e₂ .square δ₂))
  ⟩
    ( bind (F _) (bind (F _) (Δ₁ .Φ δ₁) (e₁ .bot)) λ a₁' →
      bind (F _) (bind (F _) (Δ₂ .Φ δ₂) (e₂ .bot)) λ a₂' →
      ret (a₁' , a₂')
    )
  ≡⟨⟩
    ( bind (F _) (Δ₁ .Φ δ₁) λ δ₁' →
      bind (F _) (e₁ .bot δ₁') λ a₁' →
      bind (F _) (Δ₂ .Φ δ₂) λ δ₂' →
      bind (F _) (e₂ .bot δ₂') λ a₂' →
      ret (a₁' , a₂')
    )
  ≡⟨ {! commutativity of effects  !} ⟩
    ( bind (F _) (Δ₁ .Φ δ₁) λ δ₁' →
      bind (F _) (Δ₂ .Φ δ₂) λ δ₂' →
      bind (F _) (e₁ .bot δ₁') λ a₁' →
      bind (F _) (e₂ .bot δ₂') λ a₂' →
      ret (a₁' , a₂')
    )
  ∎
giralf .split = {!   !}
giralf .listᵍ A .X = list (A .X)
giralf .listᵍ A .Φ [] = ret []
giralf .listᵍ A .Φ (a ∷ l) =
  bind (F _) (A .Φ a) λ a' →
  bind (F _) (giralf .listᵍ A .Φ l) λ l' →
  ret (a' ∷ l')
giralf .nil .top triv = ret []
giralf .nil .bot triv = ret []
giralf .nil .square triv = ≤⁻-refl
giralf .cons e₁ e₂ = {!   !}
giralf .foldrᵍ = {!   !}
