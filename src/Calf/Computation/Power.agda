module Calf.Computation.Power where

open import Calf.Value
open import Calf.Computation
open import Calf.Value.Pi public
open import Function
open import Cubical.Foundations.Prelude

Πᶜ : (X : 𝒱) → (val X → 𝒞) → 𝒞
Πᶜ X A .U = Πᵛ X (U ∘ A)
Πᶜ X A .charge c e x = A x .charge c (e x)
Πᶜ X A .charge/0 {e} = funExt λ x → A x .charge/0 {e x}
Πᶜ X A .charge/+ {e} {c₁} {c₂} = funExt λ x → A x .charge/+ {e x} {c₁} {c₂}

syntax Πᶜ X (λ x → A) = [ x ∈ X ] ⇀ A

_⇀_ : 𝒱 → 𝒞 → 𝒞
X ⇀ A = Πᶜ X (const A)

opaque
  powlam : (val X → A ⊸ B) → A ⊸ (X ⇀ B)
  powlam e .U a x = e x .U a
  powlam e .charge c a = funExt (λ x → e x .charge c a)

  powapp : A ⊸ (X ⇀ B) → val X → A ⊸ B
  powapp e x .U a = e .U a x
  powapp e x .charge c a = cong (λ f → f x) (e .charge c a)
