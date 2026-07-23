module Calf.Computation.Power where

open import Calf.Value
open import Calf.Value.Pi
open import Calf.Computation

Πᶜ : (X : 𝒱) → (X → 𝒞) → 𝒞
Πᶜ X A .U = (x : X) → U (A x)
Πᶜ X A .is-preorder = isPreorderΠ λ x → A x .is-preorder
Πᶜ X A .charge c e x = A x .charge c (e x)
Πᶜ X A .charge/0 {e} = funExt λ x → A x .charge/0 {e x}
Πᶜ X A .charge/+ {e} {c₁} {c₂} = funExt λ x → A x .charge/+ {e x} {c₁} {c₂}

syntax Πᶜ X (λ x → A) = [ x ∈ X ] ⇀ A

infixr 2 _⇀_

_⇀_ : 𝒱 → 𝒞 → 𝒞
X ⇀ A = [ _ ∈ X ] ⇀ A

opaque
  powlam : (X → A ⊸ B) → A ⊸ (X ⇀ B)
  powlam e .U a x = e x .U a
  powlam e .charge c a = funExt λ x → e x .charge c a

  powapp : A ⊸ (X ⇀ B) → X → A ⊸ B
  powapp e x .U a = e .U a x
  powapp e x .charge c a = cong (_$ x) (e .charge c a)
