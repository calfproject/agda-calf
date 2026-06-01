module Calf.Computation.Power where

open import Calf.Value
open import Calf.Computation
open import Calf.Value.Pi public
open import Function

Πᶜ : (X : 𝒱) → (val X → 𝒞) → 𝒞
Πᶜ X A .U = Πᵛ X (U ∘ A)
Πᶜ X A .charge c e x = A x .charge c (e x)
Πᶜ X A .charge/0 {e} i x = A x .charge/0 {e x} i
Πᶜ X A .charge/+ {e} {c₁} {c₂} i x = A x .charge/+ {e x} {c₁} {c₂} i
Πᶜ X A .seal = {!   !}
Πᶜ X A .seal/abs = {!   !}
Πᶜ X A .seal/charge = {!   !}

syntax Πᶜ X (λ x → A) = [ x ∈ X ] ⇀ A

_⇀_ : 𝒱 → 𝒞 → 𝒞
X ⇀ A = Πᶜ X (const A)
