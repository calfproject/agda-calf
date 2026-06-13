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
Πᶜ X A .seal e e◦ e⊑e◦ x = A x .seal (e x) (λ abs → e◦ abs x) (λ abs → ⊑ᵛ-mono {Πᵛ X (U ∘ A)} {U (A x)} (_$ x) (e⊑e◦ abs))
Πᶜ X A .seal/abs abs = funExt λ x → A x .seal/abs abs
Πᶜ X A .seal/unit = funExt λ x → A x .seal/unit
Πᶜ X A .seal/mult = funExt λ x → A x .seal/mult
Πᶜ X A .seal/charge = funExt λ x → A x .seal/charge

syntax Πᶜ X (λ x → A) = [ x ∈ X ] ⇀ A

_⇀_ : 𝒱 → 𝒞 → 𝒞
X ⇀ A = Πᶜ X (const A)
