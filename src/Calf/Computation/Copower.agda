module Calf.Computation.Copower where

open import Calf.Core.Directed
open import Calf.Value
open import Calf.Computation
open import Calf.Value.Sigma public
open import Cubical.Foundations.Prelude using (cong)
open import Function

Σᶜ : (X : 𝒱) ⦃ _ : isDiscreteᵛ X ⦄ → (val X → 𝒞) → 𝒞
Σᶜ X A .U = Σᵛ X (U ∘ A)
Σᶜ X A .charge c (x , a) = x , A x .charge c a
Σᶜ X A .charge/0 {x , a} = cong (x ,_) (A x .charge/0)
Σᶜ X A .charge/+ {x , a} = cong (x ,_) (A x .charge/+)

syntax Σᶜ X (λ x → A) = [ x ∈ X ] ⋊ A

_⋊_ : (X : 𝒱) ⦃ _ : isDiscrete (val X) ⦄ → 𝒞 → 𝒞
X ⋊ A = Σᶜ X (const A)
