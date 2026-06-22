module Calf.Computation.Copower where

open import Calf.Value
open import Calf.Computation
open import Cubical.Foundations.Prelude using (cong)
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma public
open import Function

Σᶜ : (X : 𝒱) → (X → 𝒞) → 𝒞
Σᶜ X A .U = Σ[ x ∈ X ] U (A x)
Σᶜ X A .is-set = isSetΣ {!   !} λ x → A x .is-set
Σᶜ X A .charge c (x , a) = x , A x .charge c a
Σᶜ X A .charge/0 {x , a} = cong (x ,_) (A x .charge/0)
Σᶜ X A .charge/+ {x , a} = cong (x ,_) (A x .charge/+)

syntax Σᶜ X (λ x → A) = [ x ∈ X ] ⋊ A

_⋊_ : 𝒱 → 𝒞 → 𝒞
X ⋊ A = Σᶜ X (const A)
