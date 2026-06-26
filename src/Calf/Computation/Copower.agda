module Calf.Computation.Copower where

open import Calf.Value
open import Calf.Value.Sigma public
open import Calf.Computation
open import Cubical.Foundations.Prelude using (cong)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

Σᶜ : (X : 𝒱ₛ) → (⟨ X ⟩ → 𝒞) → 𝒞
Σᶜ isSetX A .U = Σ[ x ∈ _ ] U (A x)
Σᶜ isSetX A .is-set = isSetΣ (str isSetX) λ x → A x .is-set
Σᶜ isSetX A .charge c (x , a) = x , A x .charge c a
Σᶜ isSetX A .charge/0 {x , a} = cong (x ,_) (A x .charge/0)
Σᶜ isSetX A .charge/+ {x , a} = cong (x ,_) (A x .charge/+)

syntax Σᶜ X (λ x → A) = [ x ∈ X ] ⋊ A

_⋊_ : 𝒱ₛ → 𝒞 → 𝒞
X ⋊ A = [ _ ∈ X ] ⋊ A
