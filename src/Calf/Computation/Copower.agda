module Calf.Computation.Copower where

open import Calf.Value
open import Calf.Value.Product public
open import Calf.Value.Sigma public
open import Calf.Computation
open import Cubical.Foundations.Prelude using (cong)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

Σᶜ : (X : 𝒱ₛ) ⦃ _ : isDiscrete (val X) ⦄ → (X .val → 𝒞) → 𝒞
Σᶜ X A .U = Σ[ x ∈ val X ] U (A x)
Σᶜ X A .is-set = isSetΣ (X .is-set) λ x → A x .is-set
Σᶜ X A .charge c (x , a) = x , A x .charge c a
Σᶜ X A .charge/0 {x , _} = cong (x ,_) (A x .charge/0)
Σᶜ X A .charge/+ {x , _} = cong (x ,_) (A x .charge/+)

syntax Σᶜ X (λ x → A) = [ x ∈ X ] ⋊ A

_⋊_ : 𝒱ₛ → 𝒞 → 𝒞
(X ⋊ A) .U = val X × U A
(X ⋊ A) .is-set = isSet× (X .is-set) (A .is-set)
(X ⋊ A) .charge c (x , a) = x , A .charge c a
(X ⋊ A) .charge/0 {x , _} = cong (x ,_) (A .charge/0)
(X ⋊ A) .charge/+ {x , _} = cong (x ,_) (A .charge/+)
