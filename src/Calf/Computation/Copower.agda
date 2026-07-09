module Calf.Computation.Copower where

open import Calf.Value
open import Calf.Value.Product public
open import Calf.Value.Sigma public
open import Calf.Computation
open import Cubical.Foundations.Prelude using (cong)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

Σᶜ : isSet X × isDiscrete X → (X → 𝒞) → 𝒞
Σᶜ {X} (isSetX , isDiscreteX) A .U = Σ[ x ∈ X ] U (A x)
Σᶜ {X} (isSetX , isDiscreteX) A .is-preorder = isPreorderΣ isSetX isDiscreteX λ x → A x .is-preorder
Σᶜ {X} (isSetX , isDiscreteX) A .charge c (x , a) = x , A x .charge c a
Σᶜ {X} (isSetX , isDiscreteX) A .charge/0 {x , _} = cong (x ,_) (A x .charge/0)
Σᶜ {X} (isSetX , isDiscreteX) A .charge/+ {x , _} = cong (x ,_) (A x .charge/+)

syntax Σᶜ X (λ x → A) = [ x ∈ X ] ⋊ A

_⋊_ : 𝒱ₚ → 𝒞 → 𝒞
(X ⋊ A) .U = ⟨ X ⟩ × U A
(X ⋊ A) .is-preorder = isPreorder× (str X) (A .is-preorder)
(X ⋊ A) .charge c (x , a) = x , A .charge c a
(X ⋊ A) .charge/0 {x , _} = cong (x ,_) (A .charge/0)
(X ⋊ A) .charge/+ {x , _} = cong (x ,_) (A .charge/+)
