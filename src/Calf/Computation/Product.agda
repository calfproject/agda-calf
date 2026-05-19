module Calf.Computation.Product where

open import Calf.Computation
open import Calf.Value.Product public

_×ᶜ_ : 𝒞 → 𝒞 → 𝒞
(A ×ᶜ B) .U = A .U ×ᵛ B .U
(A ×ᶜ B) .charge c e .proj₁ = A .charge c (e .proj₁)
(A ×ᶜ B) .charge c e .proj₂ = B .charge c (e .proj₂)
(A ×ᶜ B) .charge/0 {e} i .proj₁ = A .charge/0 {e .proj₁} i
(A ×ᶜ B) .charge/0 {e} i .proj₂ = B .charge/0 {e .proj₂} i
(A ×ᶜ B) .charge/+ {e} {c₁} {c₂} i .proj₁ = A .charge/+ {e .proj₁} {c₁} {c₂} i
(A ×ᶜ B) .charge/+ {e} {c₁} {c₂} i .proj₂ = B .charge/+ {e .proj₂} {c₁} {c₂} i
