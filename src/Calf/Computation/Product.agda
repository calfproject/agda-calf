module Calf.Computation.Product where

open import Calf.Computation
open import Calf.Value.Product public

_×ᶜ_ : 𝒞 → 𝒞 → 𝒞
(A ×ᶜ B) .U = A .U ×ᵛ B .U
(A ×ᶜ B) .charge c e .fst = A .charge c (e .fst)
(A ×ᶜ B) .charge c e .snd = B .charge c (e .snd)
(A ×ᶜ B) .charge/0 {e} i .fst = A .charge/0 {e .fst} i
(A ×ᶜ B) .charge/0 {e} i .snd = B .charge/0 {e .snd} i
(A ×ᶜ B) .charge/+ {e} {c₁} {c₂} i .fst = A .charge/+ {e .fst} {c₁} {c₂} i
(A ×ᶜ B) .charge/+ {e} {c₁} {c₂} i .snd = B .charge/+ {e .snd} {c₁} {c₂} i
