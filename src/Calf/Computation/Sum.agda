module Calf.Computation.Sum where

open import Calf.Computation
open import Cubical.Foundations.Prelude using (cong)
open import Cubical.Data.Sum public

_+ᶜ_ : 𝒞 → 𝒞 → 𝒞
(A +ᶜ B) .U = A .U ⊎ B .U
(A +ᶜ B) .is-set = isSet⊎ (A .is-set) (B .is-set)
(A +ᶜ B) .charge c (inl a) = inl (A .charge c a)
(A +ᶜ B) .charge c (inr b) = inr (B .charge c b)
(A +ᶜ B) .charge/0 {inl a} = cong inl (A .charge/0)
(A +ᶜ B) .charge/0 {inr b} = cong inr (B .charge/0)
(A +ᶜ B) .charge/+ {inl a} = cong inl (A .charge/+)
(A +ᶜ B) .charge/+ {inr b} = cong inr (B .charge/+)
