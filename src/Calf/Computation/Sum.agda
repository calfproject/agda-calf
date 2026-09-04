module Calf.Computation.Sum where

open import Calf.Value
open import Calf.Computation

open import Calf.Value.Sum public

_+ᶜ_ : 𝒞 → 𝒞 → 𝒞
(A +ᶜ B) .U = A .U ⊎ B .U
(A +ᶜ B) .is-preorder = isPreorder⊎ (A .is-preorder) (B .is-preorder)
(A +ᶜ B) .charge c (inj₁ a) = inj₁ (A .charge c a)
(A +ᶜ B) .charge c (inj₂ b) = inj₂ (B .charge c b)
(A +ᶜ B) .charge-0 {inj₁ a} = cong inj₁ (A .charge-0)
(A +ᶜ B) .charge-0 {inj₂ b} = cong inj₂ (B .charge-0)
(A +ᶜ B) .charge-+ {inj₁ a} = cong inj₁ (A .charge-+)
(A +ᶜ B) .charge-+ {inj₂ b} = cong inj₂ (B .charge-+)
