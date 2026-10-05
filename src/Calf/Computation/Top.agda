module Calf.Computation.Top where

open import Calf.Core.Cost
open import Calf.Computation

⊤ : 𝒞
⊤ .U = ℂ
⊤ .is-preorder = isPreorderℂ
⊤ .charge = _+ℂ_
⊤ .charge-0 = +ℂ-identityˡ _
⊤ .charge-+ = +ℂ-assoc _ _ _

rec : U A → ⊤ ⊸ A
rec {A} a .U c = A .charge c a
rec {A} a .charge c c' = A .charge-+
