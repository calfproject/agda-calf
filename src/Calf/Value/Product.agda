module Calf.Value.Product where

open import Calf.Value
open import Cubical.Data.Sigma public
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

infixr 2 _×ᵛ_
_×ᵛ_ : 𝒱 → 𝒱 → 𝒱
(X ×ᵛ Y) .val = val X × val Y
(X ×ᵛ Y) .is-set = isSet× (X .is-set) (Y .is-set)
(X ×ᵛ Y) .is-preorder = {!   !}
-- .ortho g .fst .fst 𝕚₂ .fst = X .is-preorder .ortho (fst ∘ g) .fst .fst 𝕚₂
-- (X ×ᵛ Y) .is-preorder .ortho g .fst .fst 𝕚₂ .snd = Y .is-preorder .ortho (snd ∘ g) .fst .fst 𝕚₂
-- (X ×ᵛ Y) .is-preorder .ortho g .fst .snd i 𝕚∨𝕚 .fst =
--   X .is-preorder .ortho (fst ∘ g) .fst .snd i 𝕚∨𝕚
-- (X ×ᵛ Y) .is-preorder .ortho g .fst .snd i 𝕚∨𝕚 .snd =
--   Y .is-preorder .ortho (snd ∘ g) .fst .snd i 𝕚∨𝕚
-- (X ×ᵛ Y) .is-preorder .ortho g .snd y i .fst 𝕚₂ .fst =
--   X .is-preorder .ortho (fst ∘ g) .snd
--     ((λ 𝕚₂ → y .fst 𝕚₂ .fst) , λ j 𝕚∨𝕚 → y .snd j 𝕚∨𝕚 .fst)
--     i .fst 𝕚₂
-- (X ×ᵛ Y) .is-preorder .ortho g .snd y i .fst 𝕚₂ .snd =
--   Y .is-preorder .ortho (snd ∘ g) .snd
--     ((λ 𝕚₂ → y .fst 𝕚₂ .snd) , λ j 𝕚∨𝕚 → y .snd j 𝕚∨𝕚 .snd)
--     i .fst 𝕚₂
-- (X ×ᵛ Y) .is-preorder .ortho g .snd y i .snd j 𝕚∨𝕚 .fst =
--   X .is-preorder .ortho (fst ∘ g) .snd
--     ((λ 𝕚₂ → y .fst 𝕚₂ .fst) , λ j 𝕚∨𝕚 → y .snd j 𝕚∨𝕚 .fst)
--     i .snd j 𝕚∨𝕚
-- (X ×ᵛ Y) .is-preorder .ortho g .snd y i .snd j 𝕚∨𝕚 .snd =
--   Y .is-preorder .ortho (snd ∘ g) .snd
--     ((λ 𝕚₂ → y .fst 𝕚₂ .snd) , λ j 𝕚∨𝕚 → y .snd j 𝕚∨𝕚 .snd)
--     i .snd j 𝕚∨𝕚
