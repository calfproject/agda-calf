module Calf.Value.Product where

open import Calf.Value
open import Data.Product public
open import Cubical.Foundations.Function

infixr 2 _×ᵛ_
_×ᵛ_ : 𝒱 → 𝒱 → 𝒱
(X ×ᵛ Y) .val = val X × val Y
(X ×ᵛ Y) .isPreorder g .proj₁ .proj₁ 𝕚₂ .proj₁ = X .isPreorder (proj₁ ∘ g) .proj₁ .proj₁ 𝕚₂
(X ×ᵛ Y) .isPreorder g .proj₁ .proj₁ 𝕚₂ .proj₂ = Y .isPreorder (proj₂ ∘ g) .proj₁ .proj₁ 𝕚₂
(X ×ᵛ Y) .isPreorder g .proj₁ .proj₂ = {!   !}
(X ×ᵛ Y) .isPreorder g .proj₂ = {!   !}
