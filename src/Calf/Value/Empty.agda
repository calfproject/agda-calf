module Calf.Value.Empty where

open import Calf.Value
open import Cubical.Data.Empty public

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma

0ᵛ : 𝒱
0ᵛ .val = ⊥
0ᵛ .isPreorder .ortho g .fst .fst (𝕚 , _) = g (inj₀ 𝕚)
0ᵛ .isPreorder .ortho g .fst .snd = funExt λ 𝕚∨𝕚 → isProp⊥ _ _
0ᵛ .isPreorder .ortho g .snd _ = ΣPathP ((funExt λ _ → isProp⊥ _ _) , {!   !})
