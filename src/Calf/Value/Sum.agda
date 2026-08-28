module Calf.Value.Sum where

open import Calf.Core.Directed
open import Calf.Value
open import Cubical.Data.Sum renaming (inl to inj₁; inr to inj₂) public

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool
open import Calf.Value.Bool
open import Calf.Value.Sigma

isPreorder⊎ : isPreorder X → isPreorder Y → isPreorder (X ⊎ Y)
isPreorder⊎ {X} {Y} isPreorderX isPreorderY =
  isLocalRetract to from (λ { (inj₁ _) → refl ; (inj₂ _) → refl })
    (isPreorderΣ Bool₌ λ { false → isPreorderX ; true → isPreorderY })
  where
    to : X ⊎ Y → Σ Bool (if_then Y else X)
    to (inj₁ x) = false , x
    to (inj₂ y) = true , y

    from : Σ Bool (if_then Y else X) → X ⊎ Y
    from (false , v) = inj₁ v
    from (true , v) = inj₂ v
