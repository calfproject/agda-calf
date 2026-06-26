module Calf.Value.Unit where

open import Calf.Value
open import Cubical.Data.Unit public
open import Cubical.Foundations.Prelude

open import Cubical.Data.Unit
  renaming (Unit to ⊤; isSetUnit to isSet⊤)
  public

instance
  isDiscrete⊤ : isDiscrete ⊤
  isDiscrete⊤ .is-discrete _ .sec = (λ _ _ → tt) , (λ _ → refl)
  isDiscrete⊤ .is-discrete _ .secCong _ _ = (λ _ → refl) , (λ _ → refl)

isPreorder⊤ : isPreorder ⊤
isPreorder⊤ = isDiscrete→isPreorder
