module Calf.Value.Sigma where

open import Cubical.Data.Sigma
  using (Σ; _,_)
  renaming (fst to proj₁; snd to proj₂)
  public
open import Cubical.Foundations.HLevels using (isSetΣ) public
open import Calf.Value

isPreorderΣ : {Y : X → 𝒱} ⦃ _ : isDiscrete X ⦄
  → ((x : X) → isPreorder (Y x))
  → isPreorder (Σ X Y)
isPreorderΣ = {!   !}
