module Calf.Value.Sigma where

open import Cubical.Data.Sigma
  using (Σ; _,_)
  renaming (fst to proj₁; snd to proj₂)
  public
open import Cubical.Foundations.HLevels using (isSetΣ) public
open import Cubical.Foundations.Equiv using (isEquiv)
open import Calf.Value

opaque
  unfolding Fᴾ

  isPreorderΣ : {Y : X → 𝒱}
    → isSet X
    → isDiscrete X
    → ((x : X) → isPreorder (Y x))
    → isPreorder (Σ X Y)
  isPreorderΣ {X} isSetX isDiscreteX isPreorderY =
    isLocalΣ (isSet∧isDiscrete→isPreorder isSetX isDiscreteX) nullT isPreorderY
    where
      nullT : (α : Requirements) → isEquiv (const {A = X} {B = Tᴾ α})
      nullT transitive = null[Δ²] isSetX isDiscreteX
      nullT thin = null[𝕊Unit] isDiscreteX
      nullT hset = null[Unit]
