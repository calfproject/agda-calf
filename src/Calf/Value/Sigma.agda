module Calf.Value.Sigma where

open import Cubical.Data.Sigma
  using (Σ; _,_; ΣPathP)
  renaming (fst to proj₁; snd to proj₂)
  public
open import Cubical.Data.Sigma.Properties public
open import Cubical.Foundations.HLevels using (isSetΣ) public
open import Cubical.Foundations.Equiv using (isEquiv)
open import Calf.Value

opaque
  unfolding Fᴾ

  isPreorderΣ : (X : 𝒱ₛ) {Y : ⟨ X ⟩ → 𝒱}
    → ((x : ⟨ X ⟩) → isPreorder (Y x))
    → isPreorder (Σ ⟨ X ⟩ Y)
  isPreorderΣ X isPreorderY =
    isLocalΣ (isSet∧isDiscrete→isPreorder (str X .fst) (str X .snd)) nullT isPreorderY
    where
      nullT : (α : Requirements) → isEquiv (const {A = ⟨ X ⟩} {B = Tᴾ α})
      nullT transitive = null[Δ²] (str X .fst) (str X .snd)
      nullT thin = null[𝕊Unit] (str X .snd)
      nullT hset = null[Unit]
