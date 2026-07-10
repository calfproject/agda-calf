module Calf.Value.Sigma where

open import Cubical.Data.Sigma
  using (Σ; _,_; ΣPathP)
  renaming (fst to proj₁; snd to proj₂)
  public
