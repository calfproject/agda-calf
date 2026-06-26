module Calf.Value.Sigma where

open import Cubical.Data.Sigma
  using (Σ; _,_)
  renaming (fst to proj₁; snd to proj₂)
  public
