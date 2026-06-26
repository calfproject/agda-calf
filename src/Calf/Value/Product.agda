module Calf.Value.Product where

open import Cubical.Data.Sigma
  using (_×_; _,_)
  renaming (fst to proj₁; snd to proj₂)
  public
open import Cubical.Foundations.HLevels using (isSet×) public
open import Calf.Value

isPreorder× : isPreorder X → isPreorder Y → isPreorder (X × Y)
isPreorder× = {!   !}
