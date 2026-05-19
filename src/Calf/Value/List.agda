module Calf.Value.List where

open import Calf.Value
open import Cubical.Data.List
  using (List; []; _∷_; _++_; [_]; length)
  renaming (rev to reverse)
  public

Listᵛ : 𝒱 → 𝒱
Listᵛ X .val = List (X .val)
Listᵛ X .isPreorder = {!   !}
