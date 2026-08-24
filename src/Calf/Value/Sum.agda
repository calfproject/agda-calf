module Calf.Value.Sum where

open import Calf.Value
open import Cubical.Data.Sum renaming (inl to inj₁; inr to inj₂) public
open import Cubical.Data.Empty renaming (elim to elim-⊥; rec to rec-⊥) public
