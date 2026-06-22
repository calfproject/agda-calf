module Calf.Value where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.PathSplit
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.HITs.Join
open import Cubical.HITs.Localization
open import Relation.Binary using (_⇒_)
open import Relation.Binary.Definitions


𝒱 = Type


-- record 𝒱 : Type₁ where
--   field
--     val : Type
--     is-set : isSet val
-- open 𝒱 public

-- 𝒱-path : {X Y : 𝒱} → val X ≡ val Y → X ≡ Y
-- 𝒱-path {X} {Y} p i .val = p i
-- 𝒱-path {X} {Y} p i .is-set =
--   isProp→PathP
--     (λ i → isPropIsSet {_} {p i})
--     (X .is-set)
--     (Y .is-set)
--     i

variable
  X Y Z : 𝒱

-- fromProp : hProp ℓ-zero → 𝒱
-- fromProp P .val = ⟨ P ⟩
-- fromProp P .is-set = isProp→isSet (P .snd)
