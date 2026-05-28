module Calf.Value where

open import Calf.Core.Directed
open import Calf.Core.Directed using (BEH) public
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


𝒱 : Type₁
𝒱 = hSet ℓ-zero

val : 𝒱 → Type
val = ⟨_⟩

variable
  X Y Z : 𝒱

𝒱-path : val X ≡ val Y → X ≡ Y
𝒱-path = TypeOfHLevel≡ 2
