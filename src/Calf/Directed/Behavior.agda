module Calf.Directed.Behavior where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit using (isContrUnit; terminal)
open import Cubical.Foundations.Equiv.Properties using (isEquivPreComp; isEquivFromIsContr)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.PathSplit
open import Cubical.Foundations.Function

open import Calf.Core.Interval
open import Calf.Directed.Discrete
open import Calf.Directed.Path

private variable X Y : Type

BEH : Type
BEH = 0𝟚 ≡ 1𝟚

isPropBEH : isProp BEH
isPropBEH = isSet𝟚 0𝟚 1𝟚

isAlgorithmic : Type → Type
isAlgorithmic X = BEH → isContr X

isAlgorithmic𝟚 : isAlgorithmic 𝟚
isAlgorithmic𝟚 beh .fst = 0𝟚
isAlgorithmic𝟚 beh .snd i =
  ≤𝟚-antisym
    (0𝟚-minimum _)
    (≤𝟚-trans (1𝟚-maximum _) (subst (_≤𝟚 0𝟚) beh ≤𝟚-refl))

⊑-beh : BEH → isDiscrete X
⊑-beh beh _ =
  fromIsEquiv _ (isEquivPreComp (terminal 𝟚 , isEquivFromIsContr _ (isAlgorithmic𝟚 beh) isContrUnit))

⊑-beh' : BEH → {x x' : X} → x ⊑ x' → x ≡ x'
⊑-beh' beh = invIsEq (isDiscrete→isEquiv[⊑-reflexive] (⊑-beh beh))
