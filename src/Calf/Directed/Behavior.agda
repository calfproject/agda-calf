module Calf.Directed.Behavior where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.PathSplit
open import Cubical.Foundations.Function

open import Calf.Core.Interval
open import Calf.Directed.Discrete
open import Calf.Directed.Path

private variable X Y : Type

BEH : Type
BEH = 0𝟚 ≡ 1𝟚

BEH-isProp : isProp BEH
BEH-isProp = isSet𝟚 0𝟚 1𝟚

𝟚-isAlgorithmic : BEH → isContr 𝟚
𝟚-isAlgorithmic beh .fst = 0𝟚
𝟚-isAlgorithmic beh .snd i =
  ≤𝟚-antisym
    (0𝟚-minimum _)
    (≤𝟚-trans (1𝟚-maximum _) (subst (_≤𝟚 0𝟚) beh ≤𝟚-refl))

open isPathSplitEquiv

⊑-beh : BEH → isDiscrete X
⊑-beh beh _ .sec .fst f _ = f 0𝟚
⊑-beh beh _ .sec .snd f =
  funExt (cong (f $_) ∘ isContr→isProp (𝟚-isAlgorithmic beh) 0𝟚)
⊑-beh beh _ .secCong g g' .fst p = funExt λ _ → cong (_$ 0𝟚) p
⊑-beh beh _ .secCong g g' .snd p i j 𝕚 =
  p j (isContr→isProp (𝟚-isAlgorithmic beh) 0𝟚 𝕚 i)

⊑-beh' : BEH → {x x' : X} → x ⊑ x' → x ≡ x'
⊑-beh' beh = invIsEq (isDiscrete→isEquiv[≡⇒⊑] (⊑-beh beh))
