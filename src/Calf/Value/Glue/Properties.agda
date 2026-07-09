module Calf.Value.Glue.Properties where

open import Calf.Value
open import Calf.Value.Closed
open import Calf.Value.Glue.Base

isSetGlue : ∀ {X• X◦ χ•} → isSet ⟨ X• ⟩ → isSet ⟨ X◦ ⟩ → isSet (Glue X• X◦ χ•)
isSetGlue isSetX• isSetX◦ x x' h h' i j .• = isSetX• (x .•) (x' .•) (cong • h) (cong • h') i j
isSetGlue isSetX• isSetX◦ x x' h h' i j .◦ = isSetX◦ (x .◦) (x' .◦) (cong ◦ h) (cong ◦ h') i j
isSetGlue {χ• = χ•} isSetX• isSetX◦ x x' h h' i j .•→◦ =
  isSet→SquareP
    (λ k l → isProp→isSet
      (●-preserves-isSet isSetX◦
        (χ• (isSetX• (x .•) (x' .•) (cong • h) (cong • h') k l))
        (η• (isSetX◦ (x .◦) (x' .◦) (cong ◦ h) (cong ◦ h') k l))))
    (λ l → h l .•→◦)
    (λ l → h' l .•→◦)
    (λ _ → x .•→◦)
    (λ _ → x' .•→◦)
    i j
