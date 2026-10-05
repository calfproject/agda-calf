module Calf.Computation.Empty where

open import Calf.Core.Cost
open import Calf.Value
open import Calf.Computation
open import Calf.Computation.Copower

open import Calf.Value.Empty public

0ᶜ : 𝒞
0ᶜ .U = ∥ 0ᵛ ∥ᴾ
0ᶜ .is-preorder = isPreorderᴾ
0ᶜ .charge _ = recᴾ isPreorderᴾ λ ()
0ᶜ .charge-0 {a} =
  recᴾ-unique {X = 0ᵛ} isPreorderᴾ (0ᶜ .charge 0ℂ) (λ x → x) (λ ()) a
0ᶜ .charge-+ {a} {c₁} {c₂} =
  cong (0ᶜ .charge c₁) (recᴾ-unique {X = 0ᵛ} isPreorderᴾ (λ x → x) (0ᶜ .charge c₂) (λ ()) a)

absurdᶜ : 0ᶜ ⊸ A
absurdᶜ {A} .U = recᴾ (A .is-preorder) λ ()
absurdᶜ {A} .charge c = recᴾ-unique (A .is-preorder) _ _ λ ()

Σᶜ-0ᵛ : ∀ {A} → Σᶜ₌ 0ᵛ₌ A ≃ᶜ 0ᶜ
Σᶜ-0ᵛ =
  invEquivᶜ $
    absurdᶜ ,
    isoToIsEquiv (iso _ (λ ()) (λ ()) (recᴾ-unique isPreorderᴾ _ _ λ ()))
