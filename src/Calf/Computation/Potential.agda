module Calf.Computation.Potential where

open import Cubical.Foundations.Prelude

open import Calf.Core.Cost
open import Calf.Value
open import Calf.Computation
open import Calf.Computation.Abstraction
open import Calf.Computation.Free

Potential : (X → ℂ) → 𝒞
Potential {X} Φ = Abstractionᶜ (F X) (F X) (bind' λ x → F _ .charge (Φ x) (ret x))

Potential-0ℂ : Potential {X} (λ _ → 0ℂ) ≡ F X
Potential-0ℂ =
  cong (Abstractionᶜ _ _) (cong bind' (funExt λ _ → F _ .charge/0) ∙ bind'/η)
  ∙ Abstractionᶜ-id

square : {ΦX : X → ℂ} {ΦY : Y → ℂ}
  → (f : X → Y)
  → (c-⊤ c-abs : X → ℂ)
  → (∀ x → c-⊤ x +ℂ ΦY (f x) ≡ ΦX x +ℂ c-abs x)
  → Potential ΦX ⊸ Potential ΦY
square {ΦX = ΦX} {ΦY = ΦY} f c-⊤ c-abs amortization =
  squareᶜ'
    (bind' λ x → F _ .charge (c-⊤ x) (ret (f x)))
    (bind' λ x → F _ .charge (c-abs x) (ret (f x)))
    λ a-⊤ →
        bind' (λ x → F _ .charge (ΦY x) (ret x)) .U
        (bind' (λ x → F _ .charge (c-⊤ x) (ret (f x))) .U a-⊤)
      ≡⟨ {!   !} ⟩
        bind' (λ x → F _ .charge (c-⊤ x +ℂ ΦY (f x)) (ret (f x))) .U a-⊤
      ≡⟨ cong (λ e → bind' {A = F _} e .U a-⊤) (funExt λ x → cong (λ e → F _ .charge e _) (amortization x)) ⟩
        bind' (λ x → F _ .charge (ΦX x +ℂ c-abs x) (ret (f x))) .U a-⊤
      ≡⟨ {!   !} ⟩
        bind' (λ x → F _ .charge (c-abs x) (ret (f x))) .U
        (bind' (λ x → F _ .charge (ΦX x) (ret x)) .U a-⊤)
      ∎
