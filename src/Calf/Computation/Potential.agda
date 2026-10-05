module Calf.Computation.Potential where

open import Cubical.Foundations.Univalence using (ua→; ua-gluePath)

open import Calf.Core.Cost
open import Calf.Value
open import Calf.Value.Closed as ●
open import Calf.Computation
open import Calf.Computation.Abstraction
open import Calf.Computation.Closed as ●ᶜ
open import Calf.Computation.Copower
open import Calf.Computation.Credit
open import Calf.Computation.Free
open import Calf.Computation.Glue hiding (square; squareᶜ)
open import Calf.Computation.Open as ◯ᶜ
open import Calf.Computation.Top

Potential : (X → ℂ) → 𝒞
Potential {X} Φ = Abstractionᶜ (costed (id {X}) Φ)

square : {ΦX : X → ℂ} {ΦY : Y → ℂ}
  → (f : X → Y)
  → (c-⊤ c-abs : X → ℂ)
  → (∀ x → c-⊤ x +ℂ ΦY (f x) ≡ ΦX x +ℂ c-abs x)
  → Potential ΦX ⊸ Potential ΦY
square {ΦX = ΦX} {ΦY = ΦY} f c-⊤ c-abs amortization =
  squareᶜ (costed id ΦX) (costed id ΦY)
    (costed f c-⊤)
    (costed f c-abs)
    (funExtᶜ⁻ $
      costed-⨾ᶜ f c-⊤ id ΦY
      ∙ costed-cong (λ _ → refl) amortization
      ∙ sym (costed-⨾ᶜ id ΦX f c-abs))

Σᶜ-Abstractionᶜ : {A-⊤ A-abs : ⟨ X₌ ⟩ → 𝒞} (α : (x : ⟨ X₌ ⟩) → A-⊤ x ⊸ A-abs x)
  → Abstractionᶜ (Σᶜ-map {hA = {!   !}} {{!   !}} α) ≃ᶜ Σᶜ₌ X₌ (Abstractionᶜ ∘ α)
Σᶜ-Abstractionᶜ {X₌} {A-⊤} {A-abs} α = {!   !}
--     cong fromFractureᶜ fracture-proof ∙ glue-fracture-retractᶜ _
--     where
--       Abs : ⟨ X ⟩ → 𝒞
--       Abs x = Abstractionᶜ (A-⊤ x) (A-abs x) (α x)

--       fracture-proof :
--         Abstractionᶜ-Fracture (Σᶜ₌ X A-⊤) (Σᶜ₌ X A-abs) (Σᶜ-map α) ≡ toFractureᶜ (Σᶜ₌ X Abs)
--       fracture-proof =
--           Abstractionᶜ-Fracture (Σᶜ₌ X A-⊤) (Σᶜ₌ X A-abs) (Σᶜ-map α)
--         ≡⟨ Fractureᶜ-path-U
--               (Σᶜ-●ᶜ X A-⊤)
--               (Σᶜ-◯ᶜ X A-abs)
--               (Σᶜ-fracture-map-path X A-⊤ A-abs
--                 (Σᶜ-map α ⨾ᶜ η◦ᶜ {Σᶜ₌ X A-abs})
--                 (λ x → ●ᶜ.map (α x ⨾ᶜ η◦ᶜ {A-abs x}))
--                 (λ x a → refl)) ⟩
--           record
--             { A• = ●ᶜ• (Σᶜ₌ X (●ᶜ ∘ A-⊤))
--             ; A◦ = ◯ᶜ◦ (Σᶜ₌ X (◯ᶜ ∘ A-abs))
--             ; α• = Σᶜ-fracture-map X {●ᶜ ∘ A-⊤} {◯ᶜ ∘ A-abs} (λ x → ●ᶜ.map (α x ⨾ᶜ η◦ᶜ {A-abs x}))
--             }
--         ≡⟨ Fractureᶜ-path-U
--               (cong (●ᶜ ∘ Σᶜ₌ X) (funExt λ x → sym (●ᶜ-Abstractionᶜ (α x))))
--               (cong (◯ᶜ ∘ Σᶜ₌ X) (funExt λ x → sym (◯ᶜ-Abstractionᶜ (α x))))
--               (congP (λ _ → Σᶜ-fracture-map X)
--                 (funExt λ x → Abstractionᶜ-coherence (α x))) ⟩
--           record
--             { A• = ●ᶜ• (Σᶜ₌ X (●ᶜ ∘ Abs))
--             ; A◦ = ◯ᶜ◦ (Σᶜ₌ X (◯ᶜ ∘ Abs))
--             ; α• = Σᶜ-fracture-map X {●ᶜ ∘ Abs} {◯ᶜ ∘ Abs} (λ x → ●ᶜ.map (η◦ᶜ {Abs x}))
--             }
--         ≡⟨ Fractureᶜ-path-U
--               (sym (Σᶜ-●ᶜ X Abs))
--               (sym (Σᶜ-◯ᶜ X Abs))
--               (symP (Σᶜ-fracture-map-path X Abs Abs
--                 (η◦ᶜ {Σᶜ₌ X Abs})
--                 (λ x → ●ᶜ.map (η◦ᶜ {Abs x}))
--                 (λ x a → refl))) ⟩
--           toFractureᶜ (Σᶜ₌ X Abs)
--         ∎

-- Σᶜ-map-chargeᶜ : ∀ {A : ⟨ X₌ ⟩ → 𝒞} c → Σᶜ-map {A = A} {B = A} (λ _ → chargeᶜ c) ≡ chargeᶜ {A = Σᶜ₌ X₌ A} c
-- Σᶜ-map-chargeᶜ c = funExtᶜ λ _ → refl

opaque
  unfolding ▷[_]_

--   ▷-Σᶜ : ∀ {A : ⟨ X₌ ⟩ → 𝒞} c → ▷[ c ] Σᶜ₌ X₌ A ≡ Σᶜ₌ X₌ (λ x → ▷[ c ] A x)
--   ▷-Σᶜ {X} {A} c =
--     cong (Abstractionᶜ (Σᶜ₌ X A) (Σᶜ₌ X A)) (sym (Σᶜ-map-chargeᶜ c)) ∙ Σᶜ-Abstractionᶜ (λ _ → chargeᶜ c)

  Potential-credit : ∀ Φ → Potential Φ ≃ᶜ [ x ∈ X₌ ] ⋊ (▷[ Φ x ] ⊤)
  Potential-credit {X₌} Φ =
      Potential Φ
    ≃ᶜ⟨ idEquivᶜ _ ⟩
      Abstractionᶜ {F ⟨ X₌ ⟩} {F ⟨ X₌ ⟩} (costed id Φ)
    ≃ᶜ⟨ Abstractionᶜ-≃ {!   !} {!   !} {!   !} ⟩
      Abstractionᶜ {[ x ∈ X₌ ] ⋊ ⊤} {[ x ∈ X₌ ] ⋊ ⊤} (Σᶜ-map (chargeᶜ ∘ Φ))
    ≃ᶜ⟨ Σᶜ-Abstractionᶜ (chargeᶜ ∘ Φ) ⟩
      [ x ∈ X₌ ] ⋊ (▷[ Φ x ] ⊤)
    ■ᶜ
