module Calf.Value.Abstraction where

open import Cubical.Foundations.GroupoidLaws using (rUnit)
open import Cubical.Foundations.Univalence

open import Calf.Core.Abstract
open import Calf.Value
open import Calf.Value.Closed as ●
open import Calf.Value.Glue as Glue hiding (square)
open import Calf.Value.Open as ◯

open Fracture

Abstraction-Fracture : {X-⊤ X-abs : 𝒱} → (X-⊤ → X-abs) → Fracture
Abstraction-Fracture {X-⊤} {X-abs} χ .X• = ●• X-⊤
Abstraction-Fracture {X-⊤} {X-abs} χ .X◦ = ◯◦ X-abs
Abstraction-Fracture {X-⊤} {X-abs} χ .χ• = ●.map (χ ⨾ η◦)

Abstraction : {X-⊤ X-abs : 𝒱} → (X-⊤ → X-abs) → 𝒱
Abstraction = fromFracture ∘ Abstraction-Fracture

Abstraction-id : (X : 𝒱) → X ≃ Abstraction (id {X})
Abstraction-id X = fracture , fracture-isEquiv

square
  : ∀ {X-⊤ X-abs Y-⊤ Y-abs}
  → (χ : X-⊤ → X-abs) (ψ : Y-⊤ → Y-abs)
  → (f-⊤ : X-⊤ → Y-⊤)
  → (f-abs : X-abs → Y-abs)
  → ((x-⊤ : X-⊤) → ψ (f-⊤ x-⊤) ≡ f-abs (χ x-⊤))
  → Abstraction χ → Abstraction ψ
square χ ψ f-⊤ f-abs f-coh =
  Glue.square
    (●.map f-⊤)
    (◯.map f-abs)
    (●.elim (λ _ → ●.isModal●≡) (cong (η• ∘ η◦) ∘ f-coh))

module _ {X-⊤ X-abs} (χ : X-⊤ → X-abs) where
  triangle
    : (x-⊤ : X-⊤) (x-abs : X-abs)
    → χ x-⊤ ≡ x-abs
    → Abstraction χ
  triangle x-⊤ x-abs p = (η• x-⊤ , η◦ x-abs) , cong (η• ∘ η◦) p

  inj-⊤ : X-⊤ → Abstraction χ
  inj-⊤ x-⊤ = triangle x-⊤ (χ x-⊤) refl

  proj-abs : Abstraction χ → X-abs
  proj-abs = square χ id χ id (λ _ → refl) ⨾ invEq (Abstraction-id X-abs)

  inj-proj : (x-⊤ : X-⊤) → proj-abs (inj-⊤ x-⊤) ≡ χ x-⊤
  inj-proj x-⊤ =
      invEq (Abstraction-id X-abs) (square χ id χ id (λ _ → refl) (inj-⊤ x-⊤))
    ≡⟨ cong (invEq (Abstraction-id X-abs) ∘ (fst (fracture _) ,_)) (sym (rUnit refl)) ⟩
      invEq (Abstraction-id X-abs) (fracture (χ x-⊤))
    ≡⟨ retEq (Abstraction-id X-abs) (χ x-⊤) ⟩
      χ x-⊤
    ∎


Abstraction-open
  : ∀ {X-⊤ X-abs} (χ : X-⊤ → X-abs)
  → ⟨ ABS ⟩
  → Abstraction χ ≃ X-abs
Abstraction-open {X-⊤} {X-abs} χ abs =
  Glue-open (Abstraction-Fracture χ) abs ∙ₑ ◯-open abs

square-openP
  : ∀ {X-⊤ X-abs} (χ : X-⊤ → X-abs) {Y-⊤ Y-abs} (β : Y-⊤ → Y-abs)
  → (f-⊤ : X-⊤ → Y-⊤) (f-abs : X-abs → Y-abs)
  → (f-coh : (x-⊤ : X-⊤) → β (f-⊤ x-⊤) ≡ f-abs (χ x-⊤))
  → (abs : ⟨ ABS ⟩)
  → PathP
      (λ i → ua (Abstraction-open χ abs) i → ua (Abstraction-open β abs) i)
      (square χ β f-⊤ f-abs f-coh)
      f-abs
square-openP χ β _ _ _ abs =
  ua→ λ x → ua-gluePath (Abstraction-open β abs) refl

triangle-openP
  : ∀ {X-⊤ X-abs} (χ : X-⊤ → X-abs)
  → (x-⊤ : X-⊤) (x-abs : X-abs) (x-coh : χ x-⊤ ≡ x-abs)
  → (abs : ⟨ ABS ⟩)
  → PathP (λ i → ua (Abstraction-open χ abs) i)
      (triangle χ x-⊤ x-abs x-coh)
      x-abs
triangle-openP χ _ _ _ abs =
  ua-gluePath (Abstraction-open χ abs) refl
