module Calf.Value.Abstraction where

open import Cubical.Foundations.GroupoidLaws using (rUnit)

open import Calf.Value
open import Calf.Value.Closed as ●
open import Calf.Value.Glue as Glue hiding (square)
open import Calf.Value.Open as ◯

Abstraction : {X-⊤ X-abs : 𝒱} → (X-⊤ → X-abs) → 𝒱
Abstraction {X-⊤} {X-abs} χ = Glue (● X-⊤) (◯ X-abs) (●.map (η◦ ∘ χ))

Abstraction-id : (X : 𝒱) → X ≃ Abstraction (id {X})
Abstraction-id X = fracture , fracture-isEquiv

square
  : ∀ {X-⊤ X-abs Y-⊤ Y-abs}
  → (χ : X-⊤ → X-abs) (ψ : Y-⊤ → Y-abs)
  → (f-⊤ : X-⊤ → Y-⊤)
  → (f-abs : X-abs → Y-abs)
  → ((x-⊤ : X-⊤) → ψ (f-⊤ x-⊤) ≡ f-abs (χ x-⊤))
  → Abstraction χ → Abstraction ψ
square χ ψ f-⊤ f-abs f-coherence =
  Glue.square
    (●.map f-⊤)
    (◯.map f-abs)
    (●.elim (λ x• → ●-≡-isModal _ _) (λ x → cong (η• ∘ η◦) (f-coherence x)))

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
