module Calf.Value.Abstraction where

open import Calf.Value
open import Calf.Value.Open as ◯
open import Calf.Value.Closed as ●
open import Calf.Value.Glue as Glue hiding (square)

Abstraction : (X-⊤ X-abs : 𝒱) → (X-⊤ → X-abs) → 𝒱
Abstraction X-⊤ X-abs χ = Glue (● X-⊤) (◯ X-abs) (●.map (η◦ ∘ χ))

Abstraction-id : Abstraction X X id ≡ X
Abstraction-id = glue-fracture-retract _

square
  : ∀ {X-⊤ X-abs χ Y-⊤ Y-abs ψ}
  → (f-⊤ : X-⊤ → Y-⊤)
  → (f-abs : X-abs → Y-abs)
  → ((x-⊤ : X-⊤) → ψ (f-⊤ x-⊤) ≡ f-abs (χ x-⊤))
  → Abstraction X-⊤ X-abs χ → Abstraction Y-⊤ Y-abs ψ
square {X-⊤ = X-⊤} {X-abs = X-abs} {χ = χ} {Y-⊤ = Y-⊤} {Y-abs = Y-abs} {ψ = ψ} f-⊤ f-abs f-coherence =
  Glue.square
    {X• = ● X-⊤} {X◦ = ◯ X-abs} {χ = ●.map (η◦ ∘ χ)}
    {Y• = ● Y-⊤} {Y◦ = ◯ Y-abs} {ψ = ●.map (η◦ ∘ ψ)}
    (●.map f-⊤)
    (◯.map f-abs)
    (●.elim (λ x• → ●-≡-isModal _ _) (λ x → cong (η• ∘ η◦) (f-coherence x)))

triangle : ∀ {X-⊤ X-abs χ}
  → X-⊤ → Abstraction X-⊤ X-abs χ
triangle {χ = χ} x = (η• x , η◦ (χ x)) , refl
