module Calf.Value.Abstraction where

open import Calf.Value
open import Calf.Value.Open as ◯
open import Calf.Value.Closed as ●
open import Calf.Value.Glue

Abstraction : (X-⊤ X-abs : 𝒱) → (X-⊤ → X-abs) → 𝒱
Abstraction X-⊤ X-abs χ =
  Glue
    (● X-⊤ , ●.η-isEquiv)
    (◯ X-abs , ◯.η-isEquiv)
    (●.map (η◦ ∘ χ))

Abstraction-id : Abstraction X X id ≡ X
Abstraction-id = glue-fracture-retract _

square'
  : ∀ {X-⊤ X-abs χ Y-⊤ Y-abs ψ}
  → (f-⊤ : X-⊤ → Y-⊤)
  → (f-abs : X-abs → Y-abs)
  → ((x-⊤ : X-⊤) → ψ (f-⊤ x-⊤) ≡ f-abs (χ x-⊤))
  → Abstraction X-⊤ X-abs χ → Abstraction Y-⊤ Y-abs ψ
square' {X-⊤ = X-⊤} {X-abs = X-abs} {χ = χ} {Y-⊤ = Y-⊤} {Y-abs = Y-abs} {ψ = ψ} f-⊤ f-abs f-coherence =
  square
    {X• = ● X-⊤ , ●.η-isEquiv}
    {X◦ = ◯ X-abs , ◯.η-isEquiv}
    {χ = ●.map (η◦ ∘ χ)}
    {Y• = ● Y-⊤ , ●.η-isEquiv}
    {Y◦ = ◯ Y-abs , ◯.η-isEquiv}
    {ψ = ●.map (η◦ ∘ ψ)}
    (●.map f-⊤)
    (◯.map f-abs)
    (λ x• →
        ●.map (η◦ ∘ ψ) (●.map f-⊤ x•)
      ≡⟨ ●.map-∘ f-⊤ (η◦ ∘ ψ) x• ⟩
        ●.map (λ x → η◦ (ψ (f-⊤ x))) x•
      ≡⟨ cong (λ f → ●.map f x•) (funExt λ x → cong (η◦) (f-coherence x)) ⟩
        ●.map (λ x → η◦ (f-abs (χ x))) x•
      ≡⟨ sym (●.map-∘ (η◦ ∘ χ) (◯.map f-abs) x•) ⟩
        ●.map (◯.map f-abs) (●.map (η◦ ∘ χ) x•)
      ∎)
