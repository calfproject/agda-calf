module Calf.Computation.Abstraction.Base where

open import Calf.Value
open import Calf.Value.Abstraction
open import Calf.Value.Closed as ●
open import Calf.Computation
open import Calf.Computation.Closed as ●ᶜ
open import Calf.Computation.Glue as Glueᶜ hiding (squareᶜ)
open import Calf.Computation.Open as ◯ᶜ

open Fractureᶜ

Abstractionᶜ-Fracture : {A-⊤ A-abs : 𝒞} → (A-⊤ ⊸ A-abs) → Fractureᶜ
Abstractionᶜ-Fracture {A-⊤} {A-abs} α .A• = ●ᶜ• A-⊤
Abstractionᶜ-Fracture {A-⊤} {A-abs} α .A◦ = ◯ᶜ◦ A-abs
Abstractionᶜ-Fracture {A-⊤} {A-abs} α .α• = ●ᶜ.map (α ⨾ᶜ η◦ᶜ)

Abstractionᶜ : {A-⊤ A-abs : 𝒞} → (A-⊤ ⊸ A-abs) → 𝒞
Abstractionᶜ = fromFractureᶜ ∘ Abstractionᶜ-Fracture

Abstractionᶜ-≃
  : ∀ {A-⊤ A-abs α B-⊤ B-abs β}
  → (e-⊤ : A-⊤ ≃ᶜ B-⊤)
  → (e-abs : A-abs ≃ᶜ B-abs)
  → equivFunᶜ e-⊤ ⨾ᶜ β ≡ α ⨾ᶜ equivFunᶜ e-abs
  → Abstractionᶜ α ≃ᶜ Abstractionᶜ β
Abstractionᶜ-≃ e-⊤ e-abs e-coh =
  Glueᶜ-≃ (●ᶜ-≃ e-⊤) (◯ᶜ-≃ e-abs) $
    ●ᶜ.map-∘ (equivFunᶜ e-⊤) _
    ∙ (funExtᶜ (funExt⁻ (cong (●.map ∘ (η◦ ∘_) ∘ U) e-coh)))
    ∙ sym (●ᶜ.map-∘ _ (equivFunᶜ (◯ᶜ-≃ e-abs)))

squareᶜ
  : ∀ {A-⊤ A-abs B-⊤ B-abs}
  → (α : A-⊤ ⊸ A-abs) (β : B-⊤ ⊸ B-abs)
  → (f-⊤ : A-⊤ ⊸ B-⊤) (f-abs : A-abs ⊸ B-abs)
  → ((a-⊤ : U A-⊤) → U β (U f-⊤ a-⊤) ≡ U f-abs (U α a-⊤))
  → Abstractionᶜ α ⊸ Abstractionᶜ β
squareᶜ α β f-⊤ f-abs f-coherence =
  Glueᶜ.squareᶜ {α• = ●ᶜ.map (α ⨾ᶜ η◦ᶜ)} {β• = ●ᶜ.map (β ⨾ᶜ η◦ᶜ)}
    (●ᶜ.map f-⊤)
    (◯ᶜ.map f-abs)
    (funExtᶜ (●ᶜ.elim (λ _ → ●ᶜ.●-≡-isModal _ _) λ a → cong (η• ∘ η◦) (f-coherence a)))

module _ {A-⊤ A-abs} (α : A-⊤ ⊸ A-abs) where
  triangleᶜ : ∀ (a-⊤ : U A-⊤) (a-abs : U A-abs)
    → α .U a-⊤ ≡ a-abs
    → U (Abstractionᶜ α)
  triangleᶜ = triangle (α .U)

  injᶜ-⊤ : A-⊤ ⊸ Abstractionᶜ α
  injᶜ-⊤ .U = inj-⊤ (α .U)
  injᶜ-⊤ .charge c a =
    Glue-path (is-set (◯ᶜ A-abs)) refl (cong η◦ (α .charge c a))

Abstractionᶜ-id : (A : 𝒞) → A ≃ᶜ Abstractionᶜ (idᶜ {A})
Abstractionᶜ-id A = injᶜ-⊤ idᶜ , fracture-isEquiv

module _ {A-⊤ A-abs} (α : A-⊤ ⊸ A-abs) where
  projᶜ-abs : Abstractionᶜ α ⊸ A-abs
  projᶜ-abs = squareᶜ α idᶜ α idᶜ (λ _ → refl) ⨾ᶜ invEqᶜ (Abstractionᶜ-id A-abs)

  injᶜ-projᶜ : injᶜ-⊤ α ⨾ᶜ projᶜ-abs ≡ α
  injᶜ-projᶜ = funExtᶜ λ a →
      projᶜ-abs .U (injᶜ-⊤ α .U a)
    ≡⟨ cong (invIsEq fracture-isEquiv) (Glue-path (is-set (◯ᶜ A-abs)) refl refl) ⟩
      invIsEq fracture-isEquiv (fracture (α .U a))
    ≡⟨ retEqᶜ (Abstractionᶜ-id A-abs) (α .U a) ⟩
      α .U a
    ∎
