module Calf.Computation.Abstraction.Base where

open import Calf.Value
open import Calf.Value.Abstraction
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
Abstractionᶜ α = fromFractureᶜ (Abstractionᶜ-Fracture α)

Abstractionᶜ-≃
  : ∀ {A-⊤ A-abs α B-⊤ B-abs β}
  → (e-⊤ : A-⊤ ≃ᶜ B-⊤)
  → (e-abs : A-abs ≃ᶜ B-abs)
  → equivFunᶜ e-⊤ ⨾ᶜ β ≡ α ⨾ᶜ equivFunᶜ e-abs
  → Abstractionᶜ α ≃ᶜ Abstractionᶜ β
Abstractionᶜ-≃ e-⊤ e-abs e-coh = Glueᶜ-≃ {!   !} {!   !} {!   !}

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

triangle-U : ∀ {A-⊤ A-abs} (α : A-⊤ ⊸ A-abs) (a-⊤ : U A-⊤) (a-abs : U A-abs)
  → α .U a-⊤ ≡ a-abs
  → U (Abstractionᶜ α)
triangle-U α = triangle (α .U)

triangleᶜ : ∀ {A-⊤ A-abs} (α : A-⊤ ⊸ A-abs) → A-⊤ ⊸ Abstractionᶜ α
triangleᶜ α .U = triangle′ (α .U)
triangleᶜ {A-abs = A-abs} α .charge c a =
  Glue-path (is-set (◯ᶜ A-abs)) refl (cong η◦ (α .charge c a))

Abstractionᶜ-id : (A : 𝒞) → A ≃ᶜ Abstractionᶜ (idᶜ {A})
Abstractionᶜ-id A = triangleᶜ idᶜ , fracture-isEquiv

triangle-abs : ∀ {A-⊤ A-abs} {α : A-⊤ ⊸ A-abs} {B}
  → A-abs ⊸ B
  → Abstractionᶜ α ⊸ B
triangle-abs {α = α} {B} f-abs =
  squareᶜ α idᶜ (α ⨾ᶜ f-abs) f-abs (λ _ → refl)
  ⨾ᶜ invEqᶜ (Abstractionᶜ-id B)

triangle-⊤ : ∀ {A B-⊤ B-abs}
  → (β : B-⊤ ⊸ B-abs)
  → A ⊸ B-⊤
  → A ⊸ Abstractionᶜ β
triangle-⊤ β f-⊤ = f-⊤ ⨾ᶜ triangleᶜ β
