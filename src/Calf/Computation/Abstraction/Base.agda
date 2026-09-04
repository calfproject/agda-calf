module Calf.Computation.Abstraction.Base where

open import Calf.Core.Abstract
open import Calf.Value
import Calf.Value.Closed ABS as ●
import Calf.Value.Abstraction as Abstraction
open import Calf.Computation
open import Calf.Computation.Open ABS as ◯ᶜ
open import Calf.Computation.Closed ABS as ●ᶜ
open import Calf.Computation.Glue ABS as Glueᶜ hiding (squareᶜ)
open import Cubical.Foundations.Univalence using (ua→; ua-gluePath)

open Fractureᶜ

opaque
  Abstractionᶜ-Fracture : (A-⊤ A-abs : 𝒞) → (A-⊤ ⊸ A-abs) → Fractureᶜ
  Abstractionᶜ-Fracture A-⊤ A-abs α .A• = ●ᶜ• A-⊤
  Abstractionᶜ-Fracture A-⊤ A-abs α .A◦ = ◯ᶜ◦ A-abs
  Abstractionᶜ-Fracture A-⊤ A-abs α .α• = ●ᶜ.map (α ⨾ᶜ η◦ᶜ)

  Abstractionᶜ : (A-⊤ A-abs : 𝒞) → (A-⊤ ⊸ A-abs) → 𝒞
  Abstractionᶜ A-⊤ A-abs α = fromFractureᶜ (Abstractionᶜ-Fracture A-⊤ A-abs α)

opaque
  unfolding Abstractionᶜ

  squareᶜ
    : ∀ {A-⊤ A-abs B-⊤ B-abs}
    → (α : A-⊤ ⊸ A-abs) (β : B-⊤ ⊸ B-abs)
    → (f-⊤ : A-⊤ ⊸ B-⊤) (f-abs : A-abs ⊸ B-abs)
    → ((a-⊤ : U A-⊤) → U β (U f-⊤ a-⊤) ≡ U f-abs (U α a-⊤))
    → Abstractionᶜ A-⊤ A-abs α ⊸ Abstractionᶜ B-⊤ B-abs β
  squareᶜ α β f-⊤ f-abs f-coherence =
    Glueᶜ.squareᶜ
      (●ᶜ.map f-⊤)
      (◯ᶜ.map f-abs)
      coh
    where
      coh : ●ᶜ.map f-⊤ ⨾ᶜ ●ᶜ.map (β ⨾ᶜ η◦ᶜ) ≡ ●ᶜ.map (α ⨾ᶜ η◦ᶜ) ⨾ᶜ ●ᶜ.map (◯ᶜ.map f-abs)
      coh =
        ⊸-path refl refl
          (funExt (●.elim (λ _ → ●.●-≡-isModal _ _) λ a → cong (η• ∘ η◦) (f-coherence a)))

opaque
  unfolding Abstractionᶜ

  triangleᶜ : ∀ {A-⊤ A-abs} (α : A-⊤ ⊸ A-abs) → A-⊤ ⊸ Abstractionᶜ A-⊤ A-abs α
  triangleᶜ {A-⊤} {A-abs} α .U = Abstraction.triangle
  triangleᶜ {A-⊤} {A-abs} α .charge c a =
    Glue-path (is-set (◯ᶜ A-abs)) refl (cong η◦ (α .charge c a))

  triangle-U : ∀ {B-⊤ B-abs} (β : B-⊤ ⊸ B-abs) (b-⊤ : U B-⊤) (b-abs : U B-abs)
    → β .U b-⊤ ≡ b-abs
    → U (Abstractionᶜ B-⊤ B-abs β)
  triangle-U {B-abs = B-abs} β b-⊤ b-abs b-coherence =
    (η• b-⊤ , η◦ᶜ {A = B-abs} .U b-abs) ,
    cong (λ b → η• (η◦ᶜ {A = B-abs} .U b)) b-coherence

opaque
  unfolding Abstractionᶜ

  Abstractionᶜ-id : (A : 𝒞) → Abstractionᶜ A A idᶜ ≡ A
  Abstractionᶜ-id A =
    cong (Glueᶜ (●ᶜ A) (◯ᶜ A) ∘ ●ᶜ.map) (⨾ᶜ-identityˡ η◦ᶜ)
    ∙ glue-fracture-retractᶜ A

triangle-abs : ∀ {A-⊤ A-abs α B}
  → A-abs ⊸ B
  → Abstractionᶜ A-⊤ A-abs α ⊸ B
triangle-abs {α = α} {B} f-abs =
  subst (_ ⊸_) (Abstractionᶜ-id B) $
  squareᶜ α idᶜ (α ⨾ᶜ f-abs) f-abs (λ _ → refl)

triangle-⊤ : ∀ {A B-⊤ B-abs}
  → (β : B-⊤ ⊸ B-abs)
  → A ⊸ B-⊤
  → A ⊸ Abstractionᶜ B-⊤ B-abs β
triangle-⊤ β f-⊤ = f-⊤ ⨾ᶜ triangleᶜ β

opaque
  unfolding Abstractionᶜ Abstractionᶜ-id glue-fracture-retractᶜ triangleᶜ ⊸-path

  triangleᶜ-id : PathP (λ i → A ⊸ Abstractionᶜ-id A i) (triangleᶜ idᶜ) idᶜ
  triangleᶜ-id {A} =
    compPathP' {B = A ⊸_}
      (⊸-path
        refl (cong (Glueᶜ (●ᶜ A) (◯ᶜ A) ∘ ●ᶜ.map) (⨾ᶜ-identityˡ η◦ᶜ))
        {f₀ = triangleᶜ idᶜ}
        {f₁ = fractureᶜ}
        refl)
      (⊸-path refl (glue-fracture-retractᶜ A)
        {f₀ = fractureᶜ}
        {f₁ = idᶜ}
        (funExt λ a →
          symP (ua-gluePath (fractureᶜ {A} .U , fracture-isEquiv) {x = a} refl)))
