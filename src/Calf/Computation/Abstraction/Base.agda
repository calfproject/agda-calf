module Calf.Computation.Abstraction.Base where

open import Calf.Value
import Calf.Value.Closed as ●
import Calf.Value.Abstraction as Abstraction
open import Calf.Computation
open import Calf.Computation.Open as ◯ᶜ
open import Calf.Computation.Closed as ●ᶜ
open import Calf.Computation.Glue as Glueᶜ hiding (squareᶜ)
open import Cubical.Foundations.Univalence using (ua→; ua-gluePath)

open 𝒞-FRACTURE

opaque
  Abstractionᶜ-FRAC : (A-⊤ A-abs : 𝒞) → (A-⊤ ⊸ A-abs) → 𝒞-FRACTURE
  Abstractionᶜ-FRAC A-⊤ A-abs α .A• = ●ᶜ• A-⊤
  Abstractionᶜ-FRAC A-⊤ A-abs α .A◦ = ◯ᶜ◦ A-abs
  Abstractionᶜ-FRAC A-⊤ A-abs α .α• = ●ᶜ.map (α ⨾ᶜ η◦ᶜ)

  Abstractionᶜ : (A-⊤ A-abs : 𝒞) → (A-⊤ ⊸ A-abs) → 𝒞
  Abstractionᶜ A-⊤ A-abs α = 𝒞-Glue (Abstractionᶜ-FRAC A-⊤ A-abs α)

opaque
  unfolding Abstractionᶜ

  Abstractionᶜ-id : Abstractionᶜ A A idᶜ ≡ A
  Abstractionᶜ-id {A} =
    cong (Glueᶜ (●ᶜ• A) (◯ᶜ◦ A) ∘ ●ᶜ.map) (idᶜ⨾ᶜf≡f η◦ᶜ)
    ∙ 𝒞-glue-fracture-retract A

opaque
  unfolding Abstractionᶜ

  squareᶜ'
    : ∀ {A-⊤ A-abs α B-⊤ B-abs β}
    → (f-⊤ : A-⊤ ⊸ B-⊤) (f-abs : A-abs ⊸ B-abs)
    → ((a-⊤ : U A-⊤) → U β (U f-⊤ a-⊤) ≡ U f-abs (U α a-⊤))
    → Abstractionᶜ A-⊤ A-abs α ⊸ Abstractionᶜ B-⊤ B-abs β
  squareᶜ' {α = α} {β = β} f-⊤ f-abs f-coherence =
    Glueᶜ.squareᶜ
      (●ᶜ.map f-⊤)
      (◯ᶜ.map f-abs)
      coh
    where
      coh : ●ᶜ.map f-⊤ ⨾ᶜ ●ᶜ.map (β ⨾ᶜ η◦ᶜ) ≡ ●ᶜ.map (α ⨾ᶜ η◦ᶜ) ⨾ᶜ ●ᶜ.map (◯ᶜ.map f-abs)
      coh =
            ●ᶜ.map f-⊤ ⨾ᶜ ●ᶜ.map (β ⨾ᶜ η◦ᶜ)
          ≡⟨ ●ᶜ.map-∘ f-⊤ (β ⨾ᶜ η◦ᶜ) ⟩
            ●ᶜ.map (f-⊤ ⨾ᶜ (β ⨾ᶜ η◦ᶜ))
          ≡⟨ cong ●ᶜ.map
                (⊸-path refl refl
                  (funExt λ a-⊤ → cong η◦ (f-coherence a-⊤))) ⟩
            ●ᶜ.map ((α ⨾ᶜ η◦ᶜ) ⨾ᶜ ◯ᶜ.map f-abs)
          ≡⟨ sym (●ᶜ.map-∘ (α ⨾ᶜ η◦ᶜ) (◯ᶜ.map f-abs)) ⟩
            ●ᶜ.map (α ⨾ᶜ η◦ᶜ) ⨾ᶜ ●ᶜ.map (◯ᶜ.map f-abs)
          ∎

triangle : ∀ {A-⊤ A-abs α B}
  → A-abs ⊸ B
  → Abstractionᶜ A-⊤ A-abs α ⊸ B
triangle {α = α} {B} f-abs =
  subst (_ ⊸_) Abstractionᶜ-id $
  squareᶜ' (α ⨾ᶜ f-abs) f-abs (λ _ → refl)

opaque
  unfolding Abstractionᶜ

  triangle-Uᶜ : ∀ {A-⊤ A-abs α} → A-⊤ ⊸ Abstractionᶜ A-⊤ A-abs α
  triangle-Uᶜ {A-⊤} {A-abs} {α} .U = Abstraction.triangle
  triangle-Uᶜ {A-⊤} {A-abs} {α} .charge c a =
    Glue-path (is-set (◯ᶜ A-abs)) refl (cong η◦ (α .charge c a))

  triangleᶜ' : ∀ {B-⊤ B-abs β} (b-⊤ : U B-⊤) (b-abs : U B-abs)
    → β .U b-⊤ ≡ b-abs
    → U (Abstractionᶜ B-⊤ B-abs β)
  triangleᶜ' b-⊤ b-abs b-coherence .• = η• b-⊤
  triangleᶜ' {B-abs = B-abs} b-⊤ b-abs b-coherence .◦ = η◦ᶜ {A = B-abs} .U b-abs
  triangleᶜ' {B-abs = B-abs} b-⊤ b-abs b-coherence .•→◦ =
    cong (λ b → η• (η◦ᶜ {A = B-abs} .U b)) b-coherence

triangle' : ∀ {A B-⊤ B-abs β}
  → A ⊸ B-⊤
  → A ⊸ Abstractionᶜ B-⊤ B-abs β
triangle' f-⊤ = f-⊤ ⨾ᶜ triangle-Uᶜ

opaque
  unfolding Abstractionᶜ Abstractionᶜ-id 𝒞-glue-fracture-retract triangle-Uᶜ ⊸-path

  triangle-Uᶜ-id : PathP (λ i → A ⊸ Abstractionᶜ-id {A} i) (triangle-Uᶜ {A} {A} {idᶜ}) idᶜ
  triangle-Uᶜ-id {A} =
    compPathP' {B = A ⊸_}
      (⊸-path
        refl (cong (Glueᶜ (●ᶜ• A) (◯ᶜ◦ A) ∘ ●ᶜ.map) (idᶜ⨾ᶜf≡f η◦ᶜ))
        {f₀ = triangle-Uᶜ {A} {A} {idᶜ}}
        {f₁ = 𝒞-fracture {A}}
        refl)
      (⊸-path refl (𝒞-glue-fracture-retract A)
        {f₀ = 𝒞-fracture {A}}
        {f₁ = idᶜ}
        (funExt λ a →
          symP (ua-gluePath (𝒞-fracture {A} .U , fracture-isEquiv) {x = a} refl)))
