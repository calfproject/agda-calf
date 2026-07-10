module Calf.Computation.Abstraction.Base where

open import Calf.Value
open import Calf.Computation
open import Calf.Computation.Open as ◯ᶜ
open import Calf.Computation.Closed as ●ᶜ
open import Calf.Computation.Glue as Glueᶜ hiding (squareᶜ)
import Calf.Value.Closed as ●

open 𝒞-FRAC

Abstractionᶜ-FRAC : (A-⊤ A-abs : 𝒞) → (A-⊤ ⊸ A-abs) → 𝒞-FRAC
Abstractionᶜ-FRAC A-⊤ A-abs α .A• = ●ᶜ A-⊤ , ●ᶜ.η-isEquiv
Abstractionᶜ-FRAC A-⊤ A-abs α .A◦ = ◯ᶜ A-abs , ◯ᶜ.η-isEquiv
Abstractionᶜ-FRAC A-⊤ A-abs α .α• = ●ᶜ.map (α ⨾ᶜ η◦ᶜ)

opaque
  Abstractionᶜ : (A-⊤ A-abs : 𝒞) → (A-⊤ ⊸ A-abs) → 𝒞
  Abstractionᶜ A-⊤ A-abs α = 𝒞-fromFRAC (Abstractionᶜ-FRAC A-⊤ A-abs α)

  Abstractionᶜ-id : Abstractionᶜ A A idᶜ ≡ A
  Abstractionᶜ-id {A} =
    cong (Glueᶜ (●ᶜ A , ●ᶜ.η-isEquiv) (◯ᶜ A , ◯ᶜ.η-isEquiv) ∘ ●ᶜ.map) (idᶜ⨾ᶜf≡f η◦ᶜ)
    ∙ 𝒞-glue-fracture-retract A

  glue-path
    : ∀ {A-⊤ A-abs α}
    → {q r : U (𝒞-fromFRAC (Abstractionᶜ-FRAC A-⊤ A-abs α))}
    → q .• ≡ r .•
    → q .◦ ≡ r .◦
    → q ≡ r
  glue-path {A-abs = A-abs} {α = α} {q = q} {r = r} p• p◦ i .• = p• i
  glue-path {A-abs = A-abs} {α = α} {q = q} {r = r} p• p◦ i .◦ = p◦ i
  glue-path {A-abs = A-abs} {α = α} {q = q} {r = r} p• p◦ i .•→◦ =
    isProp→PathP
      (λ i → ●ᶜ (◯ᶜ A-abs) .is-set
        (●ᶜ.map (α ⨾ᶜ η◦ᶜ {A = A-abs}) .U (p• i))
        (●.η• (p◦ i)))
      (q .•→◦)
      (r .•→◦)
      i

  squareᶜ' : ∀ {A-⊤ A-abs α B-⊤ B-abs β} (f-⊤ : A-⊤ ⊸ B-⊤) (f-abs : A-abs ⊸ B-abs)
    → ((a-⊤ : U A-⊤) → U β (U f-⊤ a-⊤) ≡ U f-abs (U α a-⊤))
    → Abstractionᶜ A-⊤ A-abs α ⊸ Abstractionᶜ B-⊤ B-abs β
  squareᶜ' {α = α} {β = β} f-⊤ f-abs f-coherence =
    Glueᶜ.squareᶜ
      (●ᶜ.map f-⊤)
      (◯ᶜ.map f-abs)
      (  ●ᶜ.map f-⊤ ⨾ᶜ ●ᶜ.map (β ⨾ᶜ η◦ᶜ)
       ≡⟨ ●ᶜ.map-∘ f-⊤ (β ⨾ᶜ η◦ᶜ) ⟩
         ●ᶜ.map (f-⊤ ⨾ᶜ (β ⨾ᶜ η◦ᶜ))
       ≡⟨ cong ●ᶜ.map
             (⊸-path refl refl
               (funExt λ a-⊤ → cong η◦ (f-coherence a-⊤))) ⟩
         ●ᶜ.map ((α ⨾ᶜ η◦ᶜ) ⨾ᶜ ◯ᶜ.map f-abs)
       ≡⟨ sym (●ᶜ.map-∘ (α ⨾ᶜ η◦ᶜ) (◯ᶜ.map f-abs)) ⟩
         ●ᶜ.map (α ⨾ᶜ η◦ᶜ) ⨾ᶜ ●ᶜ.map (◯ᶜ.map f-abs)
       ∎)

  squareᶜ'-FRAC
    : ∀ {A-⊤ A-abs α B-⊤ B-abs β}
    → (f-⊤ : A-⊤ ⊸ B-⊤) (f-abs : A-abs ⊸ B-abs)
    → ((a-⊤ : U A-⊤) → U β (U f-⊤ a-⊤) ≡ U f-abs (U α a-⊤))
    → 𝒞-fromFRAC (Abstractionᶜ-FRAC A-⊤ A-abs α)
        ⊸ 𝒞-fromFRAC (Abstractionᶜ-FRAC B-⊤ B-abs β)
  squareᶜ'-FRAC f-⊤ f-abs f-coherence =
    squareᶜ' f-⊤ f-abs f-coherence

triangle : ∀ {A-⊤ A-abs α B}
  → A-abs ⊸ B
  → Abstractionᶜ A-⊤ A-abs α ⊸ B
triangle {α = α} {B} f-abs =
  subst (_ ⊸_) Abstractionᶜ-id $
  squareᶜ' (α ⨾ᶜ f-abs) f-abs (λ _ → refl)

triangle' : ∀ {A B-⊤ B-abs β}
  → A ⊸ B-⊤
  → A ⊸ Abstractionᶜ B-⊤ B-abs β
triangle' {β = β} f-⊤ =
  subst (_⊸ _) Abstractionᶜ-id $
  squareᶜ' f-⊤ (f-⊤ ⨾ᶜ β) (λ _ → refl)

opaque
  unfolding Abstractionᶜ

  triangle-U : ∀ {A-⊤ A-abs α}
    → U A-⊤
    → U (Abstractionᶜ A-⊤ A-abs α)
  triangle-U a-⊤ .• = η• a-⊤
  triangle-U {α = α} a-⊤ .◦ = η◦ (α .U a-⊤)
  triangle-U a-⊤ .•→◦ = refl

  triangleᶜ' : ∀ {B-⊤ B-abs β} (b-⊤ : U B-⊤) (b-abs : U B-abs)
    → β .U b-⊤ ≡ b-abs
    → U (Abstractionᶜ B-⊤ B-abs β)
  triangleᶜ' b-⊤ b-abs b-coherence .• = η• b-⊤
  triangleᶜ' {B-abs = B-abs} b-⊤ b-abs b-coherence .◦ = η◦ᶜ {A = B-abs} .U b-abs
  triangleᶜ' {B-abs = B-abs} b-⊤ b-abs b-coherence .•→◦ =
    cong (λ b → η• (η◦ᶜ {A = B-abs} .U b)) b-coherence
