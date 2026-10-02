module Calf.Computation.Abstraction.Properties where

open import Cubical.Foundations.Univalence using (ua; ua→; ua-gluePath)

open import Calf.Core.Abstract
open import Calf.Core.Cost using (ℂ)
open import Calf.Value
import Calf.Value.Closed as ●
import Calf.Value.Open as ◯
open import Calf.Computation
open import Calf.Computation.Closed as ●ᶜ
open import Calf.Computation.Glue as Glueᶜ hiding (squareᶜ)
open import Calf.Computation.Open as ◯ᶜ

open import Calf.Computation.Abstraction.Base


●ᶜ-Abstractionᶜ : ∀ {A-⊤ A-abs} (α : A-⊤ ⊸ A-abs) → ●ᶜ (Abstractionᶜ α) ≃ᶜ ●ᶜ A-⊤
●ᶜ-Abstractionᶜ {A-⊤} {A-abs} α = glue•ᶜ (Abstractionᶜ-Fracture α)

◯ᶜ-Abstractionᶜ : ∀ {A-⊤ A-abs} (α : A-⊤ ⊸ A-abs) → ◯ᶜ (Abstractionᶜ α) ≃ᶜ ◯ᶜ A-abs
◯ᶜ-Abstractionᶜ {A-⊤} {A-abs} α = glue◦ᶜ (Abstractionᶜ-Fracture α)

Abstractionᶜ-open
  : ∀ {A-⊤ A-abs} (α : A-⊤ ⊸ A-abs)
  → ⟨ ABS ⟩
  → Abstractionᶜ α ≃ᶜ A-abs
Abstractionᶜ-open {A-⊤} {A-abs} α abs =
  Glueᶜ-open (Abstractionᶜ-Fracture α) abs ∙ₑᶜ ◯ᶜ-open abs

square-openP
  : ∀ {A-⊤ A-abs} (α : A-⊤ ⊸ A-abs) {B-⊤ B-abs} (β : B-⊤ ⊸ B-abs)
  → (f-⊤ : A-⊤ ⊸ B-⊤) (f-abs : A-abs ⊸ B-abs)
  → (f-coh : (a-⊤ : U A-⊤) → U β (U f-⊤ a-⊤) ≡ U f-abs (U α a-⊤))
  → (abs : ⟨ ABS ⟩)
  → PathP
      (λ i → uaᶜ (Abstractionᶜ-open α abs) i ⊸ uaᶜ (Abstractionᶜ-open β abs) i)
      (squareᶜ α β f-⊤ f-abs f-coh)
      f-abs
square-openP α β _ _ _ abs =
  ⊸-path
    (uaᶜ (Abstractionᶜ-open α abs))
    (uaᶜ (Abstractionᶜ-open β abs))
    (ua→ λ a → uaᶜ-gluePath (Abstractionᶜ-open β abs) refl)

triangleᶜ-openP
  : ∀ {A-⊤ A-abs} (α : A-⊤ ⊸ A-abs)
  → (a-⊤ : U A-⊤) (a-abs : U A-abs) (a-coh : α .U a-⊤ ≡ a-abs)
  → (abs : ⟨ ABS ⟩)
  → PathP (λ i → U (uaᶜ (Abstractionᶜ-open α abs) i))
      (triangleᶜ α a-⊤ a-abs a-coh)
      a-abs
triangleᶜ-openP α _ _ _ abs =
  uaᶜ-gluePath (Abstractionᶜ-open α abs) refl

squareᶜ-⨾ᶜ : ∀ {A-⊤ A-abs α B-⊤ B-abs β C-⊤ C-abs γ}
  (f-⊤ : A-⊤ ⊸ B-⊤) (f-abs : A-abs ⊸ B-abs)
  (f-coh : (a : U A-⊤) → β .U (f-⊤ .U a) ≡ f-abs .U (α .U a))
  (g-⊤ : B-⊤ ⊸ C-⊤) (g-abs : B-abs ⊸ C-abs)
  (g-coh : (b : U B-⊤) → γ .U (g-⊤ .U b) ≡ g-abs .U (β .U b))
  → squareᶜ α β f-⊤ f-abs f-coh ⨾ᶜ squareᶜ β γ g-⊤ g-abs g-coh
    ≡ squareᶜ α γ (f-⊤ ⨾ᶜ g-⊤) (f-abs ⨾ᶜ g-abs)
        (λ a → g-coh (f-⊤ .U a) ∙ cong (g-abs .U) (f-coh a))
squareᶜ-⨾ᶜ {C-abs = C-abs} f-⊤ f-abs f-coh g-⊤ g-abs g-coh =
  funExtᶜ λ a →
    Glue-path (is-set (◯ᶜ C-abs))
      (●.map-∘ (f-⊤ .U) (g-⊤ .U) (proj• a))
      (◯.map-∘ (f-abs .U) (g-abs .U) (proj◦ a))

squareᶜ-≡ : ∀ {A-⊤ A-abs α B-⊤ B-abs β}
  {f-⊤ f-⊤' : A-⊤ ⊸ B-⊤} {f-abs f-abs' : A-abs ⊸ B-abs}
  {f-coh : (a : U A-⊤) → β .U (f-⊤ .U a) ≡ f-abs .U (α .U a)}
  {f-coh' : (a : U A-⊤) → β .U (f-⊤' .U a) ≡ f-abs' .U (α .U a)}
  → f-⊤ ≡ f-⊤'
  → f-abs ≡ f-abs'
  → squareᶜ α β f-⊤ f-abs f-coh ≡ squareᶜ α β f-⊤' f-abs' f-coh'
squareᶜ-≡ {B-⊤ = B-⊤} {B-abs} {β} {f-coh = f-coh} {f-coh' = f-coh'} p p' =
  funExtᶜ λ a →
    Glue-path (is-set (◯ᶜ B-abs))
      (cong (λ f → ●.map (f .U) (proj• a)) p)
      (cong (λ f → ◯.map (f .U) (proj◦ a)) p')

Abstractionᶜ-fuse : ∀ {A-⊤ A-abs B-⊤ B-abs}
    (α : A-⊤ ⊸ A-abs) (β : B-⊤ ⊸ B-abs)
    (f-⊤ : A-⊤ ⊸ B-⊤) (f-abs : A-abs ⊸ B-abs)
    (f-coh : (a-⊤ : U A-⊤) → U β (U f-⊤ a-⊤) ≡ U f-abs (U α a-⊤)) →
  Abstractionᶜ (squareᶜ α β f-⊤ f-abs f-coh) ≃ᶜ Abstractionᶜ (α ⨾ᶜ f-abs)
Abstractionᶜ-fuse {A-⊤} {A-abs} {B-⊤} {B-abs} α β f-⊤ f-abs f-coh =
    Abstractionᶜ (squareᶜ α β f-⊤ f-abs f-coh)
  ≃ᶜ⟨⟩
    Glueᶜ (●ᶜ.map (squareᶜ α β f-⊤ f-abs f-coh ⨾ᶜ η◦ᶜ))
  ≃ᶜ⟨
    Glueᶜ-≃
      (●ᶜ-Abstractionᶜ α)
      (◯ᶜ-Abstractionᶜ β)
      (funExtᶜ (●.elim (λ _ → ●-≡-isModal _ _) lemma))
  ⟩
    Glueᶜ (●ᶜ.map (α ⨾ᶜ f-abs ⨾ᶜ η◦ᶜ))
  ≃ᶜ⟨⟩
    Abstractionᶜ (α ⨾ᶜ f-abs)
  ■ᶜ
  where
    lemma : ∀ a →
      ●.map (◯.map (f-abs .U) ∘ η◦ ∘ α .U) (proj• a)
      ≡ η• (equivFunᶜ (◯ᶜ-Abstractionᶜ β) .U (η◦ (squareᶜ α β f-⊤ f-abs f-coh .U a)))
    lemma a =
        ●.map (◯.map (f-abs .U) ∘ η◦ ∘ α .U) (proj• a)
      ≡⟨ sym (●.map-∘ (η◦ ∘ α .U) (◯.map (f-abs .U)) (proj• a)) ⟩
        ●.map (◯.map (f-abs .U)) (●.map (η◦ ∘ α .U) (proj• a))
      ≡⟨ cong (●.map (◯.map (f-abs .U))) (proj•→◦ a) ⟩
        ●.map (◯.map (f-abs .U)) (η• (proj◦ a))
      ≡⟨ refl ⟩
        η• (◯.map (f-abs .U) (proj◦ a))
      ≡⟨ cong η• (sym (◯.elim-β (λ _ → strᶜ (◯ᶜ◦ B-abs)) proj◦ (squareᶜ α β f-⊤ f-abs f-coh .U a))) ⟩
        η• (equivFunᶜ (◯ᶜ-Abstractionᶜ β) .U (η◦ (squareᶜ α β f-⊤ f-abs f-coh .U a)))
      ∎
