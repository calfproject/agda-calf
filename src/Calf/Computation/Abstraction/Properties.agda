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

triangleᶜ-natural : ∀ {A-⊤ A-abs α B-⊤ B-abs β}
  (f-⊤ : A-⊤ ⊸ B-⊤) (f-abs : A-abs ⊸ B-abs)
  (coh : (a : U A-⊤) → β .U (f-⊤ .U a) ≡ f-abs .U (α .U a))
  → triangleᶜ α ⨾ᶜ squareᶜ α β f-⊤ f-abs coh
    ≡ f-⊤ ⨾ᶜ triangleᶜ β
triangleᶜ-natural {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} f-⊤ f-abs coh =
  funExtᶜ λ a →
    Glue-path (is-set (◯ᶜ B-abs))
      refl
      (funExt λ _ → sym (coh a))

-- opaque
--   unfolding Abstractionᶜ ●ᶜ-Abstractionᶜ

--   Abstractionᶜ-coherence : ∀ {A-⊤ A-abs} (α : A-⊤ ⊸ A-abs) →
--     PathP
--       (λ i →
--         sym (●ᶜ-Abstractionᶜ α) i ⊸
--         ●ᶜ (sym (◯ᶜ-Abstractionᶜ α) i))
--       (●ᶜ.map (α ⨾ᶜ η◦ᶜ {A = A-abs}))
--       (●ᶜ.map (η◦ᶜ {A = Abstractionᶜ α}))
--   Abstractionᶜ-coherence {A-⊤} {A-abs} α = {!   !}
--     -- glue-fracture-sectionᶜ-α•
--     --   (Abstractionᶜ-Fracture α)

Abstractionᶜ-open
  : ∀ {A-⊤ A-abs} (α : A-⊤ ⊸ A-abs)
  → ⟨ ABS ⟩
  → Abstractionᶜ α ≃ᶜ A-abs
Abstractionᶜ-open {A-⊤} {A-abs} α abs =
  Glueᶜ-open (Abstractionᶜ-Fracture α) abs ∙ₑᶜ ◯ᶜ-open abs

--   square-openP
--     : ∀ {A-⊤ A-abs B-⊤ B-abs}
--     → (α : A-⊤ ⊸ A-abs) (β : B-⊤ ⊸ B-abs)
--     → (f-⊤ : A-⊤ ⊸ B-⊤) (f-abs : A-abs ⊸ B-abs)
--     → (f-coh : (a-⊤ : U A-⊤) → U β (U f-⊤ a-⊤) ≡ U f-abs (U α a-⊤))
--     → (abs : ⟨ ABS ⟩)
--     → PathP
--       (λ i →
--         Abstractionᶜ-open α abs i
--           ⊸ Abstractionᶜ-open β abs i)
--       (squareᶜ α β f-⊤ f-abs f-coh)
--       f-abs
--   square-openP α β f-⊤ f-abs f-coh abs =
--     ⊸-path
--       (Abstractionᶜ-open α abs)
--       (Abstractionᶜ-open β abs)
--       (ua→
--         {e = Abstractionᶜ-open-≃ α abs .fst .U
--            , Abstractionᶜ-open-≃ α abs .snd}
--         {B = λ i → U (Abstractionᶜ-open β abs i)}
--         {!   !})
--         -- (λ _ →
--         --   ua-gluePath
--         --     ( Abstractionᶜ-open-≃ β abs .fst .U
--         --     , Abstractionᶜ-open-≃ β abs .snd)
--         --     refl))

--   triangle-U-openP : ∀ {B-⊤ B-abs} (β : B-⊤ ⊸ B-abs)
--       (b-⊤ : U B-⊤) (b-abs : U B-abs) (b-coh : β .U b-⊤ ≡ b-abs) (abs : ⟨ ABS ⟩) →
--     PathP (λ i → U (Abstractionᶜ-open β abs i))
--       (triangle-U β b-⊤ b-abs b-coh)
--       b-abs
--   triangle-U-openP β b-⊤ b-abs b-coh abs = {!   !}
--     -- ua-gluePath
--     --   ( Abstractionᶜ-open-≃ β abs .fst .U
--     --   , Abstractionᶜ-open-≃ β abs .snd)
--     --   refl


squareᶜ-charge
  : ∀ {A-⊤ A-abs} (α : A-⊤ ⊸ A-abs) (c : ℂ)
  → (α-charge : (a : U A-⊤) → α .U (A-⊤ .charge c a) ≡ A-abs .charge c (α .U a))
  → squareᶜ α α
      (chargeᶜ {A-⊤} c) (chargeᶜ {A-abs} c)
      α-charge
    ≡ chargeᶜ {Abstractionᶜ α} c
squareᶜ-charge {A-⊤} {A-abs} α c α-charge =
  funExtᶜ λ _ → Glue-path (is-set (◯ᶜ A-abs)) refl refl

squareᶜ-⨾ᶜ : ∀ {A-⊤ A-abs α B-⊤ B-abs β C-⊤ C-abs γ}
  (f-⊤ : A-⊤ ⊸ B-⊤) (f-abs : A-abs ⊸ B-abs)
  (f-coh : (a : U A-⊤) → β .U (f-⊤ .U a) ≡ f-abs .U (α .U a))
  (g-⊤ : B-⊤ ⊸ C-⊤) (g-abs : B-abs ⊸ C-abs)
  (gc : (b : U B-⊤) → γ .U (g-⊤ .U b) ≡ g-abs .U (β .U b))
  → squareᶜ α β f-⊤ f-abs f-coh ⨾ᶜ squareᶜ β γ g-⊤ g-abs gc
    ≡ squareᶜ α γ (f-⊤ ⨾ᶜ g-⊤) (f-abs ⨾ᶜ g-abs)
        (λ a → gc (f-⊤ .U a) ∙ cong (g-abs .U) (f-coh a))
squareᶜ-⨾ᶜ {C-abs = C-abs} {γ} f-⊤ f-abs f-coh g-⊤ g-abs gc =
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
squareᶜ-≡ {B-⊤ = B-⊤} {B-abs} {β} {f-coh = f-coh} {f-coh' = f-coh'} p q =
  funExtᶜ λ a →
    Glue-path (is-set (◯ᶜ B-abs))
      (cong (λ f → ●.map (f .U) (proj• a)) p)
      (cong (λ f → ◯.map (f .U) (proj◦ a)) q)

Abstractionᶜ-fuse : ∀ {A-⊤ A-abs B-⊤ B-abs}
    (α : A-⊤ ⊸ A-abs) (β : B-⊤ ⊸ B-abs)
    (f-⊤ : A-⊤ ⊸ B-⊤) (f-abs : A-abs ⊸ B-abs)
    (f-coh : (a-⊤ : U A-⊤) → U β (U f-⊤ a-⊤) ≡ U f-abs (U α a-⊤)) →
  Abstractionᶜ (squareᶜ α β f-⊤ f-abs f-coh) ≃ᶜ Abstractionᶜ (α ⨾ᶜ f-abs)
Abstractionᶜ-fuse {A-⊤} {A-abs} {B-⊤} {B-abs} α β f-⊤ f-abs f-coh =
    Abstractionᶜ (squareᶜ α β f-⊤ f-abs f-coh)
  ≃ᶜ⟨⟩
    Glueᶜ
      (●ᶜ (Abstractionᶜ α))
      (◯ᶜ (Abstractionᶜ β))
      (●ᶜ.map (squareᶜ α β f-⊤ f-abs f-coh ⨾ᶜ η◦ᶜ))
  ≃ᶜ⟨
    Glueᶜ-≃
      {α• = ●ᶜ.map (squareᶜ α β f-⊤ f-abs f-coh ⨾ᶜ η◦ᶜ)}
      {β• = ●ᶜ.map (α ⨾ᶜ f-abs ⨾ᶜ η◦ᶜ)}
      (●ᶜ-Abstractionᶜ α)
      (◯ᶜ-Abstractionᶜ β)
      (funExtᶜ (●.elim (λ _ → ●-≡-isModal _ _) lemma))
  ⟩
    Glueᶜ
      (●ᶜ A-⊤)
      (◯ᶜ B-abs)
      (●ᶜ.map (α ⨾ᶜ f-abs ⨾ᶜ η◦ᶜ))
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
