open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma using (ΣPathP; Σ≡Prop)

module Calf.Computation.Seal where

open import Calf.Core.Abstract using (ABS)
open import Calf.Core.Cost
open import Calf.Core.Directed
open import Calf.Computation
open import Calf.Value
import Calf.Value.Closed as ●
import Calf.Value.Open as ◯
open import Calf.Value.Seal
open import Calf.Computation.Power
open import Calf.Computation.Open as ◯ᶜ
open import Calf.Computation.Closed as ●ᶜ
open import Calf.Computation.Glue using (𝒞-FRACTURE; 𝒞-Fracture; proj•ᶜ; proj◦ᶜ)
open import Calf.Computation.Abstraction

private
  thin● : (A : 𝒞) → isThin (● (U A))
  thin● A = isPreorder→isThin (isPreorder● (A .is-preorder))

Glueᵈᶜ : (A• A◦ : 𝒞) (α• : A• ⊸ ●ᶜ A◦) → 𝒞
Glueᵈᶜ A• A◦ α• .U = Glueᵈ (U A•) (U A◦) (U α•)
Glueᵈᶜ A• A◦ α• .is-preorder =
  isPreorderGlueᵈ
    {U A•}
    {U A◦}
    (A• .is-preorder)
    (A◦ .is-preorder)
Glueᵈᶜ A• A◦ α• .charge c ((x• , x◦) , p) =
  (A• .charge c x• , A◦ .charge c x◦) ,
  ≡∙⊑ (α• .charge c x•) (⊑-mono (●ᶜ A◦ .charge c) p)
Glueᵈᶜ A• A◦ α• .charge/0 =
  Σ≡Prop (λ _ → thin● A◦ _ _)
    (ΣPathP (A• .charge/0 , A◦ .charge/0))
Glueᵈᶜ A• A◦ α• .charge/+ =
  Σ≡Prop (λ _ → thin● A◦ _ _)
    (ΣPathP (A• .charge/+ , A◦ .charge/+))

open 𝒞-FRACTURE

𝒞-Glueᵈ : 𝒞-FRACTURE → 𝒞
𝒞-Glueᵈ F = Glueᵈᶜ ⟨ F .A• ⟩ᶜ ⟨ F .A◦ ⟩ᶜ (F .α•)

Sealᶜ : 𝒞 → 𝒞
Sealᶜ = 𝒞-Glueᵈ ∘ 𝒞-Fracture

proj•ᶜᵈ : Sealᶜ A ⊸ ●ᶜ A
proj•ᶜᵈ .U = •
proj•ᶜᵈ .charge c g = refl

proj◦ᶜᵈ : Sealᶜ A ⊸ ◯ᶜ A
proj◦ᶜᵈ .U = ◦
proj◦ᶜᵈ .charge c g = refl


_⊸ᵈ_ : 𝒞 → 𝒞 → 𝒱
A ⊸ᵈ B = A ⊸ Sealᶜ B

pair : (f• : A ⊸ ●ᶜ B) (f◦ : A ⊸ ◯ᶜ B) → ((a : U A) → ●.map η◦ (f• .U a) ⊑ η• (f◦ .U a)) → (A ⊸ᵈ B)
pair f• f◦ f-coh .U a = (f• .U a , f◦ .U a) , f-coh a
pair {B = B} f• f◦ f-coh .charge c a =
  Σ≡Prop (λ _ → thin● (◯ᶜ B) _ _)
    (ΣPathP (f• .charge c a , f◦ .charge c a))

idᵈ : A ⊸ᵈ A
idᵈ .U a = (η• a , η◦ a) , ⊑-refl
idᵈ {A} .charge c a = Σ≡Prop (λ _ → thin● (◯ᶜ A) _ _) refl

infixl 9 _⨾ᵈ_
_⨾ᵈ_ : (A ⊸ᵈ B) → (B ⊸ᵈ C) → (A ⊸ᵈ C)
_⨾ᵈ_ {A} {B} {C} f g =
  pair
    (f ⨾ᶜ proj•ᶜᵈ ⨾ᶜ ●ᶜ.bind (g ⨾ᶜ proj•ᶜᵈ))
    (f ⨾ᶜ proj◦ᶜᵈ ⨾ᶜ ◯ᶜ.bind {B} {C} (g ⨾ᶜ proj◦ᶜᵈ))
    coh
  where
    g◦◦ : U B → U (◯ᶜ C)
    g◦◦ b = ◦ (g .U b)

    bind-coh : (b• : U (●ᶜ B))
      → ●.map η◦ (●ᶜ.bind (g ⨾ᶜ proj•ᶜᵈ) .U b•) ⊑ ●.map g◦◦ b•
    bind-coh =
      ●.ind-prop _ (λ _ → thin● (◯ᶜ C) _ _)
        (λ b → g .U b .snd)
        (λ abs → ≡⇒⊑ (●.◯-isProp● abs _ _))

    coh : (a : U A)
      → ●.map η◦ (●ᶜ.bind (g ⨾ᶜ proj•ᶜᵈ) .U (• (f .U a)))
        ⊑ η• (◯ᶜ.bind {B} {C} (g ⨾ᶜ proj◦ᶜᵈ) .U (◦ (f .U a)))
    coh a =
      ⊑-trans (●ᶜ (◯ᶜ C) .is-preorder)
        (bind-coh (• (f .U a)))
        (≡∙⊑
          (sym (●.map-∘ η◦ (λ b◦ p → g◦◦ (b◦ p) p) (• (f .U a))))
          (⊑-mono (●.map (λ b◦ p → g◦◦ (b◦ p) p)) (f .U a .snd)))

squareᵈᶜ : ∀ {A-⊤ A-abs α B-⊤ B-abs β}
  → (f-⊤ : A-⊤ ⊸ B-⊤)
  → (f-abs : A-abs ⊸ B-abs)
  → ((a-⊤ : U A-⊤) → U β (U f-⊤ a-⊤) ⊑[ B-abs ] U f-abs (U α a-⊤))
  → Abstractionᶜ A-⊤ A-abs α ⊸ᵈ Abstractionᶜ B-⊤ B-abs β
squareᵈᶜ = {!   !}
