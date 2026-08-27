open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma using (ΣPathP; Σ≡Prop)

module Calf.Computation.Seal where

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
open import Calf.Computation.Glue
  using (𝒞-FRACTURE; 𝒞-Fracture; 𝒞-Glue; 𝒞-glue-fracture-section; proj•ᶜ; proj◦ᶜ)
open import Calf.Computation.Abstraction

private
  thin● : (A : 𝒞) → isThin (● (U A))
  thin● A = isPreorder→isThin (isPreorder● (A .is-preorder))

Glueᵈᶜ : (A• A◦ : 𝒞) (α• : A• ⊸ ●ᶜ A◦) → 𝒞
Glueᵈᶜ A• A◦ α• .U = Glueᵈ (U A•) (U A◦) (U α•)
Glueᵈᶜ A• A◦ α• .is-preorder =
  isPreorderGlueᵈ (U A•) (U A◦)
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

glueᵈ : (G : 𝒞-FRACTURE) (f• : A ⊸ ⟨ G .A• ⟩ᶜ) (f◦ : A ⊸ ⟨ G .A◦ ⟩ᶜ)
  → ((a : U A) → U (G .α•) (U f• a) ⊑ η• (U f◦ a))
  → A ⊸ 𝒞-Glueᵈ G
glueᵈ G f• f◦ f-coh .U a = (f• .U a , f◦ .U a) , f-coh a
glueᵈ G f• f◦ f-coh .charge c a =
  Σ≡Prop (λ _ → thin● ⟨ G .A◦ ⟩ᶜ _ _)
    (ΣPathP (f• .charge c a , f◦ .charge c a))

pair : (f• : A ⊸ ●ᶜ B) (f◦ : A ⊸ ◯ᶜ B) → ((a : U A) → ●.map η◦ (f• .U a) ⊑ η• (f◦ .U a)) → (A ⊸ᵈ B)
pair {B = B} = glueᵈ (𝒞-Fracture B)

idᵈ : A ⊸ᵈ A
idᵈ .U a = (η• a , η◦ a) , ⊑-refl
idᵈ {A} .charge c a = Σ≡Prop (λ _ → thin● (◯ᶜ A) _ _) refl

infixl 9 _⨾ᵈ_
_⨾ᵈ_ : (A ⊸ᵈ B) → (B ⊸ᵈ C) → (A ⊸ᵈ C)
_⨾ᵈ_ {A} {B} {C} f g =
  pair
    (f ⨾ᶜ proj•ᶜᵈ ⨾ᶜ g•)
    (f ⨾ᶜ proj◦ᶜᵈ ⨾ᶜ g◦)
    (λ a →
      ⊑-trans (●ᶜ (◯ᶜ C) .is-preorder)
        (bind-coh (• (f .U a)))
        (⊑-mono (●.map (g◦ .U)) (f .U a .snd)))
  where
    g• : ●ᶜ B ⊸ ●ᶜ C
    g• = ●ᶜ.bind (g ⨾ᶜ proj•ᶜᵈ)

    g◦ : ◯ᶜ B ⊸ ◯ᶜ C
    g◦ = ◯ᶜ.bind {B} {C} (g ⨾ᶜ proj◦ᶜᵈ)

    bind-coh : (b• : U (●ᶜ B)) → ●.map η◦ (g• .U b•) ⊑ ●.map (g◦ .U) (●.map η◦ b•)
    bind-coh =
      ●.ind-prop _ (λ _ → thin● (◯ᶜ C) _ _)
        (λ b → g .U b .snd)
        (λ abs → ⊑-reflexive (●.◯-isProp● abs _ _))

squareᵈ : (F G : 𝒞-FRACTURE)
  → (f• : ⟨ F .A• ⟩ᶜ ⊸ ⟨ G .A• ⟩ᶜ)
  → (f◦ : ⟨ F .A◦ ⟩ᶜ ⊸ ⟨ G .A◦ ⟩ᶜ)
  → ((a• : U ⟨ F .A• ⟩ᶜ) → U (G .α•) (U f• a•) ⊑ U (●ᶜ.map f◦) (U (F .α•) a•))
  → 𝒞-Glue F ⊸ 𝒞-Glueᵈ G
squareᵈ F G f• f◦ f-coh =
  glueᵈ G (proj•ᶜ F ⨾ᶜ f•) (proj◦ᶜ F ⨾ᶜ f◦)
    (λ ((a• , a◦) , acoh) → ⊑∙≡ (f-coh a•) (cong (U (●ᶜ.map f◦)) acoh))

Sealᶜ-Glue : (F : 𝒞-FRACTURE) → Sealᶜ (𝒞-Glue F) ≡ 𝒞-Glueᵈ F
Sealᶜ-Glue F = cong 𝒞-Glueᵈ (𝒞-glue-fracture-section F)

opaque
  unfolding Abstractionᶜ

  squareᵈᶜ : ∀ {A-⊤ A-abs B-⊤ B-abs}
    → (α : A-⊤ ⊸ A-abs) (β : B-⊤ ⊸ B-abs)
    → (f-⊤ : A-⊤ ⊸ B-⊤)
    → (f-abs : A-abs ⊸ B-abs)
    → ((a-⊤ : U A-⊤) → U β (U f-⊤ a-⊤) ⊑[ B-abs ] U f-abs (U α a-⊤))
    → Abstractionᶜ A-⊤ A-abs α ⊸ᵈ Abstractionᶜ B-⊤ B-abs β
  squareᵈᶜ {A-⊤} {A-abs} {B-⊤} {B-abs} α β f-⊤ f-abs f-coh =
    subst (Abstractionᶜ A-⊤ A-abs α ⊸_) (sym (Sealᶜ-Glue (Abstractionᶜ-FRAC B-⊤ B-abs β)))
      (squareᵈ (Abstractionᶜ-FRAC A-⊤ A-abs α) (Abstractionᶜ-FRAC B-⊤ B-abs β)
        (●ᶜ.map f-⊤) (◯ᶜ.map f-abs)
        (●.ind-prop _ (λ _ → thin● (◯ᶜ B-abs) _ _)
          (λ a → ⊑-mono η• (⊑-mono η◦ (f-coh a)))
          (λ abs → ⊑-reflexive (●.◯-isProp● abs _ _))))
