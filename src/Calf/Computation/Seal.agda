open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma using (ΣPathP; Σ≡Prop)

module Calf.Computation.Seal where

open import Calf.Core.Cost
open import Calf.Core.Directed
open import Calf.Computation
open import Calf.Value
import Calf.Value.Closed as ●ᵛ
import Calf.Value.Open as ◯ᵛ
open import Calf.Value.Glue
open import Calf.Value.Seal
open import Calf.Computation.Power
open import Calf.Computation.Open as ◯ᶜ
open import Calf.Computation.Closed as ●ᶜ
open import Calf.Computation.Glue
open import Calf.Computation.Abstraction

private
  thin● : (A : 𝒞) → isThin (● (U A))
  thin● A = isPreorder→isThin (isPreorder● (A .is-preorder))

Glueᵈᶜ : (A• : 𝒞•) (A◦ : 𝒞◦) (α• : ⟨ A• ⟩ᶜ ⊸ ●ᶜ ⟨ A◦ ⟩ᶜ) → 𝒞
Glueᵈᶜ A• A◦ α• .U = Glueᵈ (U• A•) (U◦ A◦) (U α•)
Glueᵈᶜ A• A◦ α• .is-preorder =
  isPreorderGlueᵈ
    {U• A•}
    {U◦ A◦}
    (⟨ A• ⟩ᶜ .is-preorder)
    (⟨ A◦ ⟩ᶜ .is-preorder)
Glueᵈᶜ A• A◦ α• .charge c ((x• , x◦) , p) =
  (⟨ A• ⟩ᶜ .charge c x• , ⟨ A◦ ⟩ᶜ .charge c x◦) ,
  ≡∙⊑ (α• .charge c x•) (⊑-mono (●ᶜ ⟨ A◦ ⟩ᶜ .charge c) p)
Glueᵈᶜ A• A◦ α• .charge/0 =
  Σ≡Prop (λ _ → thin● ⟨ A◦ ⟩ᶜ _ _)
    (ΣPathP (⟨ A• ⟩ᶜ .charge/0 , ⟨ A◦ ⟩ᶜ .charge/0))
Glueᵈᶜ A• A◦ α• .charge/+ =
  Σ≡Prop (λ _ → thin● ⟨ A◦ ⟩ᶜ _ _)
    (ΣPathP (⟨ A• ⟩ᶜ .charge/+ , ⟨ A◦ ⟩ᶜ .charge/+))

open 𝒞-FRACTURE

𝒞-Glueᵈ : 𝒞-FRACTURE → 𝒞
𝒞-Glueᵈ F = Glueᵈᶜ (F .A•) (F .A◦) (F .α•)

Sealᶜ : 𝒞 → 𝒞
Sealᶜ = 𝒞-Glueᵈ ∘ 𝒞-Fracture

_⊸ᵈ_ : 𝒞 → 𝒞 → 𝒱
A ⊸ᵈ B = A ⊸ Sealᶜ B

idᵈ : A ⊸ᵈ A
idᵈ .U a = (η• a , η◦ a) , ⊑-refl
idᵈ {A} .charge c a =
  Σ≡Prop (λ _ → thin● (◯ᶜ A) _ _) refl

infixl 9 _⨾ᵈ_
_⨾ᵈ_ : (A ⊸ B) → (B ⊸ C) → (A ⊸ C)
f ⨾ᵈ g = {!   !}

squareᵈ' : ∀ {A-⊤ A-abs α B-⊤ B-abs β} (f-⊤ : A-⊤ ⊸ B-⊤) (f-abs : A-abs ⊸ B-abs)
  → ((a-⊤ : U A-⊤) → U β (U f-⊤ a-⊤) ⊑[ B-abs ] U f-abs (U α a-⊤))
  → Abstractionᶜ A-⊤ A-abs α ⊸ᵈ Abstractionᶜ B-⊤ B-abs β
squareᵈ' = {!   !}
