module Calf.Value.Glue.Base where

open import Calf.Value
open import Calf.Value.Closed as ●
open import Calf.Value.Open as ◯
open import Calf.Value.Product

open import Cubical.Foundations.Univalence using (ua)

record Glue (X• : 𝒱•) (X◦ : 𝒱◦) (χ• : ⟨ X• ⟩ → ● ⟨ X◦ ⟩) : 𝒱 where
  field
    • : ⟨ X• ⟩
    ◦ : ⟨ X◦ ⟩
    •→◦ : χ• • ≡ η• ◦
open Glue public

opaque
  Glue-path : ∀ {X• X◦ χ•} {g g' : Glue X• X◦ χ•}
    → isSet ⟨ X◦ ⟩
    → g .• ≡ g' .•
    → g .◦ ≡ g' .◦
    → g ≡ g'
  Glue-path isSetX◦ p• p◦ i .• = p• i
  Glue-path isSetX◦ p• p◦ i .◦ = p◦ i
  Glue-path {χ• = χ•} {g} {g'} isSetX◦ p• p◦ i .•→◦ =
    isProp→PathP
      (λ i → isSet● isSetX◦ (χ• (p• i)) (η• (p◦ i)))
      (g .•→◦)
      (g' .•→◦)
      i

Glue-pullback-≃ : ∀ {X• X◦ χ•} →
  Glue X• X◦ χ• ≃ (Σ[ (x◦ , x•) ∈ ⟨ X◦ ⟩ × ⟨ X• ⟩ ] (η• x◦ ≡ χ• x•))
Glue-pullback-≃ =
  isoToEquiv $ iso
    (λ g → (g .◦ , g .•) , sym (g .•→◦))
    (λ ((x◦ , x•) , h) → record { • = x• ; ◦ = x◦ ; •→◦ = sym h })
    (λ _ → refl)
    (λ _ → refl)

Glue-pullback : ∀ {X• X◦ χ•} →
  Glue X• X◦ χ• ≡ (Σ[ (x◦ , x•) ∈ ⟨ X◦ ⟩ × ⟨ X• ⟩ ] (η• x◦ ≡ χ• x•))
Glue-pullback = ua Glue-pullback-≃

opaque
  isSetGlue : ∀ {X• X◦ χ•} → isSet ⟨ X• ⟩ → isSet ⟨ X◦ ⟩ → isSet (Glue X• X◦ χ•)
  isSetGlue isSetX• isSetX◦ =
    subst isSet (sym Glue-pullback) $
    isSetΣ
      (isSet× isSetX◦ isSetX•)
      λ _ → isProp→isSet (isSet● isSetX◦ _ _)

record 𝒱-FRACTURE : 𝒱₁ where
  field
    X• : 𝒱•
    X◦ : 𝒱◦
    χ• : ⟨ X• ⟩ → ● ⟨ X◦ ⟩
open 𝒱-FRACTURE

𝒱-FRACTURE-path
  : {F G : 𝒱-FRACTURE}
  → (X•-path : F .X• ≡ G .X•)
  → (X◦-path : F .X◦ ≡ G .X◦)
  → PathP
      (λ i → X•-path i .fst → ● (X◦-path i .fst))
      (F .χ•)
      (G .χ•)
  → F ≡ G
𝒱-FRACTURE-path X•-path X◦-path χ•-path i .X• = X•-path i
𝒱-FRACTURE-path X•-path X◦-path χ•-path i .X◦ = X◦-path i
𝒱-FRACTURE-path X•-path X◦-path χ•-path i .χ• = χ•-path i

𝒱-Glue : 𝒱-FRACTURE → 𝒱
𝒱-Glue F = Glue (F .X•) (F .X◦) (F .χ•)

𝒱-Fracture : 𝒱 → 𝒱-FRACTURE
𝒱-Fracture X .X• = ●• X
𝒱-Fracture X .X◦ = ◯◦ X
𝒱-Fracture X .χ• = ●.map η◦

record 𝒱-Square (X Y : 𝒱-FRACTURE) : 𝒱 where
  field
    f• : ⟨ X .X• ⟩ → ⟨ Y .X• ⟩
    f◦ : ⟨ X .X◦ ⟩ → ⟨ Y .X◦ ⟩
    f-coh : (x• : ⟨ X .X• ⟩) → Y .χ• (f• x•) ≡ ●.map f◦ (X .χ• x•)

Square-pullback-≃ : {F G : 𝒱-FRACTURE} →
  𝒱-Square F G ≃
    (Σ[ (f◦ , f•) ∈ (⟨ F .X◦ ⟩ → ⟨ G .X◦ ⟩) × (⟨ F .X• ⟩ → ⟨ G .X• ⟩) ]
      (●.map f◦ ∘ F .χ• ≡ G .χ• ∘ f•))
Square-pullback-≃ =
  isoToEquiv $ iso
    (λ S → (S .𝒱-Square.f◦ , S .𝒱-Square.f•) , sym (funExt (S .𝒱-Square.f-coh)))
    (λ ((f◦ , f•) , h) → record { f• = f• ; f◦ = f◦ ; f-coh = funExt⁻ (sym h) })
    (λ _ → refl)
    (λ _ → refl)

square
  : ∀ {X• X◦ χ Y• Y◦ ψ}
  → (f• : X• .fst → Y• .fst)
  → (f◦ : X◦ .fst → Y◦ .fst)
  → ((x• : X• .fst) → ψ (f• x•) ≡ ●.map f◦ (χ x•))
  → Glue X• X◦ χ → Glue Y• Y◦ ψ
square f• f◦ f-coh q .• = f• (q .•)
square f• f◦ f-coh q .◦ = f◦ (q .◦)
square f• f◦ f-coh q .•→◦ = f-coh (q .•) ∙ cong (●.map f◦) (q .•→◦)
