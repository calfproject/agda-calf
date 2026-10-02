module Calf.Value.Glue.Base where

open import Cubical.Foundations.Equiv.Properties using (congEquiv)
open import Cubical.Foundations.Path using (compPathlEquiv)
open import Cubical.Foundations.Univalence using (ua; ua→)
open import Cubical.Data.Sigma using (ΣPathP; Σ≡Prop; Σ-cong-equiv; ≃-×)

open import Calf.Value
open import Calf.Value.Closed as ●
open import Calf.Value.Open as ◯
open import Calf.Value.Product

Glue : {X• X◦ : 𝒱} (χ• : X• → ● X◦) → 𝒱
Glue {X•} {X◦} χ• = Σ[ (x• , x◦) ∈ X• × X◦ ] χ• x• ≡ η• x◦

module _ {X• X◦ : 𝒱} {χ• : X• → ● X◦} where
  proj• : Glue χ• → X•
  proj• ((x• , _) , _) = x•

  proj◦ : Glue χ• → X◦
  proj◦ ((_ , x◦) , _) = x◦

  proj•→◦ : (x : Glue χ•) → χ• (proj• x) ≡ η• (proj◦ x)
  proj•→◦ = proj₂

  opaque
    Glue-path : ∀ {x x' : Glue χ•}
      → isSet X◦
      → proj• x ≡ proj• x'
      → proj◦ x ≡ proj◦ x'
      → x ≡ x'
    Glue-path isSetX◦ p• p◦ =
      Σ≡Prop (λ _ → isSet● isSetX◦ _ _) (ΣPathP (p• , p◦))

  opaque
    isSetGlue : isSet X• → isSet X◦ → isSet (Glue χ•)
    isSetGlue isSetX• isSetX◦ =
      isSetΣ
        (isSet× isSetX• isSetX◦)
        λ _ → isProp→isSet (isSet● isSetX◦ _ _)

  opaque
    isPreorderGlue : isPreorder X• → isPreorder X◦ → isPreorder (Glue χ•)
    isPreorderGlue isPreorderX• isPreorderX◦ =
      isLocalPullback isPreorderX• isPreorderX◦ (isPreorder● isPreorderX◦) χ• η•

record Fracture : 𝒱₁ where
  field
    X• : 𝒱•
    X◦ : 𝒱◦
    χ• : ⟨ X• ⟩ → ● ⟨ X◦ ⟩
open Fracture

Fracture-path
  : {F F' : Fracture}
  → (X•-path : F .X• ≡ F' .X•)
  → (X◦-path : F .X◦ ≡ F' .X◦)
  → PathP
      (λ i → X•-path i .fst → ● (X◦-path i .fst))
      (F .χ•)
      (F' .χ•)
  → F ≡ F'
Fracture-path X•-path X◦-path χ•-path i .X• = X•-path i
Fracture-path X•-path X◦-path χ•-path i .X◦ = X◦-path i
Fracture-path X•-path X◦-path χ•-path i .χ• = χ•-path i

Fracture-ua
  : {F F' : Fracture}
  → (e• : ⟨ F .X• ⟩ ≃ ⟨ F' .X• ⟩)
  → (e◦ : ⟨ F .X◦ ⟩ ≃ ⟨ F' .X◦ ⟩)
  → F' .χ• ∘ equivFun e• ≡ ●.map (equivFun e◦) ∘ F .χ•
  → F ≡ F'
Fracture-ua e• e◦ e•→◦ =
  Fracture-path
    (𝒱•-path (ua e•))
    (𝒱◦-path (ua e◦))
    (ua→ λ x• → ●-ua-gluePath e◦ (sym (funExt⁻ e•→◦ x•)))

fromFracture : Fracture → 𝒱
fromFracture F = Glue (F .χ•)

toFracture : 𝒱 → Fracture
toFracture X .X• = ●• X
toFracture X .X◦ = ◯◦ X
toFracture X .χ• = ●.map η◦

Fracture-Square : Fracture → Fracture → 𝒱
Fracture-Square F₁ F₂ =
  Σ[ (f• , f◦) ∈ (⟨ F₁ .X• ⟩ → ⟨ F₂ .X• ⟩) × (⟨ F₁ .X◦ ⟩ → ⟨ F₂ .X◦ ⟩) ]
    F₂ .χ• ∘ f• ≡ ●.map f◦ ∘ F₁ .χ•

square
  : ∀ {X• X◦ χ Y• Y◦ ψ}
  → (f• : X• → Y•)
  → (f◦ : X◦ → Y◦)
  → ((x• : X•) → ψ (f• x•) ≡ ●.map f◦ (χ x•))
  → Glue χ → Glue ψ
square f• f◦ f-coh ((x• , x◦) , h) =
  (f• x• , f◦ x◦) , f-coh x• ∙ cong (●.map f◦) h

square-isEquiv
  : ∀ {X• X◦} (χ : X• → ● X◦) {Y• Y◦} (ψ : Y• → ● Y◦) {f• : X• → Y•} {f◦ : X◦ → Y◦}
  → (f-coh : (x• : X•) → ψ (f• x•) ≡ ●.map f◦ (χ x•))
  → isEquiv f• → isEquiv f◦ → isEquiv (square {χ = χ} {ψ = ψ} f• f◦ f-coh)
square-isEquiv χ ψ {f•} {f◦} f-coh e• e◦ =
  equivIsEquiv
    (Σ-cong-equiv (≃-× (f• , e•) (f◦ , e◦)) λ (x• , x◦) →
      congEquiv (●.map f◦ , ●.map-isEquiv e◦) ∙ₑ compPathlEquiv (f-coh x•))
