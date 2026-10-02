module Calf.Computation.Glue.Base where

open import Cubical.Foundations.Univalence using (ua; ua→)
open import Cubical.Data.Sigma

open import Calf.Value
open import Calf.Computation
open import Calf.Computation.Closed as ●ᶜ
open import Calf.Computation.Open as ◯ᶜ

open import Calf.Value.Glue public

Glueᶜ : {A• A◦ : 𝒞} (α• : A• ⊸ ●ᶜ A◦) → 𝒞
Glueᶜ {A•} {A◦} α• .U = Glue (α• .U)
Glueᶜ {A•} {A◦} α• .is-preorder = isPreorderGlue (A• .is-preorder) (A◦ .is-preorder)
Glueᶜ {A•} {A◦} α• .charge c ((x• , x◦) , h) =
  (A• .charge c x• , A◦ .charge c x◦) ,
  α• .charge c x• ∙ cong (●ᶜ A◦ .charge c) h
Glueᶜ {A•} {A◦} α• .charge-0 =
  Glue-path (is-set A◦) (A• .charge-0) (A◦ .charge-0)
Glueᶜ {A•} {A◦} α• .charge-+ =
  Glue-path (is-set A◦) (A• .charge-+) (A◦ .charge-+)

module _ {A• A◦ : 𝒞} {α• : A• ⊸ ●ᶜ A◦} where
  proj•ᶜ : Glueᶜ α• ⊸ A•
  proj•ᶜ .U = proj•
  proj•ᶜ .charge _ _ = refl

  proj◦ᶜ : Glueᶜ α• ⊸ A◦
  proj◦ᶜ .U = proj◦
  proj◦ᶜ .charge _ _ = refl

  proj•→◦ᶜ : proj•ᶜ ⨾ᶜ α• ≡ proj◦ᶜ ⨾ᶜ η•ᶜ
  proj•→◦ᶜ = funExtᶜ proj•→◦

  ⊸-Glueᶜ-≃ : {A : 𝒞}
    → (A ⊸ Glueᶜ α•)
    ≃ (Σ[ (f• , f◦) ∈ (A ⊸ A•) × (A ⊸ A◦) ] f• ⨾ᶜ α• ≡ f◦ ⨾ᶜ η•ᶜ)
  ⊸-Glueᶜ-≃ {A} = isoToEquiv (iso fwd bwd sec ret)
    where
      fwd : (A ⊸ Glueᶜ α•) → Σ[ (f• , f◦) ∈ (A ⊸ A•) × (A ⊸ A◦) ] f• ⨾ᶜ α• ≡ f◦ ⨾ᶜ η•ᶜ
      fwd f =
        (f ⨾ᶜ proj•ᶜ , f ⨾ᶜ proj◦ᶜ) ,
        ⨾ᶜ-assoc f proj•ᶜ α• ∙ cong (f ⨾ᶜ_) proj•→◦ᶜ ∙ sym (⨾ᶜ-assoc f proj◦ᶜ η•ᶜ)

      bwd : (Σ[ (f• , f◦) ∈ (A ⊸ A•) × (A ⊸ A◦) ] f• ⨾ᶜ α• ≡ f◦ ⨾ᶜ η•ᶜ) → (A ⊸ Glueᶜ α•)
      bwd ((f• , f◦) , f-coh) .U a =
        (f• .U a , f◦ .U a) , funExt⁻ (cong U f-coh) a
      bwd ((f• , f◦) , f-coh) .charge c a =
        Glue-path (is-set A◦) (f• .charge c a) (f◦ .charge c a)

      sec : section fwd bwd
      sec ((f• , f◦) , f-coh) =
        Σ≡Prop (λ _ → isSet⊸ _ _)
          (ΣPathP (funExtᶜ (λ _ → refl) , funExtᶜ (λ _ → refl)))

      ret : retract fwd bwd
      ret f = funExtᶜ λ a → Σ≡Prop (λ _ → is-set (●ᶜ A◦) _ _) refl

record Fractureᶜ : 𝒱₁ where
  field
    A• : 𝒞•
    A◦ : 𝒞◦
    α• : ⟨ A• ⟩ᶜ ⊸ ●ᶜ ⟨ A◦ ⟩ᶜ
open Fractureᶜ

Fractureᶜ-path
  : {F F' : Fractureᶜ}
  → (p• : ⟨ F .A• ⟩ᶜ ≡ ⟨ F' .A• ⟩ᶜ)
  → (p◦ : ⟨ F .A◦ ⟩ᶜ ≡ ⟨ F' .A◦ ⟩ᶜ)
  → PathP
      (λ i → p• i ⊸ ●ᶜ (p◦ i))
      (F .α•)
      (F' .α•)
  → F ≡ F'
Fractureᶜ-path {F} {F'} A•-path A◦-path α•-path i .A• = 𝒞•-path {F .A•} {F' .A•} A•-path i
Fractureᶜ-path {F} {F'} A•-path A◦-path α•-path i .A◦ = 𝒞◦-path {F .A◦} {F' .A◦} A◦-path i
Fractureᶜ-path {F} {F'} A•-path A◦-path α•-path i .α• = α•-path i

Fractureᶜ-ua
  : {F F' : Fractureᶜ}
  → (e• : ⟨ F .A• ⟩ᶜ ≃ᶜ ⟨ F' .A• ⟩ᶜ)
  → (e◦ : ⟨ F .A◦ ⟩ᶜ ≃ᶜ ⟨ F' .A◦ ⟩ᶜ)
  → F' .α• .U ∘ equivFunᶜ e• .U ≡ ●ᶜ.map (equivFunᶜ e◦) .U ∘ F .α• .U
  → F ≡ F'
Fractureᶜ-ua e• e◦ e•→◦ =
  Fractureᶜ-path
    (uaᶜ e•)
    (uaᶜ e◦)
    (⊸-path
      (uaᶜ e•)
      (cong ●ᶜ (uaᶜ e◦))
      (ua→ λ a• → ●-ua-gluePath (U-≃ e◦) (funExt⁻ (sym e•→◦) a•)))

fromFractureᶜ : Fractureᶜ → 𝒞
fromFractureᶜ F = Glueᶜ (F .α•)

toFractureᶜ : 𝒞 → Fractureᶜ
toFractureᶜ A .A• = ●ᶜ• A
toFractureᶜ A .A◦ = ◯ᶜ◦ A
toFractureᶜ A .α• = ●ᶜ.map η◦ᶜ

U-Fracture : Fractureᶜ → Fracture
U-Fracture F =
  record
    { X• = U• (F .A•)
    ; X◦ = U◦ (F .A◦)
    ; χ• = U (F .α•)
    }

Fractureᶜ-Square : Fractureᶜ → Fractureᶜ → 𝒱
Fractureᶜ-Square F F' =
  Σ[ (f• , f◦) ∈ (⟨ F .A• ⟩ᶜ ⊸ ⟨ F' .A• ⟩ᶜ) × (⟨ F .A◦ ⟩ᶜ ⊸ ⟨ F' .A◦ ⟩ᶜ) ]
    f• ⨾ᶜ F' .α• ≡ F .α• ⨾ᶜ ●ᶜ.map f◦

squareᶜ
  : ∀ {A• A◦ α• B• B◦ β•}
  → (f• : A• ⊸ B•)
  → (f◦ : A◦ ⊸ B◦)
  → f• ⨾ᶜ β• ≡ α• ⨾ᶜ ●ᶜ.map f◦
  → Glueᶜ α• ⊸ Glueᶜ β•
squareᶜ f• f◦ f-coh .U =
  square
    (f• .U)
    (f◦ .U)
    (funExt⁻ (cong U f-coh))
squareᶜ {B◦ = B◦} f• f◦ f-coh .charge c a =
  Σ≡Prop (λ _ → is-set (●ᶜ B◦) _ _)
    (ΣPathP (f• .charge c (proj• a) , f◦ .charge c (proj◦ a)))

Glueᶜ-≃
  : ∀ {A• A◦ α• B• B◦ β•}
  → (e• : A• ≃ᶜ B•)
  → (e◦ : A◦ ≃ᶜ B◦)
  → equivFunᶜ e• ⨾ᶜ β• ≡ α• ⨾ᶜ ●ᶜ.map (equivFunᶜ e◦)
  → Glueᶜ α• ≃ᶜ Glueᶜ β•
Glueᶜ-≃ {α• = α•} {β• = β•} e• e◦ coh =
  squareᶜ (equivFunᶜ e•) (equivFunᶜ e◦) coh ,
  square-isEquiv (U α•) (U β•) (funExt⁻ (cong U coh)) (equivIsEquivᶜ e•) (equivIsEquivᶜ e◦)
