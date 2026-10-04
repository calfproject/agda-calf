module Calf.Computation.Seal where

open import Calf.Core.Abstract
open import Calf.Value
import Calf.Value.Closed as ●
open import Calf.Value.Glue using (proj•; proj◦)
import Calf.Value.Open as ◯
open import Calf.Value.Product
open import Calf.Value.Seal
open import Calf.Value.Sigma
open import Calf.Computation
open import Calf.Computation.Abstraction
open import Calf.Computation.Closed as ●ᶜ hiding (map; join)
open import Calf.Computation.Glue
  using (Glueᶜ; Fractureᶜ; toFractureᶜ; fromFractureᶜ; glue•ᶜ; glue◦ᶜ; glue•→◦ᶜ)
open import Calf.Computation.Open as ◯ᶜ hiding (map; join)

Glueᵈᶜ : {A• A◦ : 𝒞} (α• : A• ⊸ ●ᶜ A◦) → 𝒞
Glueᵈᶜ {A•} {A◦} α• .U = Glueᵈ (U α•)
Glueᵈᶜ {A•} {A◦} α• .is-preorder =
  isPreorderGlueᵈ
    (A• .is-preorder)
    (A◦ .is-preorder)
Glueᵈᶜ {A•} {A◦} α• .charge c ((x• , x◦) , p) =
  (A• .charge c x• , A◦ .charge c x◦) ,
  ≡∙⊑ (α• .charge c x•) (mono (●ᶜ A◦ .charge c) p)
Glueᵈᶜ {A•} {A◦} α• .charge-0 =
  Glueᵈ-path (A◦ .is-preorder) (A• .charge-0) (A◦ .charge-0)
Glueᵈᶜ {A•} {A◦} α• .charge-+ =
  Glueᵈ-path (A◦ .is-preorder) (A• .charge-+) (A◦ .charge-+)

module _ {A• A◦ : 𝒞} {α• : A• ⊸ ●ᶜ A◦} where
  proj•ᵈᶜ : Glueᵈᶜ α• ⊸ A•
  proj•ᵈᶜ .U = proj•ᵈ
  proj•ᵈᶜ .charge c g = refl

  proj◦ᵈᶜ : Glueᵈᶜ α• ⊸ A◦
  proj◦ᵈᶜ .U = proj◦ᵈ
  proj◦ᵈᶜ .charge c g = refl

  proj•→◦ᵈᶜ : (aᵈ : U (Glueᵈᶜ α•)) → α• .U (proj•ᵈᶜ .U aᵈ) ⊑ η• (proj◦ᵈᶜ .U aᵈ)
  proj•→◦ᵈᶜ = proj•→◦ᵈ

  ⊸-Glueᵈᶜ-≃ : {A : 𝒞}
    → (A ⊸ Glueᵈᶜ α•)
    ≃ (Σ[ (f• , f◦) ∈ (A ⊸ A•) × (A ⊸ A◦) ] ((a : U A) → α• .U (f• .U a) ⊑ η• (f◦ .U a)))
  ⊸-Glueᵈᶜ-≃ {A} = isoToEquiv (iso fwd bwd sec ret)
    where
      fwd :
        (A ⊸ Glueᵈᶜ α•)
        → Σ[ (f• , f◦) ∈ (A ⊸ A•) × (A ⊸ A◦) ] ((a : U A) → α• .U (f• .U a) ⊑ η• (f◦ .U a))
      fwd f = (f ⨾ᶜ proj•ᵈᶜ , f ⨾ᶜ proj◦ᵈᶜ) , proj•→◦ᵈᶜ ∘ f .U

      bwd :
        (Σ[ (f• , f◦) ∈ (A ⊸ A•) × (A ⊸ A◦) ] ((a : U A) → α• .U (f• .U a) ⊑ η• (f◦ .U a)))
        → (A ⊸ Glueᵈᶜ α•)
      bwd ((f• , f◦) , f-coh) .U a =
        (f• .U a , f◦ .U a) , f-coh a
      bwd ((f• , f◦) , f-coh) .charge c a =
        Glueᵈ-path (A◦ .is-preorder) (f• .charge c a) (f◦ .charge c a)

      sec : section fwd bwd
      sec _ =
        Σ≡Prop (λ _ → isPropΠ λ _ → is-thin (●ᶜ A◦) _ _)
          (ΣPathP (funExtᶜ (λ _ → refl) , funExtᶜ (λ _ → refl)))

      ret : retract fwd bwd
      ret _ = funExtᶜ λ _ → refl

open Fractureᶜ

fromFractureᵈᶜ : Fractureᶜ → 𝒞
fromFractureᵈᶜ F = Glueᵈᶜ (F .α•)

Fractureᶜ-Squareᵈ : Fractureᶜ → Fractureᶜ → 𝒱
Fractureᶜ-Squareᵈ F₁ F₂ =
  Σ[ (f• , f◦) ∈ (⟨ F₁ .A• ⟩ᶜ ⊸ ⟨ F₂ .A• ⟩ᶜ) × (⟨ F₁ .A◦ ⟩ᶜ ⊸ ⟨ F₂ .A◦ ⟩ᶜ) ]
    ((a : U ⟨ F₁ .A• ⟩ᶜ) → F₂ .α• .U (f• .U a) ⊑ ●ᶜ.map f◦ .U (F₁ .α• .U a))

module _ {A• A◦} {α• : A• ⊸ ●ᶜ A◦} {B• B◦} {β• : B• ⊸ ●ᶜ B◦} where
  squareᵈ-Glueᶜ
    : (f• : A• ⊸ B•)
    → (f◦ : A◦ ⊸ B◦)
    → ((a : U A•) → β• .U (f• .U a) ⊑ ●ᶜ.map f◦ .U (α• .U a))
    → Glueᶜ α• ⊸ Glueᵈᶜ β•
  squareᵈ-Glueᶜ f• f◦ f-coh .U = squareᵈ (f• .U) (f◦ .U) f-coh
  squareᵈ-Glueᶜ f• f◦ f-coh .charge c a =
    Glueᵈ-path (is-preorder B◦) (f• .charge c (proj• a)) (f◦ .charge c (proj◦ a))

  Glueᵈᶜ-≃
    : (e• : A• ≃ᶜ B•)
    → (e◦ : A◦ ≃ᶜ B◦)
    → ((a : U A•) → β• .U (equivFunᶜ e• .U a) ≡ ●ᶜ.map (equivFunᶜ e◦) .U (α• .U a))
    → Glueᵈᶜ α• ≃ᶜ Glueᵈᶜ β•
  Glueᵈᶜ-≃ e• e◦ e-coh = fwd , equivIsEquiv equiv
    where
      equiv : Glueᵈ (U α•) ≃ Glueᵈ (U β•)
      equiv =
        Σ-cong-equiv (≃-× (U-≃ e•) (U-≃ e◦)) λ (a• , _) →
          monoEquiv (U-≃ (●ᶜ-≃ e◦)) ∙ₑ ≡∙⊑Equiv (e-coh a•)

      fwd : _ ⊸ _
      fwd .U = equivFun equiv
      fwd .charge c aᵈ =
        Glueᵈ-path
          (is-preorder B◦)
          (equivFunᶜ e• .charge c (proj•ᵈ aᵈ))
          (equivFunᶜ e◦ .charge c (proj◦ᵈ aᵈ))

Sealᶜ : 𝒞 → 𝒞
Sealᶜ = fromFractureᵈᶜ ∘ toFractureᶜ

Sealᶜ-fromFractureᶜ : (F : Fractureᶜ) → Sealᶜ (fromFractureᶜ F) ≃ᶜ fromFractureᵈᶜ F
Sealᶜ-fromFractureᶜ F = Glueᵈᶜ-≃ (glue•ᶜ F) (glue◦ᶜ F) (glue•→◦ᶜ F)

Sealᶜ-open : ⟨ ABS ⟩ → Sealᶜ A ≃ᶜ A
Sealᶜ-open {A} abs =
  proj◦ᵈᶜ ⨾ᶜ ◯ᶜ-eval-open abs A ,
  subst isEquiv
    (funExt λ a → transportRefl _ ∙ cong (proj◦ᵈ a) (transportRefl _))
    (equivIsEquiv (Seal-open abs))

fracture-and-gluing-squareᵈᶜ : (A ⊸ Sealᶜ B) ≃ Fractureᶜ-Squareᵈ (toFractureᶜ A) (toFractureᶜ B)
fracture-and-gluing-squareᵈᶜ {A} {B} =
    (A ⊸ Sealᶜ B)
  ≃⟨ ⊸-Glueᵈᶜ-≃ ⟩
    (Σ[ (f• , f◦) ∈ (A ⊸ ●ᶜ B) × (A ⊸ ◯ᶜ B) ] ((a : U A) → ●.map η◦ (f• .U a) ⊑ η• (f◦ .U a)))
  ≃⟨
    invEquiv
      (Σ-cong-equiv
        (≃-× (⊸-precomp-η•ᶜ-≃ (●ᶜ• B)) (⊸-precomp-η◦ᶜ-≃ (◯ᶜ◦ B)))
        (λ _ → ●.precomp-η-≃Π λ _ → ●.isModal⊑ ●.isModal●))
  ⟩
    Fractureᶜ-Squareᵈ (toFractureᶜ A) (toFractureᶜ B)
  ■

pairᵈᶜ
  : (f• : A ⊸ ●ᶜ B)
  → (f◦ : A ⊸ ◯ᶜ B)
  → ((a : U A) → ●.map η◦ (f• .U a) ⊑ η• (f◦ .U a))
  → A ⊸ Sealᶜ B
pairᵈᶜ f• f◦ f-coh = invEq ⊸-Glueᵈᶜ-≃ ((f• , f◦) , f-coh)

map : (A ⊸ B) → (Sealᶜ A ⊸ Sealᶜ B)
map {A} {B} f =
  pairᵈᶜ (proj•ᵈᶜ ⨾ᶜ ●ᶜ.map f) (proj◦ᵈᶜ ⨾ᶜ ◯ᶜ.map f) λ a →
    let open ⊑-Reasoning (●ᶜ (◯ᶜ B)) in
    begin
      ●.map η◦ (●.map (f .U) (proj•ᵈ a))
    ≡ᴾ⟨ ●.map-∘ (f .U) η◦ (proj•ᵈ a) ⟩
      ●.map (η◦ ∘ (f .U)) (proj•ᵈ a)
    ≡ᴾ⟨ cong (λ g → ●.map g (proj•ᵈ a)) (η◦-isNatural (f .U)) ⟩
      ●.map (◯.map (f .U) ∘ η◦) (proj•ᵈ a)
    ≡ᴾ⟨ sym (●.map-∘ η◦ (◯.map (f .U)) (proj•ᵈ a)) ⟩
      ●.map (◯.map (f .U)) (●.map η◦ (proj•ᵈ a))
    ⊑⟨ mono (●.map (◯.map (f .U))) (proj•→◦ᵈ a) ⟩
      ●.map (◯.map (f .U)) (η• (proj◦ᵈ a))
    ≡ᴾ⟨ refl ⟩
      η• (◯.map (f .U) (proj◦ᵈ a))
    ∎ᴾ

join : Sealᶜ (Sealᶜ A) ⊸ Sealᶜ A
join {A} =
  pairᵈᶜ (proj•ᵈᶜ ⨾ᶜ ●ᶜ.bind proj•ᵈᶜ) (proj◦ᵈᶜ ⨾ᶜ ◯ᶜ.bind proj◦ᵈᶜ) λ a →
    let open ⊑-Reasoning (●ᶜ (◯ᶜ A)) in
    begin
      ●.map η◦ (●.bind (proj•ᵈ a) proj•ᵈ)
    ≡ᴾ⟨ ●.bind-map proj•ᵈ η◦ (proj•ᵈ a) ⟩
      ●.bind (proj•ᵈ a) (●.map η◦ ∘ proj•ᵈ)
    ⊑⟨ mono (●.bind (proj•ᵈ a)) (funExtᵈ proj•→◦ᵈ) ⟩
      ●.bind (proj•ᵈ a) (η• ∘ proj◦ᵈ)
    ≡ᴾ⟨ ●.bind-η• proj◦ᵈ (proj•ᵈ a) ⟩
      ●.map proj◦ᵈ (proj•ᵈ a)
    ≡ᴾ⟨ refl ⟩
      ●.map (flip ◯.bind proj◦ᵈ ∘ η◦) (proj•ᵈ a)
    ≡ᴾ⟨ sym (●.map-∘ η◦ (flip ◯.bind proj◦ᵈ) (proj•ᵈ a)) ⟩
      ●.map (flip ◯.bind proj◦ᵈ) (●.map η◦ (proj•ᵈ a))
    ⊑⟨ mono (●.map (flip ◯.bind proj◦ᵈ)) (proj•→◦ᵈ a) ⟩
      η• (◯.bind (proj◦ᵈ a) proj◦ᵈ)
    ∎ᴾ

infix 1 _⊸ᵈ_
_⊸ᵈ_ : 𝒞 → 𝒞 → 𝒱
A ⊸ᵈ B = A ⊸ Sealᶜ B

idᵈ : A ⊸ᵈ A
idᵈ .U = fractureᵈ
idᵈ {A} .charge c a = Glueᵈ-path (◯ᶜ A .is-preorder) refl refl

⌈_⌉ : (A ⊸ B) → (A ⊸ᵈ B)
⌈ f ⌉ = f ⨾ᶜ idᵈ

infixl 9 _⨾ᵈ_
_⨾ᵈ_ : (A ⊸ᵈ B) → (B ⊸ᵈ C) → (A ⊸ᵈ C)
_⨾ᵈ_ f g = f ⨾ᶜ map g ⨾ᶜ join

squareᵈᶜ : ∀ {A-⊤ A-abs B-⊤ B-abs}
  → (α : A-⊤ ⊸ A-abs) (β : B-⊤ ⊸ B-abs)
  → (f-⊤ : A-⊤ ⊸ B-⊤)
  → (f-abs : A-abs ⊸ B-abs)
  → ((a-⊤ : U A-⊤) → U β (U f-⊤ a-⊤) ⊑ U f-abs (U α a-⊤))
  → Abstractionᶜ α ⊸ᵈ Abstractionᶜ β
squareᵈᶜ {B-abs = B-abs} α β f-⊤ f-abs f-coh =
  aux ⨾ᶜ invEqᶜ (Sealᶜ-fromFractureᶜ (Abstractionᶜ-Fracture β))
  where
    aux : Abstractionᶜ α ⊸ fromFractureᵈᶜ (Abstractionᶜ-Fracture β)
    aux =
      squareᵈ-Glueᶜ (●ᶜ.map f-⊤) (◯ᶜ.map f-abs) λ a• →
        let open ⊑-Reasoning (●ᶜ (◯ᶜ B-abs)) in
        begin
          ●.map (η◦ ∘ β .U) (●.map (f-⊤ .U) a•)
        ≡ᴾ⟨ ●.map-∘ (f-⊤ .U) (η◦ ∘ β .U) a• ⟩
          ●.map (η◦ ∘ β .U ∘ f-⊤ .U) a•
        ⊑⟨ mono (λ g → ●.map g a•) (funExtᵈ (mono η◦ ∘ f-coh)) ⟩
          ●.map (η◦ ∘ f-abs .U ∘ α .U) a•
        ≡ᴾ⟨ sym (●.map-∘ (η◦ ∘ α .U) (◯.map (f-abs .U)) a•) ⟩
          ●.map (◯.map (f-abs .U)) (●.map (η◦ ∘ α .U) a•)
        ∎ᴾ
