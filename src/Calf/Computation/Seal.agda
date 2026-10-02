module Calf.Computation.Seal where

open import Cubical.Data.Sigma using (ΣPathP; Σ≡Prop; Σ-cong-equiv; ≃-×)

open import Calf.Core.Abstract
open import Calf.Value
import Calf.Value.Closed as ●
open import Calf.Value.Glue using (proj•; proj◦)
import Calf.Value.Open as ◯
open import Calf.Value.Product
open import Calf.Value.Seal
open import Calf.Computation
open import Calf.Computation.Abstraction
open import Calf.Computation.Closed as ●ᶜ hiding (map; join)
open import Calf.Computation.Glue
  using (Glueᶜ; Fractureᶜ; toFractureᶜ; fromFractureᶜ; glue•ᶜ; glue◦ᶜ; glue•→◦ᶜ)
open import Calf.Computation.Open as ◯ᶜ hiding (map; join)

private
  thin● : (A : 𝒞) → isThin (● (U A))
  thin● A = isPreorder→isThin (isPreorder● (A .is-preorder))

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
  Σ≡Prop (λ _ → thin● A◦ _ _) (ΣPathP (A• .charge-0 , A◦ .charge-0))
Glueᵈᶜ {A•} {A◦} α• .charge-+ =
  Σ≡Prop (λ _ → thin● A◦ _ _) (ΣPathP (A• .charge-+ , A◦ .charge-+))

module _ {A• A◦ : 𝒞} {α• : A• ⊸ ●ᶜ A◦} where
  proj•ᵈᶜ : Glueᵈᶜ α• ⊸ A•
  proj•ᵈᶜ .U = proj•ᵈ
  proj•ᵈᶜ .charge c g = refl

  proj◦ᵈᶜ : Glueᵈᶜ α• ⊸ A◦
  proj◦ᵈᶜ .U = proj◦ᵈ
  proj◦ᵈᶜ .charge c g = refl

  proj•→◦ᵈᶜ : (aᵈ : U (Glueᵈᶜ α•)) → α• .U (proj•ᵈᶜ .U aᵈ) ⊑ η• (proj◦ᵈᶜ .U aᵈ)
  proj•→◦ᵈᶜ = proj•→◦ᵈ

open Fractureᶜ

fromFractureᵈᶜ : Fractureᶜ → 𝒞
fromFractureᵈᶜ F = Glueᵈᶜ (F .α•)

Fractureᵈᶜ-Square : Fractureᶜ → Fractureᶜ → 𝒱
Fractureᵈᶜ-Square F F' =
  Σ[ (f• , f◦) ∈ (⟨ F .A• ⟩ᶜ ⊸ ⟨ F' .A• ⟩ᶜ) × (⟨ F .A◦ ⟩ᶜ ⊸ ⟨ F' .A◦ ⟩ᶜ) ]
    f• ⨾ᶜ F' .α• ⊑ F .α• ⨾ᶜ ●ᶜ.map f◦

squareᵈ-Glueᶜ
  : ∀ {A• A◦ α• B• B◦ β•}
  → (f• : A• ⊸ B•)
  → (f◦ : A◦ ⊸ B◦)
  → f• ⨾ᶜ β• ⊑ α• ⨾ᶜ ●ᶜ.map f◦
  → Glueᶜ α• ⊸ Glueᵈᶜ β•
squareᵈ-Glueᶜ f• f◦ f-coh .U =
  squareᵈ (f• .U) (f◦ .U) (funExtᵈ⁻ (mono U f-coh))
squareᵈ-Glueᶜ {B◦ = B◦} f• f◦ f-coh .charge c a =
  Σ≡Prop (λ _ → is-thin (●ᶜ B◦) _ _)
    (ΣPathP (f• .charge c (proj• a) , f◦ .charge c (proj◦ a)))

Glueᵈᶜ-≃
  : ∀ {A• A◦ α• B• B◦ β•}
  → (e• : A• ≃ᶜ B•)
  → (e◦ : A◦ ≃ᶜ B◦)
  → equivFunᶜ e• ⨾ᶜ β• ≡ α• ⨾ᶜ ●ᶜ.map (equivFunᶜ e◦)
  → Glueᵈᶜ α• ≃ᶜ Glueᵈᶜ β•
Glueᵈᶜ-≃ {α• = α•} {B◦ = B◦} {β•} e• e◦ e-coh = fwd , equivIsEquiv equiv
  where
    equiv : Glueᵈ (U α•) ≃ Glueᵈ (U β•)
    equiv =
      Σ-cong-equiv (≃-× (U-≃ e•) (U-≃ e◦)) λ (a• , _) →
        monoEquiv (U-≃ (●ᶜ-≃ e◦)) ∙ₑ ≡∙⊑Equiv (funExtᶜ⁻ e-coh a•)

    fwd : _ ⊸ _
    fwd .U = equivFun equiv
    fwd .charge c aᵈ =
      Σ≡Prop (λ _ → is-thin (●ᶜ B◦) _ _)
        (ΣPathP (equivFunᶜ e• .charge c (proj•ᵈ aᵈ) , equivFunᶜ e◦ .charge c (proj◦ᵈ aᵈ)))

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

pairᵈᶜ
  : (f• : A ⊸ ●ᶜ B)
  → (f◦ : A ⊸ ◯ᶜ B)
  → ((a : U A) → ●.map η◦ (f• .U a) ⊑ η• (f◦ .U a))
  → A ⊸ Sealᶜ B
pairᵈᶜ f• f◦ f-coh .U aᵈ = (f• .U aᵈ , f◦ .U aᵈ) , f-coh aᵈ
pairᵈᶜ {A} {B} f• f◦ f-coh .charge c a =
  Σ≡Prop (λ _ → is-thin (●ᶜ (◯ᶜ B)) _ _)
    (ΣPathP (f• .charge c a , f◦ .charge c a))

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
idᵈ {A} .charge c a = Σ≡Prop (λ _ → thin● (◯ᶜ A) _ _) refl

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
      squareᵈ-Glueᶜ (●ᶜ.map f-⊤) (◯ᶜ.map f-abs) $ funExtᵈᶜ λ a• →
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
