module Calf.Value.Abstraction where

open import Cubical.Foundations.GroupoidLaws using (rUnit)
open import Cubical.Foundations.Univalence

open import Calf.Core.Abstract
open import Calf.Value
open import Calf.Value.Closed as ●
open import Calf.Value.Glue as Glue hiding (square)
open import Calf.Value.Open as ◯
open import Calf.Value.Product as ×
open import Calf.Value.Sigma

open Fracture

Abstraction-Fracture : {X-⊤ X-abs : 𝒱} → (X-⊤ → X-abs) → Fracture
Abstraction-Fracture {X-⊤} {X-abs} χ .X• = ●• X-⊤
Abstraction-Fracture {X-⊤} {X-abs} χ .X◦ = ◯◦ X-abs
Abstraction-Fracture {X-⊤} {X-abs} χ .χ• = ●.map (χ ⨾ η◦)

private variable X-⊤ X-abs Y-⊤ Y-abs Z-⊤ Z-abs : 𝒱

Abstraction : (X-⊤ → X-abs) → 𝒱
Abstraction = fromFracture ∘ Abstraction-Fracture

module _ {χ : X-⊤ → X-abs} where
  Abstraction-path : ∀ {x x' : Abstraction χ}
    → isSet X-abs
    → proj• x ≡ proj• x'
    → proj◦ x ≡ proj◦ x'
    → x ≡ x'
  Abstraction-path = Glue-path ∘ isSet◯

  Abstraction-path-open : ∀ {x x' : Abstraction χ}
    → (abs : ⟨ ABS ⟩)
    → proj◦ x abs ≡ proj◦ x' abs
    → x ≡ x'
  Abstraction-path-open {x} {x'} abs p◦ =
    Σ≡Prop
      (λ _ → isProp→isSet (isContr→isProp (◯-isConnected abs)) _ _)
      (ΣPathP
        ( isContr→isProp (◯-isConnected abs) _ _
        , funExt λ abs' →
            cong (proj◦ x) (str ABS abs' abs) ∙ p◦ ∙ cong (proj◦ x') (str ABS abs abs')
        ))

  isSetAbstraction : isSet X-⊤ → isSet X-abs → isSet (Abstraction χ)
  isSetAbstraction isSetX-⊤ isSetX-abs = isSetGlue (isSet● isSetX-⊤) (isSet◯ isSetX-abs)

Abstraction-id : (X : 𝒱) → X ≃ Abstraction (id {X})
Abstraction-id X = fracture , fracture-isEquiv

square
  : (χ : X-⊤ → X-abs) (ψ : Y-⊤ → Y-abs)
  → (f-⊤ : X-⊤ → Y-⊤)
  → (f-abs : X-abs → Y-abs)
  → ((x-⊤ : X-⊤) → ψ (f-⊤ x-⊤) ≡ f-abs (χ x-⊤))
  → Abstraction χ → Abstraction ψ
square χ ψ f-⊤ f-abs f-coh =
  Glue.square
    (●.map f-⊤)
    (◯.map f-abs)
    (●.elim (λ _ → ●.isModal●≡) (cong (η• ∘ η◦) ∘ f-coh))

module _ (χ : X-⊤ → X-abs) where
  triangle
    : (x-⊤ : X-⊤) (x-abs : X-abs)
    → χ x-⊤ ≡ x-abs
    → Abstraction χ
  triangle x-⊤ x-abs p = (η• x-⊤ , η◦ x-abs) , cong (η• ∘ η◦) p

  inj-⊤ : X-⊤ → Abstraction χ
  inj-⊤ x-⊤ = triangle x-⊤ (χ x-⊤) refl

  proj-abs : Abstraction χ → X-abs
  proj-abs = square χ id χ id (λ _ → refl) ⨾ invEq (Abstraction-id X-abs)

  inj-proj : (x-⊤ : X-⊤) → proj-abs (inj-⊤ x-⊤) ≡ χ x-⊤
  inj-proj x-⊤ =
      invEq (Abstraction-id X-abs) (square χ id χ id (λ _ → refl) (inj-⊤ x-⊤))
    ≡⟨ cong (invEq (Abstraction-id X-abs) ∘ (fst (fracture _) ,_)) (sym (rUnit refl)) ⟩
      invEq (Abstraction-id X-abs) (fracture (χ x-⊤))
    ≡⟨ retEq (Abstraction-id X-abs) (χ x-⊤) ⟩
      χ x-⊤
    ∎

Abstraction-× :
  (χ : X-⊤ → X-abs) (ψ : Y-⊤ → Y-abs)
  → Abstraction χ × Abstraction ψ ≃ Abstraction (×.map χ ψ)
Abstraction-× χ ψ =
  isoToEquiv $ iso
    (λ (((x-⊤ , x-abs) , x-coh) , ((y-⊤ , y-abs) , y-coh)) → (equivFun ●-× (x-⊤ , y-⊤) , equivFun ◯-× (x-abs , y-abs)) , {!   !})
    (λ p → square _ χ proj₁ proj₁ (λ _ → refl) p , square _ ψ proj₂ proj₂ (λ _ → refl) p)
    {!   !}
    {!   !}

square₂
  : (χ : X-⊤ → X-abs) (ψ : Y-⊤ → Y-abs) (ζ : Z-⊤ → Z-abs)
  → (f-⊤ : X-⊤ → Y-⊤ → Z-⊤)
  → (f-abs : X-abs → Y-abs → Z-abs)
  → ((x-⊤ : X-⊤) (y-⊤ : Y-⊤) → ζ (f-⊤ x-⊤ y-⊤) ≡ f-abs (χ x-⊤) (ψ y-⊤))
  → Abstraction χ → Abstraction ψ → Abstraction ζ
square₂ χ ψ ζ f-⊤ f-abs f-coh =
  curry $
  square _ ζ (uncurry f-⊤) (uncurry f-abs) (uncurry f-coh) ∘
  equivFun (Abstraction-× χ ψ)

Abstraction-open
  : (χ : X-⊤ → X-abs)
  → ⟨ ABS ⟩
  → Abstraction χ ≃ X-abs
Abstraction-open {X-⊤} {X-abs} χ abs =
  Glue-open (Abstraction-Fracture χ) abs ∙ₑ ◯-open abs

square-openP
  : (χ : X-⊤ → X-abs) (β : Y-⊤ → Y-abs)
  → (f-⊤ : X-⊤ → Y-⊤) (f-abs : X-abs → Y-abs)
  → (f-coh : (x-⊤ : X-⊤) → β (f-⊤ x-⊤) ≡ f-abs (χ x-⊤))
  → (abs : ⟨ ABS ⟩)
  → PathP
      (λ i → ua (Abstraction-open χ abs) i → ua (Abstraction-open β abs) i)
      (square χ β f-⊤ f-abs f-coh)
      f-abs
square-openP χ β _ _ _ abs =
  ua→ λ x → ua-gluePath (Abstraction-open β abs) refl

triangle-openP
  : (χ : X-⊤ → X-abs)
  → (x-⊤ : X-⊤) (x-abs : X-abs) (x-coh : χ x-⊤ ≡ x-abs)
  → (abs : ⟨ ABS ⟩)
  → PathP (λ i → ua (Abstraction-open χ abs) i)
      (triangle χ x-⊤ x-abs x-coh)
      x-abs
triangle-openP χ _ _ _ abs =
  ua-gluePath (Abstraction-open χ abs) refl
