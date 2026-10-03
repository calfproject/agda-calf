module Calf.Directed.Path where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties using (congEquiv)
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Path using (compPathrEquiv)
open import Cubical.Data.Sigma
open import Cubical.Reflection.StrictEquiv
open import Relation.Binary using (_⇒_)
open import Relation.Binary.Definitions using (Reflexive)

open import Calf.Core.Interval

module _ {X : Type} where

  infix 4 _⊑_
  _⊑_ : X → X → Type
  x ⊑ x' = Σ[ p ∈ (𝟚 → X) ] ((p 0𝟚 ≡ x) × (p 1𝟚 ≡ x'))

  path : {x x' : X} → x ⊑ x' → 𝟚 → X
  path e = e .fst

  path₀ : {x x' : X} (e : x ⊑ x') → path e 0𝟚 ≡ x
  path₀ e = e .snd .fst

  path₁ : {x x' : X} (e : x ⊑ x') → path e 1𝟚 ≡ x'
  path₁ e = e .snd .snd

  ⊑-reflexive : _≡_ ⇒ _⊑_
  ⊑-reflexive {x = x} x≡x' = (λ _ → x) , refl , x≡x'

  ⊑-refl : Reflexive _⊑_
  ⊑-refl = ⊑-reflexive refl

  ≡∙⊑ : {x y z : X} → x ≡ y → y ⊑ z → x ⊑ z
  ≡∙⊑ h e = path e , path₀ e ∙ sym h , path₁ e

  ⊑∙≡ : {x y z : X} → x ⊑ y → y ≡ z → x ⊑ z
  ⊑∙≡ e h = path e , path₀ e , path₁ e ∙ h

private variable X Y : Type

mono : (f : X → Y) {x x' : X} → x ⊑ x' → f x ⊑ f x'
mono f e = f ∘ path e , cong f (path₀ e) , cong f (path₁ e)

module _ {Y : X → Type} {f f' : (x : X) → Y x} where
  funExtᵈ : ((x : X) → f x ⊑ f' x) → f ⊑ f'
  funExtᵈ pointwise =
      (λ 𝕚 x → path (pointwise x) 𝕚)
    , funExt (path₀ ∘ pointwise)
    , funExt (path₁ ∘ pointwise)

  funExtᵈ⁻ : f ⊑ f' → ((x : X) → f x ⊑ f' x)
  funExtᵈ⁻ p x =
      (λ 𝕚 → path p 𝕚 x)
    , funExt⁻ (path₀ p) x
    , funExt⁻ (path₁ p) x

  funExtᵈEquiv : ((x : X) → f x ⊑ f' x) ≃ (f ⊑ f')
  unquoteDef funExtᵈEquiv = defStrictEquiv funExtᵈEquiv funExtᵈ funExtᵈ⁻

monoEquiv : {x x' : X} (e : X ≃ Y) → (x ⊑ x') ≃ (equivFun e x ⊑ equivFun e x')
monoEquiv e = Σ-cong-equiv (equivΠCod (const e)) λ _ → ≃-× (congEquiv e) (congEquiv e)

≡∙⊑Equiv : {x y z : X} → x ≡ y → (y ⊑ z) ≃ (x ⊑ z)
≡∙⊑Equiv h = Σ-cong-equiv-snd λ _ → ≃-× (compPathrEquiv (sym h)) (idEquiv _)

isContr⊑ : isContr X → {x x' : X} → isContr (x ⊑ x')
isContr⊑ isContrX =
  isContrΣ
    (isContrΠ (const isContrX))
    (λ _ →
      isContrΣ
        (isContr→isContrPath isContrX _ _)
        (const (isContr→isContrPath isContrX _ _)))
