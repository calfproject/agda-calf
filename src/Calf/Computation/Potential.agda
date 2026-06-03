open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma

module Calf.Computation.Potential where

open import Calf.Core.Abstract
open import Calf.Core.Cost
open import Calf.Value
open import Calf.Value.Closed as ●ᵛ
open import Calf.Computation
open import Calf.Computation.Open as ◯ᶜ
open import Calf.Computation.Closed as ●ᶜ
open import Calf.Computation.Glue

open 𝒞-FRAC

▷'-FRAC : val ℂ → 𝒞 → 𝒞-FRAC
▷'-FRAC c A .A• = ●ᶜ A , ●ᶜ.η-isEquiv
▷'-FRAC c A .A◦ = ◯ᶜ A , ◯ᶜ.η-isEquiv
▷'-FRAC c A .α• = ●ᶜ.map (CHARGE c ⨾⊸ η◦ᶜ)

▷'[_] : val ℂ → 𝒞 → 𝒞
▷'[ c ] A = Glueᶜ' A A (CHARGE c)

▷'-FRAC-open : ⟨ ABS ⟩ → (c : val ℂ) (A : 𝒞) → ▷'-FRAC c A ≡ 𝒞-toFRAC A
▷'-FRAC-open abs c A i .A• = 𝒞-toFRAC A .A•
▷'-FRAC-open abs c A i .A◦ = 𝒞-toFRAC A .A◦
▷'-FRAC-open abs c A i .α• =
  ●ᶜ.map-open abs
    (CHARGE c ⨾⊸ η◦ᶜ)
    η◦ᶜ
    i

opaque
  unfolding Glueᶜ'

  ▷'-open : ⟨ ABS ⟩ → (c : val ℂ) (A : 𝒞) → ▷'[ c ] A ≡ A
  ▷'-open abs c A = cong 𝒞-fromFRAC (▷'-FRAC-open abs c A) ∙ 𝒞-glue-fracture-retract A

store' : ∀ {c A} → A ⊸ ▷'[ c ] A
store' {c} {A} =
  subst (_⊸ ▷'[ c ] A) Glueᶜ'-id $
  squareᶜ'
    {A-⊤ = A} {A-abs = A} {α = id⊸}
    {B-⊤ = A} {B-abs = A} {β = CHARGE c}
    id⊸
    (CHARGE c)
    (λ _ → refl)

release' : ▷'[ c ] A ⊸ A
release' {c} {A} =
  subst (▷'[ c ] A ⊸_) Glueᶜ'-id $
  squareᶜ'
    {A-⊤ = A} {A-abs = A} {α = CHARGE c}
    {B-⊤ = A} {B-abs = A} {β = id⊸}
    (CHARGE c)
    id⊸
    (λ _ → refl)

▷'-map : (A ⊸ B) → (▷'[ c ] A ⊸ ▷'[ c ] B)
▷'-map {A} {B} {c} f =
  squareᶜ'
    {A-⊤ = A} {A-abs = A} {α = CHARGE c}
    {B-⊤ = B} {B-abs = B} {β = CHARGE c}
    f
    f
    (sym ∘ f .charge c)


ℙ : 𝒱
ℙ = ●ᵛ ℂ

variable
  p q r s : val ℙ

▷[_] : val ℙ → 𝒞 → 𝒞
▷[ η• c ] A = ▷'[ c ] A
▷[ ∗ p ] A = A
▷[ law c p i ] A = ▷'-open p c A i

release : ∀ {p A} → ▷[ p ] A ⊸ A
release {η• c} = release'
release {∗ p} = id⊸
release {law c p i} = {!   !}
