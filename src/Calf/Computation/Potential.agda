open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
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

ℙ : 𝒱
ℙ = ●ᵛ ℂ

variable
  p q r s : val ℙ

▷'-FRAC : val ℂ → 𝒞 → 𝒞-FRAC
▷'-FRAC c A .A• = ●ᶜ A , ●ᶜ-η•ᶜ-isEquiv {A}
▷'-FRAC c A .A◦ = ◯ᶜ A , ◯ᶜ-ηᶜ-isEquiv
▷'-FRAC c A .α = ●ᶜ.map (CHARGE c ⨾⊸ η◦ᶜ)

▷'[_] : val ℂ → 𝒞 → 𝒞
▷'[ c ] A = Glueᶜ (●ᶜ A , ●ᶜ-η•ᶜ-isEquiv {A}) (◯ᶜ A , ◯ᶜ-ηᶜ-isEquiv) (●ᶜ.map (CHARGE c ⨾⊸ η◦ᶜ))

▷'-FRAC-open : ⟨ ABS ⟩ → (c : val ℂ) (A : 𝒞) → ▷'-FRAC c A ≡ 𝒞-toFRAC A
▷'-FRAC-open abs c A i .A• = 𝒞-toFRAC A .A•
▷'-FRAC-open abs c A i .A◦ = 𝒞-toFRAC A .A◦
▷'-FRAC-open abs c A i .α =
  ●ᶜ.map-open abs
    (CHARGE c ⨾⊸ η◦ᶜ)
    η◦ᶜ
    i

▷'-open : ⟨ ABS ⟩ → (c : val ℂ) (A : 𝒞) → ▷'[ c ] A ≡ A
▷'-open abs c A = cong 𝒞-fromFRAC (▷'-FRAC-open abs c A) ∙ 𝒞-glue-fracture-retract A

▷'-map : (A ⊸ B) → (▷'[ c ] A ⊸ ▷'[ c ] B)
▷'-map = {!   !}

release' : ▷'[ c ] A ⊸ A
release' .U = {!   !}
release' .charge = {!   !}

▷[_] : val ℙ → 𝒞 → 𝒞
▷[ η• c ] A = ▷'[ c ] A
▷[ ∗ p ] A = A
▷[ law c p i ] A = ▷'-open p c A i
