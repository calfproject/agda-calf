open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Foundations.Equiv

module Calf.Computation.Potential (φ : Type) (φ-isProp : isProp φ) where

open import Calf.Core.Cost
open import Calf.Value
open import Calf.Value.Closed φ φ-isProp as ◯ᵛ
open import Calf.Computation
open import Calf.Computation.Open φ φ-isProp as ◯ᶜ
open import Calf.Computation.Closed φ φ-isProp as ●ᶜ
open import Calf.Computation.Glue φ φ-isProp

open 𝒞-FRAC

ℙ : 𝒱
ℙ = ●ᵛ ℂ

variable
  p q r s : val ℙ

▷'-FRAC : val ℂ → 𝒞 → 𝒞-FRAC
▷'-FRAC c A .A• = ●ᶜ A , ●ᶜ-ηᶜ-isEquiv
▷'-FRAC c A .A◦ = ◯ᶜ A , ◯ᶜ-ηᶜ-isEquiv
▷'-FRAC c A .α = ●ᶜ.map (CHARGE c ⨾⊸ η◦ᶜ)

▷'[_] : val ℂ → 𝒞 → 𝒞
▷'[ c ] A = Glueᶜ (●ᶜ A , ●ᶜ-ηᶜ-isEquiv) (◯ᶜ A , ◯ᶜ-ηᶜ-isEquiv) (●ᶜ.map (CHARGE c ⨾⊸ η◦ᶜ))

▷'-FRAC-open : φ → (c : val ℂ) (A : 𝒞) → ▷'-FRAC c A ≡ 𝒞-toFRAC A
▷'-FRAC-open p c A i .A• = 𝒞-toFRAC A .A•
▷'-FRAC-open p c A i .A◦ = 𝒞-toFRAC A .A◦
▷'-FRAC-open p c A i .α =
  ●ᶜ.map-open p
    (CHARGE c ⨾⊸ η◦ᶜ)
    η◦ᶜ
    i

▷'-open : φ → (c : val ℂ) (A : 𝒞) → ▷'[ c ] A ≡ A
▷'-open p c A = cong 𝒞-fromFRAC (▷'-FRAC-open p c A) ∙ 𝒞-glue-fracture-retract A

▷[_] : val ℙ → 𝒞 → 𝒞
▷[ η• c ] A = ▷'[ c ] A
▷[ ∗ p ] A = A
▷[ law c p i ] A = ▷'-open p c A i
