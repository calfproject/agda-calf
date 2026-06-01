open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma

module Calf.Computation.Open where

open import Calf.Core.Abstract
open import Calf.Value
open import Calf.Value.Open using (η◦ᵛ)
open import Calf.Value.Open hiding (◯ᵛ; η◦ᵛ) renaming (◯ᵛ-ηᵛ-isEquiv to ◯ᶜ-ηᶜ-isEquiv) public
open import Calf.Computation
open import Calf.Computation.Power

◯ᶜ : 𝒞 → 𝒞
◯ᶜ = fromProp ABS ⇀_

η◦ᶜ : A ⊸ ◯ᶜ A
η◦ᶜ {A} .U = η◦ᵛ {A .U}
η◦ᶜ .charge _ _ = refl
η◦ᶜ .seal = {!   !}

𝒞◦ : Type₁
𝒞◦ = Σ[ A ∈ 𝒞 ] isEquiv (η◦ᶜ {A} .U)

𝒞◦-path : {A◦ B◦ : 𝒞◦} → A◦ .fst ≡ B◦ .fst → A◦ ≡ B◦
𝒞◦-path p = Σ≡Prop (λ A → isPropIsEquiv (η◦ᶜ {A} .U)) p

U◦ : 𝒞◦ → 𝒱◦
U◦ A◦ .fst = A◦ .fst .U
U◦ A◦ .snd = A◦ .snd
