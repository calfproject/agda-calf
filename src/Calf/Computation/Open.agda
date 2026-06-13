open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma

module Calf.Computation.Open where

open import Calf.Core.Abstract
open import Calf.Value
open import Calf.Value.Open as ◯ᵛ hiding (map; join; bind) public
open import Calf.Computation
open import Calf.Computation.Power

◯ᶜ : 𝒞 → 𝒞
◯ᶜ = fromProp ABS ⇀_

η◦ᶜ : A ⊸ ◯ᶜ A
η◦ᶜ {A} .U = η◦ᵛ {A .U}
η◦ᶜ .charge _ _ = refl

𝒞◦ : Type₁
𝒞◦ = Σ[ A ∈ 𝒞 ] isEquiv (η◦ᶜ {A} .U)

𝒞◦-path : {A◦ B◦ : 𝒞◦} → A◦ .fst ≡ B◦ .fst → A◦ ≡ B◦
𝒞◦-path p = Σ≡Prop (λ A → isPropIsEquiv (η◦ᶜ {A} .U)) p

U◦ : 𝒞◦ → 𝒱◦
U◦ A◦ .fst = A◦ .fst .U
U◦ A◦ .snd = A◦ .snd

map : (A ⊸ B) → (◯ᶜ A ⊸ ◯ᶜ B)
map f .U = ◯ᵛ.map (f .U)
map f .charge c a◦ = funExt λ abs → f .charge c (a◦ abs)

join : ◯ᶜ (◯ᶜ A) ⊸ ◯ᶜ A
join .U = ◯ᵛ.join
join .charge c a◦ = refl

bind : (A ⊸ ◯ᶜ B) → (◯ᶜ A ⊸ ◯ᶜ B)
bind {B = B} k = map k ⨾ᶜ join {B}
