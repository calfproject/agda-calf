open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Foundations.Equiv

module Calf.Computation.Potential (φ : Type) (φ-isProp : isProp φ) where

open import Calf.Core.Cost
open import Calf.Value
open import Calf.Computation
open import Calf.Computation.Open φ φ-isProp as ◯ᶜ
open import Calf.Computation.Closed φ φ-isProp as ●ᶜ
open import Calf.Computation.Glue φ φ-isProp

ℙ : 𝒱
ℙ = ℂ -- ●ᵛ ℂ

variable
  p q r s : val ℙ

▷[_] : val ℙ → 𝒞 → 𝒞
▷[ p ] A = Glueᶜ (●ᶜ A , ●ᶜ-ηᶜ-isEquiv) (◯ᶜ A , ◯ᶜ-ηᶜ-isEquiv) (●ᶜ.map (CHARGE p ⨾⊸ η∘ᶜ))
