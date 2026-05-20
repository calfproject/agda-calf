open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Calf.Computation.Closed (φ : Type) (φ-isProp : isProp φ) where

open import Calf.Value
open import Calf.Value.Closed φ φ-isProp public
open import Calf.Computation
open import Calf.Computation.Power
open import Cubical.Foundations.Equiv

●ᶜ : 𝒞 → 𝒞
●ᶜ A .U = ●ᵛ (A .U)
●ᶜ A .charge c (η• a) = η• (A .charge c a)
●ᶜ A .charge c (∗ p) = ∗ p
●ᶜ A .charge c (law a p i) = law (A .charge c a) p i
●ᶜ A .charge/0 {η• a} = cong η• (A .charge/0)
●ᶜ A .charge/0 {∗ p} = refl
●ᶜ A .charge/0 {law a p i} = {!   !}
●ᶜ A .charge/+ {η• a} = cong η• (A .charge/+)
●ᶜ A .charge/+ {∗ p} = refl
●ᶜ A .charge/+ {law a p i} = {!   !}

η•ᶜ : A ⊸ ●ᶜ A
η•ᶜ .U = η•
η•ᶜ .charge _ _ = refl

𝒞• : Type₁
𝒞• = Σ[ A ∈ 𝒞 ] isEquiv (η•ᶜ {A} .U)

U• : 𝒞• → 𝒱•
U• A• .fst = A• .fst .U
U• A• .snd = A• .snd
