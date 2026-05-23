open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Foundations.Equiv

module Calf.Computation.Closed (φ : Type) (φ-isProp : isProp φ) where

open import Calf.Core.Cost
open import Calf.Value
open import Calf.Value.Closed φ φ-isProp as ●ᵛ using (●ᵛ; η•; ∗; law; 𝒱•)
open import Calf.Computation

●ᶜ : 𝒞 → 𝒞
●ᶜ A .U = ●ᵛ (A .U)
●ᶜ A .charge c (η• a) = η• (A .charge c a)
●ᶜ A .charge c (∗ p) = ∗ p
●ᶜ A .charge c (law a p i) = law (A .charge c a) p i
●ᶜ A .charge/0 {η• a} = cong η• (A .charge/0)
●ᶜ A .charge/0 {∗ p} = refl
●ᶜ A .charge/0 {law a p i} =
  isProp→PathP
    (λ i → 𝒱.isSet𝒱 (●ᶜ A .U)
      (●ᶜ A .charge 0ℂ (law a p i))
      (law a p i))
    (cong η• (A .charge/0))
    refl
    i
●ᶜ A .charge/+ {η• a} = cong η• (A .charge/+)
●ᶜ A .charge/+ {∗ p} = refl
●ᶜ A .charge/+ {law a p i} {c₁} {c₂} =
  isProp→PathP
    (λ i → 𝒱.isSet𝒱 (●ᶜ A .U)
      (●ᶜ A .charge (c₁ +ℂ c₂) (law a p i))
      (●ᶜ A .charge c₁ (●ᶜ A .charge c₂ (law a p i))))
    (cong η• (A .charge/+))
    refl
    i

η•ᶜ : A ⊸ ●ᶜ A
η•ᶜ .U = η•
η•ᶜ .charge _ _ = refl

𝒞• : Type₁
𝒞• = Σ[ A ∈ 𝒞 ] isEquiv (η•ᶜ {A} .U)

𝒞•-path : {A• B• : 𝒞•} → A• .fst ≡ B• .fst → A• ≡ B•
𝒞•-path p = Σ≡Prop (λ A → isPropIsEquiv (η•ᶜ {A} .U)) p

U• : 𝒞• → 𝒱•
U• A• .fst = A• .fst .U
U• A• .snd = A• .snd

map : (A ⊸ B) → (●ᶜ A ⊸ ●ᶜ B)
map f .U = ●ᵛ.map (f .U)
map f .charge c (η• a) = cong η• (f .charge c a)
map f .charge c (∗ p) = refl
map {A} {B} f .charge c (law a p i) =
  isProp→PathP
    (λ i → 𝒱.isSet𝒱 (●ᶜ B .U)
      (map f .U (●ᶜ A .charge c (law a p i)))
      (●ᶜ B .charge c (map f .U (law a p i))))
    (cong η• (f .charge c a))
    refl
    i
