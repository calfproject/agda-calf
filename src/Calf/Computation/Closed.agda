open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma

module Calf.Computation.Closed where

open import Calf.Core.Abstract
open import Calf.Core.Cost
open import Calf.Value
open import Calf.Value.Closed as ●ᵛ hiding (map; map-∘; join; bind) public
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
    (λ i → ●ᶜ A .U .is-set
      (●ᶜ A .charge 0ℂ (law a p i))
      (law a p i))
    (cong η• (A .charge/0))
    refl
    i
●ᶜ A .charge/+ {η• a} = cong η• (A .charge/+)
●ᶜ A .charge/+ {∗ p} = refl
●ᶜ A .charge/+ {law a p i} {c₁} {c₂} =
  isProp→PathP
    (λ i → ●ᶜ A .U .is-set
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
    (λ i → ●ᶜ B .U .is-set
      (map f .U (●ᶜ A .charge c (law a p i)))
      (●ᶜ B .charge c (map f .U (law a p i))))
    (cong η• (f .charge c a))
    refl
    i

map-∘ : (f : A ⊸ B) (g : B ⊸ C) → map f ⨾ᶜ map g ≡ map (f ⨾ᶜ g)
map-∘ f g = ⊸-path refl refl (funExt (●ᵛ.map-∘ (f .U) (g .U)))

map-open : ⟨ ABS ⟩ → (f g : A ⊸ B) → map f ≡ map g
map-open {A} {B} p f g =
  ⊸-path
    {A₀ = ●ᶜ A}
    {A₁ = ●ᶜ A}
    {B₀ = ●ᶜ B}
    {B₁ = ●ᶜ B}
    refl
    refl
    (funExt λ a• →
      ●-isProp p
        (map {A = A} {B = B} f .U a•)
        (map {A = A} {B = B} g .U a•))

join : ●ᶜ (●ᶜ A) ⊸ ●ᶜ A
join .U = ●ᵛ.join
join .charge c (η• a•) = refl
join .charge c (∗ abs) = refl
join {A = A} .charge c (law a• abs i) =
  isProp→PathP
    (λ i → ●ᶜ A .U .is-set
      (join {A = A} .U (●ᶜ (●ᶜ A) .charge c (law a• abs i)))
      (●ᶜ A .charge c (join {A = A} .U (law a• abs i))))
    refl
    refl
    i

bind : (A ⊸ ●ᶜ B) → (●ᶜ A ⊸ ●ᶜ B)
bind k = map k ⨾ᶜ join

bind-map : (k : A ⊸ ●ᶜ B) (f : B ⊸ C) → bind k ⨾ᶜ map f ≡ bind (k ⨾ᶜ map f)
bind-map {A = A} {B = B} {C = C} k f =
  ⊸-path refl refl (funExt h)
  where
    h : (a• : cmp (●ᶜ A)) →
      (bind k ⨾ᶜ map f) .U a• ≡ bind (k ⨾ᶜ map f) .U a•
    h (η• a) = refl
    h (∗ p) = refl
    h (law a p i) =
      isProp→PathP
        (λ i → ●ᶜ C .U .is-set
          ((bind k ⨾ᶜ map f) .U (law a p i))
          (bind (k ⨾ᶜ map f) .U (law a p i)))
        refl
        refl
        i

bind-η• : (f : A ⊸ B) → bind (f ⨾ᶜ η•ᶜ) ≡ map f
bind-η• {A = A} {B = B} f =
  ⊸-path refl refl (funExt h)
  where
    h : (a• : cmp (●ᶜ A)) → bind (f ⨾ᶜ η•ᶜ) .U a• ≡ map f .U a•
    h (η• a) = refl
    h (∗ p) = refl
    h (law a p i) =
      isProp→PathP
        (λ i → ●ᶜ B .U .is-set
          (bind (f ⨾ᶜ η•ᶜ) .U (law a p i))
          (map f .U (law a p i)))
        refl
        refl
        i
