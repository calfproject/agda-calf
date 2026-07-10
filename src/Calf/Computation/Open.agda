open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma

module Calf.Computation.Open where

open import Calf.Core.Abstract
open import Calf.Value
open import Calf.Value.Open as ◯ hiding (map; join; bind) public
open import Calf.Computation
open import Calf.Computation.Power

◯ᶜ : 𝒞 → 𝒞
◯ᶜ = ⟨ ABS ⟩ ⇀_

η◦ᶜ : A ⊸ ◯ᶜ A
η◦ᶜ .U = η◦
η◦ᶜ .charge _ _ = refl

𝒞◦ : 𝒱₁
𝒞◦ = 𝒞WithStr λ A → isEquiv (η◦ᶜ {A} .U)

𝒞◦-path : {A◦ B◦ : 𝒞◦} → ⟨ A◦ ⟩ᶜ ≡ ⟨ B◦ ⟩ᶜ → A◦ ≡ B◦
𝒞◦-path p = Σ≡Prop (λ A → isPropIsEquiv (η◦ᶜ {A} .U)) p

U◦ : 𝒞◦ → 𝒱◦
U◦ A◦ .fst = ⟨ A◦ ⟩ᶜ .U
U◦ A◦ .snd = A◦ .snd

map : (A ⊸ B) → (◯ᶜ A ⊸ ◯ᶜ B)
map f .U = ◯.map (f .U)
map f .charge c a◦ = funExt λ abs → f .charge c (a◦ abs)

map-∘ : (f : A ⊸ B) (g : B ⊸ C) → map f ⨾ᶜ map g ≡ map (f ⨾ᶜ g)
map-∘ f g = ⊸-path refl refl (funExt λ _ → refl)

join : ◯ᶜ (◯ᶜ A) ⊸ ◯ᶜ A
join .U = ◯.join
join .charge c a◦ = refl

bind : (A ⊸ ◯ᶜ B) → (◯ᶜ A ⊸ ◯ᶜ B)
bind {B = B} k = map k ⨾ᶜ join {B}

module _ where
  open import Calf.Computation.Pullback

  lex : (f : A ⊸ C) (g : B ⊸ C) → ◯ᶜ (Pullback f g) ≡ Pullback (map f) (map g)
  lex {A} {B} {C} f g = conservativity fwd fwd-equiv
    where
      fwd : ◯ᶜ (Pullback f g) ⊸ Pullback (map f) (map g)
      fwd .U e =
        (λ abs → e abs .fst) , (λ abs → e abs .snd .fst) , funExt (λ abs → e abs .snd .snd)
      fwd .charge c e =
        ΣPathP (refl , ΣPathP (refl , isProp→PathP (λ i → (◯ᶜ B) .is-set _ _) _ _))

      inv : U (Pullback (map f) (map g)) → U (◯ᶜ (Pullback f g))
      inv (a◦ , b◦ , p) abs = a◦ abs , b◦ abs , funExt⁻ p abs

      fwd-equiv : isEquivᶜ fwd
      fwd-equiv = isoToIsEquiv (iso (fwd .U) inv (λ _ → refl) (λ _ → refl))
