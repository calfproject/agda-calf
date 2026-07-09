open import Calf.Core.Abstract
open import Calf.Value

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

module Calf.Value.Open where

◯ : 𝒱 → 𝒱
◯ X = (abs : ⟨ ABS ⟩) → X

◯' : (⟨ ABS ⟩ → 𝒱) → 𝒱
◯' X = (abs : ⟨ ABS ⟩) → X abs

η◦ : {X : 𝒱} → X → ◯ X
η◦ x _ = x

map : {X Y : 𝒱} → (X → Y) → ◯ X → ◯ Y
map f x◦ abs = f (x◦ abs)

η◦-isNatural : {X Y : 𝒱} (f : X → Y) → η◦ ∘ f ≡ map f ∘ η◦
η◦-isNatural f = funExt λ x → refl

𝒱◦ : 𝒱₁
𝒱◦ = TypeWithStr _ λ X → isEquiv (η◦ {X})

join : {X : 𝒱} → ◯ (◯ X) → ◯ X
join x abs = x abs abs

bind : {X Y : 𝒱} → ◯ X → (X → ◯ Y) → ◯ Y
bind x◦ k = join (map k x◦)

η-isEquiv : {X : 𝒱} → isEquiv (η◦ {◯ X})
η-isEquiv = isoToIsEquiv (iso η◦ join η◦-join join-η◦)
  where
    η◦-join : {X : 𝒱} → (x : ◯ (◯ X)) → η◦ (join x) ≡ x
    η◦-join x = funExt λ abs → funExt λ q → cong (λ r → x r q) (str ABS q abs)

    join-η◦ : {X : 𝒱} → (x : ◯ X) → join (η◦ x) ≡ x
    join-η◦ x = refl

◯-preserves-isSet : isSet X → isSet (◯ X)
◯-preserves-isSet = isSet→

isPreorder◯ : isPreorder X → isPreorder (◯ X)
isPreorder◯ isPreorderX = isLocalΠ λ _ → isPreorderX
