open import Cubical.Modalities.Modality
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path using (compPathlEquiv; compPathrEquiv)
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma

module Calf.Computation.Closed where

open import Calf.Core.Abstract
open import Calf.Core.Cost
open import Calf.Value
open import Calf.Value.Closed as ● hiding (map; map-∘; join; bind) public
open import Calf.Computation

●ᶜ : 𝒞 → 𝒞
●ᶜ A .U = ● (A .U)
●ᶜ A .is-set = isSet● (A .is-set)
●ᶜ A .charge c (η• a) = η• (A .charge c a)
●ᶜ A .charge c (∗ p) = ∗ p
●ᶜ A .charge c (law a p i) = law (A .charge c a) p i
●ᶜ A .charge/0 {η• a} = cong η• (A .charge/0)
●ᶜ A .charge/0 {∗ p} = refl
●ᶜ A .charge/0 {law a p i} =
  isProp→PathP
    (λ i → ●ᶜ A .is-set
      (●ᶜ A .charge 0ℂ (law a p i))
      (law a p i))
    (cong η• (A .charge/0))
    refl
    i
●ᶜ A .charge/+ {η• a} = cong η• (A .charge/+)
●ᶜ A .charge/+ {∗ p} = refl
●ᶜ A .charge/+ {law a p i} {c₁} {c₂} =
  isProp→PathP
    (λ i → ●ᶜ A .is-set
      (●ᶜ A .charge (c₁ +ℂ c₂) (law a p i))
      (●ᶜ A .charge c₁ (●ᶜ A .charge c₂ (law a p i))))
    (cong η• (A .charge/+))
    refl
    i

η•ᶜ : A ⊸ ●ᶜ A
η•ᶜ .U = η•
η•ᶜ .charge _ _ = refl

isModalᶜ : 𝒞 → 𝒱
isModalᶜ A = isModal (U A)

𝒞• : 𝒱₁
𝒞• = 𝒞WithStr isModalᶜ

𝒞•-path : {A• B• : 𝒞•} → ⟨ A• ⟩ᶜ ≡ ⟨ B• ⟩ᶜ → A• ≡ B•
𝒞•-path p = Σ≡Prop (λ A → isPropIsEquiv (η•ᶜ {A} .U)) p

isModalᶜ●ᶜ : isModalᶜ (●ᶜ A)
isModalᶜ●ᶜ = isModal●

●ᶜ• : 𝒞 → 𝒞•
●ᶜ• A = ●ᶜ A , isModalᶜ●ᶜ {A}

U• : 𝒞• → 𝒱•
U• A• .fst = ⟨ A• ⟩ᶜ .U
U• A• .snd = A• .snd

map : (A ⊸ B) → (●ᶜ A ⊸ ●ᶜ B)
map f .U = ●.map (f .U)
map f .charge c (η• a) = cong η• (f .charge c a)
map f .charge c (∗ p) = refl
map {A} {B} f .charge c (law a p i) =
  isProp→PathP
    (λ i → ●ᶜ B .is-set
      (map f .U (●ᶜ A .charge c (law a p i)))
      (●ᶜ B .charge c (map f .U (law a p i))))
    (cong η• (f .charge c a))
    refl
    i

●ᶜ-charge-map
  : (c : ℂ) (a• : U (●ᶜ A))
  → ●ᶜ A .charge c a• ≡ ●.map (A .charge c) a•
●ᶜ-charge-map _ =
  ●.elim
    (λ _ → Modality.◯-=-isModal ●Modality _ _)
    (λ _ → refl)

map-∘ : (f : A ⊸ B) (g : B ⊸ C) → map f ⨾ᶜ map g ≡ map (f ⨾ᶜ g)
map-∘ f g = ⊸-path refl refl (funExt (●.map-∘ (f .U) (g .U)))

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
      ◯-isProp● p
        (map {A = A} {B = B} f .U a•)
        (map {A = A} {B = B} g .U a•))

join : ●ᶜ (●ᶜ A) ⊸ ●ᶜ A
join .U = ●.join
join .charge c (η• a•) = refl
join .charge c (∗ abs) = refl
join {A = A} .charge c (law a• abs i) =
  isProp→PathP
    (λ i → ●ᶜ A .is-set
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
    h : (a• : U (●ᶜ A)) →
      (bind k ⨾ᶜ map f) .U a• ≡ bind (k ⨾ᶜ map f) .U a•
    h (η• a) = refl
    h (∗ p) = refl
    h (law a p i) =
      isProp→PathP
        (λ i → ●ᶜ C .is-set
          ((bind k ⨾ᶜ map f) .U (law a p i))
          (bind (k ⨾ᶜ map f) .U (law a p i)))
        refl
        refl
        i

bind-η• : (f : A ⊸ B) → bind (f ⨾ᶜ η•ᶜ) ≡ map f
bind-η• {A = A} {B = B} f =
  ⊸-path refl refl (funExt h)
  where
    h : (a• : U (●ᶜ A)) → bind (f ⨾ᶜ η•ᶜ) .U a• ≡ map f .U a•
    h (η• a) = refl
    h (∗ p) = refl
    h (law a p i) =
      isProp→PathP
        (λ i → ●ᶜ B .is-set
          (bind (f ⨾ᶜ η•ᶜ) .U (law a p i))
          (map f .U (law a p i)))
        refl
        refl
        i

●ᶜ-rec : (B• : 𝒞•) → (A ⊸ ⟨ B• ⟩ᶜ) → (●ᶜ A ⊸ ⟨ B• ⟩ᶜ)
●ᶜ-rec B• g .U = ●.elim (λ _ → strᶜ B•) (g .U)
●ᶜ-rec B• g .charge c = ●.elim (λ a• → ●.isModal≡ (strᶜ B•)) (g .charge c)

⊸-precomp-η•ᶜ-isEquiv : {A : 𝒞} (B• : 𝒞•)
  → isEquiv (λ (f : ●ᶜ A ⊸ ⟨ B• ⟩ᶜ) → η•ᶜ ⨾ᶜ f)
⊸-precomp-η•ᶜ-isEquiv B• =
  isoToIsEquiv (iso (η•ᶜ ⨾ᶜ_) (●ᶜ-rec B•)
    (λ g → ⊸-path refl refl refl)
    (λ f → ⊸-path refl refl
      (funExt (●.elim (λ a• → ●.isModal≡ (strᶜ B•)) (λ a → refl)))))

⊸-precomp-η•ᶜ-≃ : {A : 𝒞} (B• : 𝒞•) → (●ᶜ A ⊸ ⟨ B• ⟩ᶜ) ≃ (A ⊸ ⟨ B• ⟩ᶜ)
⊸-precomp-η•ᶜ-≃ B• = (η•ᶜ ⨾ᶜ_) , ⊸-precomp-η•ᶜ-isEquiv B•

●ᶜ-map-CHARGE
  : (c : ℂ) (a• : U (●ᶜ A))
  → map (CHARGE {A = A} c) .U a• ≡ ●ᶜ A .charge c a•
●ᶜ-map-CHARGE c (η• a) = refl
●ᶜ-map-CHARGE c (∗ p) = refl
●ᶜ-map-CHARGE {A = A} c (law a p i) =
  isProp→PathP
    (λ i → ●ᶜ A .is-set
      (map (CHARGE {A = A} c) .U (law a p i))
      (●ᶜ A .charge c (law a p i)))
    refl
    refl
    i

module _ {A B C : 𝒞} where
  open import Calf.Computation.Pullback

  lex : (f : A ⊸ C) (g : B ⊸ C) → ●ᶜ (Pullback f g) ≡ Pullback (map f) (map g)
  lex f g = conservativity fwd (equivIsEquiv e)
    where
      e : U (●ᶜ (Pullback f g)) ≃ U (Pullback (map f) (map g))
      e = ●.●-pullback

      isProp-at : ⟨ ABS ⟩ → isProp (U (Pullback (map f) (map g)))
      isProp-at abs =
        isPropΣ (◯-isProp● abs) λ _ →
        isPropΣ (◯-isProp● abs) λ _ →
        isProp→isSet (◯-isProp● abs) _ _

      fwd : ●ᶜ (Pullback f g) ⊸ Pullback (map f) (map g)
      fwd .U = equivFun e
      fwd .charge c =
        ind-prop _ (λ _ → Pullback (map f) (map g) .is-set _ _)
          (λ t → ΣPathP (refl , ΣPathP (refl , isProp→PathP (λ i → ●ᶜ C .is-set _ _) _ _)))
          (λ abs → isProp-at abs _ _)

module _ where
  open import Calf.Computation.Copower

  Σᶜ-●ᶜ : ∀ {X A} → ●ᶜ (Σᶜ X A) ≡ ●ᶜ (Σᶜ X (●ᶜ ∘ A))
  Σᶜ-●ᶜ = {!   !}
