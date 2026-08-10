open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Univalence using (ua; ua→; ua-gluePath)
open import Cubical.Data.Sigma

module Calf.Computation.Open where

open import Calf.Core.Abstract
open import Calf.Value
open import Calf.Value.Open as ◯ hiding (map; map-∘; join; bind) public
open import Calf.Computation
open import Calf.Computation.Power

◯ᶜ : 𝒞 → 𝒞
◯ᶜ = ⟨ ABS ⟩ ⇀_

η◦ᶜ : A ⊸ ◯ᶜ A
η◦ᶜ .U = η◦
η◦ᶜ .charge _ _ = refl

isModalᶜ : 𝒞 → 𝒱
isModalᶜ A = isModal (U A)

𝒞◦ : 𝒱₁
𝒞◦ = 𝒞WithStr isModalᶜ

𝒞◦-path : {A◦ B◦ : 𝒞◦} → ⟨ A◦ ⟩ᶜ ≡ ⟨ B◦ ⟩ᶜ → A◦ ≡ B◦
𝒞◦-path p = Σ≡Prop (λ A → isPropIsEquiv (η◦ᶜ {A} .U)) p

isModalᶜ◯ᶜ : isModalᶜ (◯ᶜ A)
isModalᶜ◯ᶜ = isModal◯

◯ᶜ◦ : 𝒞 → 𝒞◦
◯ᶜ◦ A = ◯ᶜ A , isModalᶜ◯ᶜ {A}

U◦ : 𝒞◦ → 𝒱◦
U◦ A◦ = U ⟨ A◦ ⟩ᶜ , strᶜ A◦

map : (A ⊸ B) → (◯ᶜ A ⊸ ◯ᶜ B)
map f .U = ◯.map (f .U)
map f .charge c a◦ = funExt λ abs → f .charge c (a◦ abs)

map-∘ : (f : A ⊸ B) (g : B ⊸ C) → map f ⨾ᶜ map g ≡ map (f ⨾ᶜ g)
map-∘ f g = ⊸-path refl refl (funExt (◯.map-∘ (f .U) (g .U)))

join : ◯ᶜ (◯ᶜ A) ⊸ ◯ᶜ A
join .U = ◯.join
join .charge c a◦ = refl

bind : (A ⊸ ◯ᶜ B) → (◯ᶜ A ⊸ ◯ᶜ B)
bind {B = B} k = map k ⨾ᶜ join {B}

◯ᶜ-rec : (B◦ : 𝒞◦) → (A ⊸ ⟨ B◦ ⟩ᶜ) → (◯ᶜ A ⊸ ⟨ B◦ ⟩ᶜ)
◯ᶜ-rec B◦ g .U = ◯.elim (λ _ → strᶜ B◦) (g .U)
◯ᶜ-rec {A = A} B◦ g .charge c =
  ◯.elim (λ a◦ → ◯.isModal≡ (strᶜ B◦)) λ a →
      ◯.elim-β (λ _ → strᶜ B◦) (g .U) (A .charge c a)
    ∙ g .charge c a
    ∙ cong (⟨ B◦ ⟩ᶜ .charge c) (sym (◯.elim-β (λ _ → strᶜ B◦) (g .U) a))

opaque
  ⊸-precomp-η◦ᶜ-isEquiv : {A : 𝒞} (B◦ : 𝒞◦)
    → isEquiv (λ (f : ◯ᶜ A ⊸ ⟨ B◦ ⟩ᶜ) → η◦ᶜ {A} ⨾ᶜ f)
  ⊸-precomp-η◦ᶜ-isEquiv B◦ =
    isoToIsEquiv (iso (η◦ᶜ ⨾ᶜ_) (◯ᶜ-rec B◦)
      (λ g → ⊸-path refl refl (funExt (◯.elim-β (λ _ → strᶜ B◦) (g .U))))
      (λ f → ⊸-path refl refl (sym (◯.◯-rec-unique (strᶜ B◦) refl))))

⊸-precomp-η◦ᶜ-≃ : {A : 𝒞} (B◦ : 𝒞◦) → (◯ᶜ A ⊸ ⟨ B◦ ⟩ᶜ) ≃ (A ⊸ ⟨ B◦ ⟩ᶜ)
⊸-precomp-η◦ᶜ-≃ B◦ = (η◦ᶜ ⨾ᶜ_) , ⊸-precomp-η◦ᶜ-isEquiv B◦

module _ where
  open import Calf.Computation.Pullback

  lex : ∀ {A B C} (f : A ⊸ C) (g : B ⊸ C) → ◯ᶜ (Pullback f g) ≡ Pullback (map f) (map g)
  lex {A} {B} {C} f g = conservativity fwd fwd-equiv
    where
      fwd : ◯ᶜ (Pullback f g) ⊸ Pullback (map f) (map g)
      fwd .U e =
        (λ abs → e abs .fst) , (λ abs → e abs .snd .fst) ,
        funExt (λ abs → e abs .snd .snd)
      fwd .charge c e =
        ΣPathP (refl , ΣPathP (refl , isProp→PathP (λ i → (◯ᶜ C) .is-set _ _) _ _))

      inv : U (Pullback (map f) (map g)) → U (◯ᶜ (Pullback f g))
      inv (a◦ , b◦ , p) abs = a◦ abs , b◦ abs , funExt⁻ p abs

      fwd-equiv : isEquivᶜ fwd
      fwd-equiv = isoToIsEquiv (iso (fwd .U) inv (λ _ → refl) (λ _ → refl))

ABS-◯ᶜeval : ⟨ ABS ⟩ → (A : 𝒞) → ◯ᶜ A ⊸ A
ABS-◯ᶜeval abs A .U a◦ = a◦ abs
ABS-◯ᶜeval abs A .charge c a◦ = refl

ABS-◯ᶜeval-equiv
  : (abs : ⟨ ABS ⟩) (A : 𝒞)
  → isEquivᶜ (ABS-◯ᶜeval abs A)
ABS-◯ᶜeval-equiv abs A =
  isoToIsEquiv
    (iso
      (ABS-◯ᶜeval abs A .U)
      η◦
      (λ _ → refl)
      (λ a◦ → funExt λ abs' → cong a◦ (str ABS abs abs')))

ABS-◯ᶜA≃A : ⟨ ABS ⟩ → ◯ᶜ A ≃ᶜ A
ABS-◯ᶜA≃A {A} abs = ABS-◯ᶜeval abs A , ABS-◯ᶜeval-equiv abs A

ABS-◯ᶜA≡A : ⟨ ABS ⟩ → ◯ᶜ A ≡ A
ABS-◯ᶜA≡A abs = uaᶜ (ABS-◯ᶜA≃A abs)

ABS-◯ᶜmap≡f : ∀ (abs : ⟨ ABS ⟩) (f : A ⊸ B)
  → PathP (λ i → ABS-◯ᶜA≡A {A} abs i ⊸ ABS-◯ᶜA≡A {B} abs i)
      (map f)
      f
ABS-◯ᶜmap≡f {A} {B} abs f =
  ⊸-path
    (ABS-◯ᶜA≡A {A} abs)
    (ABS-◯ᶜA≡A {B} abs)
    (ua→
      {e = ABS-◯ᶜeval abs A .U , ABS-◯ᶜeval-equiv abs A}
      {B = λ i → U (ABS-◯ᶜA≡A {B} abs i)}
      (λ a◦ →
        ua-gluePath
          (ABS-◯ᶜeval abs B .U , ABS-◯ᶜeval-equiv abs B)
          refl))

ABS-◯ᶜpoint≡a : ∀ (abs : ⟨ ABS ⟩) (a◦ : U (◯ᶜ A)) (a : U A)
  → a◦ abs ≡ a
  → PathP (λ i → U (ABS-◯ᶜA≡A {A} abs i)) a◦ a
ABS-◯ᶜpoint≡a {A} abs a◦ a p =
  ua-gluePath
    (ABS-◯ᶜeval abs A .U , ABS-◯ᶜeval-equiv abs A)
    p

module _ where
  open import Calf.Computation.Copower

  private
    embed : ∀ {X A} → Σᶜ X A .U → Σᶜ X (◯ᶜ ∘ A) .U
    embed (x , a) = x , η◦ a

  Σᶜ-◯ᶜ-fwd : ∀ {X A} → ◯ᶜ (Σᶜ X A) ⊸ ◯ᶜ (Σᶜ X (◯ᶜ ∘ A))
  Σᶜ-◯ᶜ-fwd {X} {A} .U = ◯.map (embed {X} {A})
  Σᶜ-◯ᶜ-fwd .charge _ _ = refl

  Σᶜ-◯ᶜ-fwd-equiv : ∀ {X A} → isEquivᶜ (Σᶜ-◯ᶜ-fwd {X} {A})
  Σᶜ-◯ᶜ-fwd-equiv {X} {A} =
    subst isEquiv (funExt⁻ ◯.map′≡map (embed {X} {A})) (invEquiv ○Σ○≃○Σ .snd)

  Σᶜ-◯ᶜ : ∀ {X A} → ◯ᶜ (Σᶜ X A) ≡ ◯ᶜ (Σᶜ X (◯ᶜ ∘ A))
  Σᶜ-◯ᶜ {X} {A} =
    conservativity (Σᶜ-◯ᶜ-fwd {X} {A}) (Σᶜ-◯ᶜ-fwd-equiv {X} {A})
