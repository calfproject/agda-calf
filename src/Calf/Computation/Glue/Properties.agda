module Calf.Computation.Glue.Properties where

open import Calf.Core.Cost
open import Calf.Value
import Calf.Value.Open as ◯
import Calf.Value.Closed as ●
open import Calf.Value.Glue public
open import Calf.Computation
open import Calf.Computation.Open as ◯ᶜ
open import Calf.Computation.Closed as ●ᶜ
open import Cubical.Foundations.Univalence using (ua→; ua-gluePath)

open import Calf.Computation.Glue.Base
open import Calf.Computation.Glue.Fracture
open 𝒞-FRAC

fracture-map
  : (f : A ⊸ B)
  → 𝒞-fromFRAC (𝒞-toFRAC A) ⊸ 𝒞-fromFRAC (𝒞-toFRAC B)
fracture-map {A} {B} f .U q .• =
  ●ᶜ.map f .U (q .•)
fracture-map {A} {B} f .U q .◦ =
  ◯.map (f .U) (q .◦)
fracture-map {A} {B} f .U q .•→◦ =
    ●.map (η◦ᶜ {A = B} .U) (●ᶜ.map f .U (q .•))
  ≡⟨ ●.map-∘ (f .U) (η◦ᶜ {A = B} .U) (q .•) ⟩
    ●.map (λ a → η◦ᶜ {A = B} .U (f .U a)) (q .•)
  ≡⟨ sym (●.map-∘ (η◦ᶜ {A = A} .U) (◯.map (f .U)) (q .•)) ⟩
    ●.map (◯.map (f .U)) (●.map (η◦ᶜ {A = A} .U) (q .•))
  ≡⟨ cong (●.map (◯.map (f .U))) (q .•→◦) ⟩
    η• (◯.map (f .U) (q .◦))
  ∎
fracture-map {A} {B} f .charge c q i .• =
  ●ᶜ.map f .charge c (q .•) i
fracture-map {A} {B} f .charge c q i .◦ p =
  f .charge c (q .◦ p) i
fracture-map {A} {B} f .charge c q i .•→◦ =
  isProp→PathP
    (λ i → is-set (●ᶜ (◯ᶜ B))
      (●ᶜ.map (η◦ᶜ {A = B}) .U (●ᶜ.map f .charge c (q .•) i))
      (η• (λ p → f .charge c (q .◦ p) i)))
    (fracture-map {A} {B} f .U (𝒞-fromFRAC (𝒞-toFRAC A) .charge c q) .•→◦)
    (𝒞-fromFRAC (𝒞-toFRAC B) .charge c (fracture-map f .U q) .•→◦)
    i

fracture-map-coh
  : (f : A ⊸ B)
  → (q• : U (●ᶜ A))
  → (q◦ : U (◯ᶜ A))
  → (qcoh : ●ᶜ.map (η◦ᶜ {A = A}) .U q• ≡ η• q◦)
  → ●.map (η◦ᶜ {A = B} .U) (●ᶜ.map f .U q•)
    ≡ η• (◯.map (f .U) q◦)
fracture-map-coh f q• q◦ qcoh =
  fracture-map f .U
    (record { • = q• ; ◦ = q◦ ; •→◦ = qcoh })
    .•→◦

fracture-map-fracture
  : (f : A ⊸ B) (a : U A)
  → fracture-map f .U (fracture {X = U A} a) ≡ fracture {X = U B} (f .U a)
fracture-map-fracture {A} {B} f a i .• = η• (f .U a)
fracture-map-fracture {A} {B} f a i .◦ = η◦ᶜ {A = B} .U (f .U a)
fracture-map-fracture {A} {B} f a i .•→◦ =
  isProp→PathP
    (λ i → is-set (●ᶜ (◯ᶜ B))
      (η• (η◦ᶜ {A = B} .U (f .U a)))
      (η• (η◦ᶜ {A = B} .U (f .U a))))
    (fracture-map f .U (fracture {X = U A} a) .•→◦)
    refl
    i

fracture-map-same
  : (f : A ⊸ B)
  → PathP
      (λ i → 𝒞-glue-fracture-retract A i ⊸ 𝒞-glue-fracture-retract B i)
      (fracture-map f)
      f
fracture-map-same {A} {B} f =
  ⊸-path
    (𝒞-glue-fracture-retract A)
    (𝒞-glue-fracture-retract B)
    (λ i →
      ua→
        {e = 𝒞-fracture {A = A} .U , fracture-isEquiv}
        {B = λ i → U (conservativity (𝒞-fracture {A = B}) fracture-isEquiv i)}
        {f₀ = f .U}
        {f₁ = fracture-map f .U}
        (λ a →
          ua-gluePath
            (𝒞-fracture {A = B} .U , fracture-isEquiv)
            (sym (fracture-map-fracture f a)))
        (~ i))

𝒞-fracture-≡
  : {A B : 𝒞}
  → (p• : ●ᶜ A ≡ ●ᶜ B)
  → (p◦ : ◯ᶜ A ≡ ◯ᶜ B)
  → PathP (λ i → p• i ⊸ ●ᶜ (p◦ i)) (●ᶜ.map (η◦ᶜ {A = A})) (●ᶜ.map (η◦ᶜ {A = B}))
  → A ≡ B
𝒞-fracture-≡ {A} {B} p• p◦ pα =
    sym (𝒞-glue-fracture-retract A)
  ∙ cong 𝒞-fromFRAC (𝒞-FRAC-path (●ᶜ.𝒞•-path p•) (◯ᶜ.𝒞◦-path p◦) pα)
  ∙ 𝒞-glue-fracture-retract B
