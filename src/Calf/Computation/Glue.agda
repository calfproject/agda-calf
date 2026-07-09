open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence using (ua; ua→; ua-gluePath)
open import Cubical.Functions.Embedding

module Calf.Computation.Glue where

open import Calf.Core.Cost
open import Calf.Computation
open import Calf.Value
import Calf.Value.Closed as ●
import Calf.Value.Open as ◯
open import Calf.Value.Glue public
open import Calf.Computation.Open as ◯ᶜ
open import Calf.Computation.Closed as ●ᶜ

Glueᶜ : (A• : 𝒞•) (A◦ : 𝒞◦) (α• : ⟨ A• ⟩ᶜ ⊸ ●ᶜ ⟨ A◦ ⟩ᶜ) → 𝒞
Glueᶜ A• A◦ α• .U = Glue (U• A•) (U◦ A◦) (α• .U)
Glueᶜ A• A◦ α• .is-set = isSetGlue (⟨ A• ⟩ᶜ .is-set) (⟨ A◦ ⟩ᶜ .is-set)
Glueᶜ A• A◦ α• .charge c a .• = ⟨ A• ⟩ᶜ .charge c (a .•)
Glueᶜ A• A◦ α• .charge c a .◦ = ⟨ A◦ ⟩ᶜ .charge c (a .◦)
Glueᶜ A• A◦ α• .charge c a .•→◦ = α• .charge c (a .•) ∙ cong (●ᶜ ⟨ A◦ ⟩ᶜ .charge c) (a .•→◦)
Glueᶜ A• A◦ α• .charge/0 i .• = ⟨ A• ⟩ᶜ .charge/0 i
Glueᶜ A• A◦ α• .charge/0 i .◦ = ⟨ A◦ ⟩ᶜ .charge/0 i
Glueᶜ A• A◦ α• .charge/0 {a} i .•→◦ =
  isProp→PathP
    (λ i → ●ᶜ ⟨ A◦ ⟩ᶜ .is-set
      (α• .U (⟨ A• ⟩ᶜ .charge/0 {a .•} i))
      (η• (⟨ A◦ ⟩ᶜ .charge/0 {a .◦} i)))
    (α• .charge 0ℂ (a .•) ∙ cong (●ᶜ ⟨ A◦ ⟩ᶜ .charge 0ℂ) (a .•→◦))
    (a .•→◦)
    i
Glueᶜ A• A◦ α• .charge/+ i .• = ⟨ A• ⟩ᶜ .charge/+ i
Glueᶜ A• A◦ α• .charge/+ i .◦ = ⟨ A◦ ⟩ᶜ .charge/+ i
Glueᶜ A• A◦ α• .charge/+ {a} {c₁} {c₂} i .•→◦ =
  isProp→PathP
    (λ i → ●ᶜ ⟨ A◦ ⟩ᶜ .is-set
      (α• .U (⟨ A• ⟩ᶜ .charge/+ {a .•} {c₁} {c₂} i))
      (η• (⟨ A◦ ⟩ᶜ .charge/+ {a .◦} {c₁} {c₂} i)))
    (α• .charge (c₁ +ℂ c₂) (a .•) ∙ cong (●ᶜ ⟨ A◦ ⟩ᶜ .charge (c₁ +ℂ c₂)) (a .•→◦))
    (α• .charge c₁ (⟨ A• ⟩ᶜ .charge c₂ (a .•))
      ∙ cong (●ᶜ ⟨ A◦ ⟩ᶜ .charge c₁)
        (α• .charge c₂ (a .•) ∙ cong (●ᶜ ⟨ A◦ ⟩ᶜ .charge c₂) (a .•→◦)))
    i

record 𝒞-FRAC : Type₁ where
  field
    A• : 𝒞•
    A◦ : 𝒞◦
    α• : ⟨ A• ⟩ᶜ ⊸ ●ᶜ ⟨ A◦ ⟩ᶜ
open 𝒞-FRAC

𝒞-FRAC-path
  : {F G : 𝒞-FRAC}
  → (A•-path : F .A• ≡ G .A•)
  → (A◦-path : F .A◦ ≡ G .A◦)
  → PathP
      (λ i → A•-path i .fst ⊸ ●ᶜ (A◦-path i .fst))
      (F .α•)
      (G .α•)
  → F ≡ G
𝒞-FRAC-path A•-path A◦-path α•-path i .A• = A•-path i
𝒞-FRAC-path A•-path A◦-path α•-path i .A◦ = A◦-path i
𝒞-FRAC-path A•-path A◦-path α•-path i .α• = α•-path i

𝒞-FRAC→𝒱-FRAC : 𝒞-FRAC → 𝒱-FRAC
𝒞-FRAC→𝒱-FRAC F =
  record
    { X• = U• (F .A•)
    ; X◦ = U◦ (F .A◦)
    ; χ• = F .α• .U
    }

𝒞-toFRAC : 𝒞 → 𝒞-FRAC
𝒞-toFRAC A .A• = ●ᶜ A , ●ᶜ.η-isEquiv
𝒞-toFRAC A .A◦ = ◯ᶜ A , ◯ᶜ.η-isEquiv
𝒞-toFRAC A .α• = ●ᶜ.map η◦ᶜ

𝒞-fromFRAC : 𝒞-FRAC → 𝒞
𝒞-fromFRAC F = Glueᶜ (F .A•) (F .A◦) (F .α•)

proj•ᶜ : (F : 𝒞-FRAC) → 𝒞-fromFRAC F ⊸ ⟨ F .A• ⟩ᶜ
proj•ᶜ F .U g = g .•
proj•ᶜ F .charge c g = refl

proj◦ᶜ : (F : 𝒞-FRAC) → 𝒞-fromFRAC F ⊸ ⟨ F .A◦ ⟩ᶜ
proj◦ᶜ F .U g = g .◦
proj◦ᶜ F .charge c g = refl

glue•-out-charge
  : (F : 𝒞-FRAC) (c : ℂ) (g• : U (●ᶜ (𝒞-fromFRAC F)))
  → glue•-out (𝒞-FRAC→𝒱-FRAC F) (●ᶜ (𝒞-fromFRAC F) .charge c g•)
    ≡ ⟨ F .A• ⟩ᶜ .charge c
      (glue•-out (𝒞-FRAC→𝒱-FRAC F) g•)
glue•-out-charge F c g• =
  isEmbedding→Inj (isEquiv→isEmbedding (F .A• .snd))
    (glue•-out (𝒞-FRAC→𝒱-FRAC F) (●ᶜ (𝒞-fromFRAC F) .charge c g•))
    (⟨ F .A• ⟩ᶜ .charge c
      (glue•-out (𝒞-FRAC→𝒱-FRAC F) g•))
    (secIsEq (F .A• .snd) (●ᶜ.map (proj•ᶜ F) .U (●ᶜ (𝒞-fromFRAC F) .charge c g•))
      ∙ ●ᶜ.map (proj•ᶜ F) .charge c g•
      ∙ cong (●ᶜ (⟨ F .A• ⟩ᶜ) .charge c)
        (sym (secIsEq (F .A• .snd) (●ᶜ.map (proj•ᶜ F) .U g•))))

glue◦-out-charge
  : (F : 𝒞-FRAC) (c : ℂ) (g◦ : U (◯ᶜ (𝒞-fromFRAC F)))
  → glue◦-out (𝒞-FRAC→𝒱-FRAC F) (◯ᶜ (𝒞-fromFRAC F) .charge c g◦)
    ≡ ⟨ F .A◦ ⟩ᶜ .charge c
      (glue◦-out (𝒞-FRAC→𝒱-FRAC F) g◦)
glue◦-out-charge F c g◦ =
  isEmbedding→Inj (isEquiv→isEmbedding (F .A◦ .snd))
    (glue◦-out (𝒞-FRAC→𝒱-FRAC F) (◯ᶜ (𝒞-fromFRAC F) .charge c g◦))
    (⟨ F .A◦ ⟩ᶜ .charge c
      (glue◦-out (𝒞-FRAC→𝒱-FRAC F) g◦))
    (secIsEq (F .A◦ .snd) (λ p → ⟨ F .A◦ ⟩ᶜ .charge c (g◦ p .◦))
      ∙ funExt (λ p →
        cong (⟨ F .A◦ ⟩ᶜ .charge c)
          (sym (funExt⁻ (secIsEq (F .A◦ .snd) (λ p → g◦ p .◦)) p))))

𝒞-glue•-path : (F : 𝒞-FRAC) →
  (●ᶜ (𝒞-fromFRAC F) , ●ᶜ.η-isEquiv) ≡ F .A•
𝒞-glue•-path F =
  𝒞•-path
    (𝒞-path
      (cong fst (glue•-path (𝒞-FRAC→𝒱-FRAC F)))
      (charge-path
        (glue•-equiv (𝒞-FRAC→𝒱-FRAC F))
        (●ᶜ (𝒞-fromFRAC F) .charge)
        (⟨ F .A• ⟩ᶜ .charge)
        (glue•-out-charge F)))

𝒞-glue◦-path : (F : 𝒞-FRAC) →
  (◯ᶜ (𝒞-fromFRAC F) , ◯ᶜ.η-isEquiv) ≡ F .A◦
𝒞-glue◦-path F =
  𝒞◦-path
    (𝒞-path
      (cong fst (glue◦-path (𝒞-FRAC→𝒱-FRAC F)))
      (charge-path
        (glue◦-equiv (𝒞-FRAC→𝒱-FRAC F))
        (◯ᶜ (𝒞-fromFRAC F) .charge)
        (⟨ F .A◦ ⟩ᶜ .charge)
        (glue◦-out-charge F)))

𝒞-glue-fracture-section : section 𝒞-toFRAC 𝒞-fromFRAC
𝒞-glue-fracture-section F i .A• = 𝒞-glue•-path F i
𝒞-glue-fracture-section F i .A◦ = 𝒞-glue◦-path F i
𝒞-glue-fracture-section F i .α• =
  ⊸-path
    (λ i → 𝒞-glue•-path F i .fst)
    (λ i → ●ᶜ (𝒞-glue◦-path F i .fst))
    {f₀ = ●ᶜ.map η◦ᶜ}
    {f₁ = F .α•}
    (λ i → 𝒱-FRAC.χ• (glue-fracture-section (𝒞-FRAC→𝒱-FRAC F) i))
    i

𝒞-fracture : A ⊸ 𝒞-fromFRAC (𝒞-toFRAC A)
𝒞-fracture .U = fracture
𝒞-fracture {A} .charge c a i .• = η• (A .charge c a)
𝒞-fracture {A} .charge c a i .◦ = η◦ (A .charge c a)
𝒞-fracture {A} .charge c a i .•→◦ =
  isProp→PathP
    (λ i → ●ᶜ (◯ᶜ A) .is-set
      (𝒞-fromFRAC (𝒞-toFRAC A) .charge c (fracture a) .•→◦ i0)
      (η• (η◦ (A .charge c a))))
    refl
    (𝒞-fromFRAC (𝒞-toFRAC A) .charge c (fracture a) .•→◦)
    i

𝒞-glue-fracture-retract : retract 𝒞-toFRAC 𝒞-fromFRAC
𝒞-glue-fracture-retract A = sym (conservativity 𝒞-fracture fracture-isEquiv)

𝒞-fracture-and-gluing : 𝒞 ≃ 𝒞-FRAC
𝒞-fracture-and-gluing .fst = 𝒞-toFRAC
𝒞-fracture-and-gluing .snd =
  isoToIsEquiv
    (iso
      𝒞-toFRAC
      𝒞-fromFRAC
      𝒞-glue-fracture-section
      𝒞-glue-fracture-retract)

record 𝒞-Square (A B : 𝒞-FRAC) : 𝒱 where
  field
    f• : ⟨ A .A• ⟩ᶜ ⊸ ⟨ B .A• ⟩ᶜ
    f◦ : ⟨ A .A◦ ⟩ᶜ ⊸ ⟨ B .A◦ ⟩ᶜ
    f□ : (a• : U ⟨ A .A• ⟩ᶜ) → B .α• .U (f• .U a•) ≡ ●ᶜ.map f◦ .U (A .α• .U a•)

𝒞-fracture-and-gluing-square : (A ⊸ B) ≡ 𝒞-Square (𝒞-toFRAC A) (𝒞-toFRAC B)
𝒞-fracture-and-gluing-square = {!   !}

squareᶜ
  : ∀ {A• A◦ α B• B◦ β}
  → (f• : ⟨ A• ⟩ᶜ ⊸ B• .fst)
  → (f◦ : ⟨ A◦ ⟩ᶜ ⊸ B◦ .fst)
  → f• ⨾ᶜ β ≡ α ⨾ᶜ ●ᶜ.map f◦
  → Glueᶜ A• A◦ α ⊸ Glueᶜ B• B◦ β
squareᶜ f• f◦ f-coherence .U q =
  square
    (f• .U)
    (f◦ .U)
    (λ a• → cong ((_$ a•) ∘ U) f-coherence)
    q
squareᶜ f• f◦ f-coherence .charge c q i .• =
  f• .charge c (q .•) i
squareᶜ f• f◦ f-coherence .charge c q i .◦ =
  f◦ .charge c (q .◦) i
squareᶜ {A• = A•} {A◦ = A◦} {α = α} {B• = B•} {B◦ = B◦} {β = β} f• f◦ f-coherence .charge c q i .•→◦ =
  isProp→PathP
    (λ i → ●ᶜ (B◦ .fst) .is-set
      (β .U (f• .charge c (q .•) i))
      (η• (f◦ .charge c (q .◦) i)))
    (squareᶜ
      {A• = A•} {A◦ = A◦} {α = α}
      {B• = B•} {B◦ = B◦} {β = β}
      f• f◦ f-coherence .U (Glueᶜ A• A◦ α .charge c q) .•→◦)
    (Glueᶜ B• B◦ β .charge c
      (squareᶜ
        {A• = A•} {A◦ = A◦} {α = α}
        {B• = B•} {B◦ = B◦} {β = β}
        f• f◦ f-coherence .U q)
      .•→◦)
    i

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
    (λ i → ●ᶜ (◯ᶜ B) .is-set
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
    (λ i → ●ᶜ (◯ᶜ B) .is-set
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
