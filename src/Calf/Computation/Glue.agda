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
Glueᶜ A• A◦ α• .charge/0 {a} i .• = ⟨ A• ⟩ᶜ .charge/0 {a .•} i
Glueᶜ A• A◦ α• .charge/0 {a} i .◦ = ⟨ A◦ ⟩ᶜ .charge/0 {a .◦} i
Glueᶜ A• A◦ α• .charge/0 {a} i .•→◦ =
  isProp→PathP
    (λ i → ●ᶜ ⟨ A◦ ⟩ᶜ .is-set
      (α• .U (⟨ A• ⟩ᶜ .charge/0 {a .•} i))
      (η• (⟨ A◦ ⟩ᶜ .charge/0 {a .◦} i)))
    (α• .charge 0ℂ (a .•) ∙ cong (●ᶜ ⟨ A◦ ⟩ᶜ .charge 0ℂ) (a .•→◦))
    (a .•→◦)
    i
Glueᶜ A• A◦ α• .charge/+ {a} {c₁} {c₂} i .• =
  ⟨ A• ⟩ᶜ .charge/+ {a .•} {c₁} {c₂} i
Glueᶜ A• A◦ α• .charge/+ {a} {c₁} {c₂} i .◦ =
  ⟨ A◦ ⟩ᶜ .charge/+ {a .◦} {c₁} {c₂} i
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

𝒞-FRAC→FRAC : 𝒞-FRAC → FRAC
𝒞-FRAC→FRAC F =
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
  → glue•-out (𝒞-FRAC→FRAC F) (●ᶜ (𝒞-fromFRAC F) .charge c g•)
    ≡ ⟨ F .A• ⟩ᶜ .charge c
      (glue•-out (𝒞-FRAC→FRAC F) g•)
glue•-out-charge F c g• =
  isEmbedding→Inj (isEquiv→isEmbedding (F .A• .snd))
    (glue•-out (𝒞-FRAC→FRAC F) (●ᶜ (𝒞-fromFRAC F) .charge c g•))
    (⟨ F .A• ⟩ᶜ .charge c
      (glue•-out (𝒞-FRAC→FRAC F) g•))
    (secIsEq (F .A• .snd) (●ᶜ.map (proj•ᶜ F) .U (●ᶜ (𝒞-fromFRAC F) .charge c g•))
      ∙ ●ᶜ.map (proj•ᶜ F) .charge c g•
      ∙ cong (●ᶜ (⟨ F .A• ⟩ᶜ) .charge c)
        (sym (secIsEq (F .A• .snd) (●ᶜ.map (proj•ᶜ F) .U g•))))

glue◦-out-charge
  : (F : 𝒞-FRAC) (c : ℂ) (g◦ : U (◯ᶜ (𝒞-fromFRAC F)))
  → glue◦-out (𝒞-FRAC→FRAC F) (◯ᶜ (𝒞-fromFRAC F) .charge c g◦)
    ≡ ⟨ F .A◦ ⟩ᶜ .charge c
      (glue◦-out (𝒞-FRAC→FRAC F) g◦)
glue◦-out-charge F c g◦ =
  isEmbedding→Inj (isEquiv→isEmbedding (F .A◦ .snd))
    (glue◦-out (𝒞-FRAC→FRAC F) (◯ᶜ (𝒞-fromFRAC F) .charge c g◦))
    (⟨ F .A◦ ⟩ᶜ .charge c
      (glue◦-out (𝒞-FRAC→FRAC F) g◦))
    (secIsEq (F .A◦ .snd) (λ p → ⟨ F .A◦ ⟩ᶜ .charge c (g◦ p .◦))
      ∙ funExt (λ p →
        cong (⟨ F .A◦ ⟩ᶜ .charge c)
          (sym (funExt⁻ (secIsEq (F .A◦ .snd) (λ p → g◦ p .◦)) p))))

𝒞-glue•-path : (F : 𝒞-FRAC) →
  (●ᶜ (𝒞-fromFRAC F) , ●ᶜ.η-isEquiv) ≡ F .A•
𝒞-glue•-path F =
  𝒞•-path
    (𝒞-path
      (cong fst (glue•-path (𝒞-FRAC→FRAC F)))
      (charge-path
        (glue•-equiv (𝒞-FRAC→FRAC F))
        (●ᶜ (𝒞-fromFRAC F) .charge)
        (⟨ F .A• ⟩ᶜ .charge)
        (glue•-out-charge F)))

𝒞-glue◦-path : (F : 𝒞-FRAC) →
  (◯ᶜ (𝒞-fromFRAC F) , ◯ᶜ.η-isEquiv) ≡ F .A◦
𝒞-glue◦-path F =
  𝒞◦-path
    (𝒞-path
      (cong fst (glue◦-path (𝒞-FRAC→FRAC F)))
      (charge-path
        (glue◦-equiv (𝒞-FRAC→FRAC F))
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
    (λ i → FRAC.χ• (glue-fracture-section (𝒞-FRAC→FRAC F) i))
    i

𝒞-fracture-equiv : (A : 𝒞) → U A ≃ U (𝒞-fromFRAC (𝒞-toFRAC A))
𝒞-fracture-equiv A = fracture , fracture-isEquiv

fracture-charge
  : (A : 𝒞) (c : ℂ) (a : U A)
  → 𝒞-fromFRAC (𝒞-toFRAC A) .charge c (fracture {X = U A} a)
    ≡ fracture {X = U A} (A .charge c a)
fracture-charge A c a i .• = η• (A .charge c a)
fracture-charge A c a i .◦ = η◦ (A .charge c a)
fracture-charge A c a i .•→◦ =
  isProp→PathP
    (λ i → ●ᶜ (◯ᶜ A) .is-set
      (𝒞-fromFRAC (𝒞-toFRAC A) .charge c (fracture a) .•→◦ i0)
      (η• (η◦ (A .charge c a))))
    (𝒞-fromFRAC (𝒞-toFRAC A) .charge c (fracture a) .•→◦)
    refl
    i

fracture-inv-charge
  : (A : 𝒞) (c : ℂ) (g : U (𝒞-fromFRAC (𝒞-toFRAC A)))
  → invEq (𝒞-fracture-equiv A) (𝒞-fromFRAC (𝒞-toFRAC A) .charge c g)
    ≡ A .charge c (invEq (𝒞-fracture-equiv A) g)
fracture-inv-charge A c g =
  isEmbedding→Inj (isEquiv→isEmbedding (𝒞-fracture-equiv A .snd))
    (invEq (𝒞-fracture-equiv A) (𝒞-fromFRAC (𝒞-toFRAC A) .charge c g))
    (A .charge c (invEq (𝒞-fracture-equiv A) g))
    (secEq (𝒞-fracture-equiv A) (𝒞-fromFRAC (𝒞-toFRAC A) .charge c g)
      ∙ sym (cong (𝒞-fromFRAC (𝒞-toFRAC A) .charge c) (secEq (𝒞-fracture-equiv A) g))
      ∙ fracture-charge A c (invEq (𝒞-fracture-equiv A) g))

𝒞-glue-fracture-retract-U-path
  : (A : 𝒞) → U (𝒞-fromFRAC (𝒞-toFRAC A)) ≡ U A
𝒞-glue-fracture-retract-U-path A =
  ua (invEquiv (𝒞-fracture-equiv A))

𝒞-glue-fracture-retract-charge
  : (A : 𝒞)
  → PathP
      (λ i →
        ℂ
        → (𝒞-glue-fracture-retract-U-path A i)
        → (𝒞-glue-fracture-retract-U-path A i))
      (𝒞-fromFRAC (𝒞-toFRAC A) .charge)
      (A .charge)
𝒞-glue-fracture-retract-charge A =
  charge-path-inv
    (𝒞-fracture-equiv A)
    (A .charge)
    (𝒞-fromFRAC (𝒞-toFRAC A) .charge)
    (fracture-inv-charge A)

𝒞-glue-fracture-retract : retract 𝒞-toFRAC 𝒞-fromFRAC
𝒞-glue-fracture-retract A =
  𝒞-path
    (𝒞-glue-fracture-retract-U-path A)
    (𝒞-glue-fracture-retract-charge A)

𝒞-fracture-and-gluing : 𝒞 ≃ 𝒞-FRAC
𝒞-fracture-and-gluing .fst = 𝒞-toFRAC
𝒞-fracture-and-gluing .snd =
  isoToIsEquiv
    (iso
      𝒞-toFRAC
      𝒞-fromFRAC
      𝒞-glue-fracture-section
      𝒞-glue-fracture-retract)

squareᶜ
  : ∀ {A• A◦ α B• B◦ β}
  → (f• : ⟨ A• ⟩ᶜ ⊸ B• .fst)
  → (f◦ : ⟨ A◦ ⟩ᶜ ⊸ B◦ .fst)
  → f• ⨾ᶜ β ≡ α ⨾ᶜ ●ᶜ.map f◦
  → Glueᶜ A• A◦ α ⊸ Glueᶜ B• B◦ β
squareᶜ {A• = A•} {A◦ = A◦} {α = α} {B• = B•} {B◦ = B◦} {β = β} f• f◦ f-coherence .U q =
  square
    {X• = U• A•}
    {X◦ = U◦ A◦}
    {χ = α .U}
    {Y• = U• B•}
    {Y◦ = U◦ B◦}
    {ψ = β .U}
    (f• .U)
    (f◦ .U)
    (λ a• → cong ((_$ a•) ∘ U) f-coherence)
    q
squareᶜ {A• = A•} {A◦ = A◦} {α = α} {B• = B•} {B◦ = B◦} {β = β} f• f◦ f-coherence .charge c q i .• =
  f• .charge c (q .•) i
squareᶜ {A• = A•} {A◦ = A◦} {α = α} {B• = B•} {B◦ = B◦} {β = β} f• f◦ f-coherence .charge c q i .◦ =
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

opaque
  Glueᶜ' : (A-⊤ A-abs : 𝒞) → (A-⊤ ⊸ A-abs) → 𝒞
  Glueᶜ' A-⊤ A-abs α =
    Glueᶜ
      (●ᶜ A-⊤ , ●ᶜ.η-isEquiv {X = U A-⊤})
      (◯ᶜ A-abs , ◯ᶜ.η-isEquiv {X = U A-abs})
      (●ᶜ.map (α ⨾ᶜ η◦ᶜ {A = A-abs}))

Glueᶜ'-FRAC : (A-⊤ A-abs : 𝒞) → (A-⊤ ⊸ A-abs) → 𝒞-FRAC
Glueᶜ'-FRAC A-⊤ A-abs α .A• =
  ●ᶜ A-⊤ , ●ᶜ.η-isEquiv {X = U A-⊤}
Glueᶜ'-FRAC A-⊤ A-abs α .A◦ =
  ◯ᶜ A-abs , ◯ᶜ.η-isEquiv {X = U A-abs}
Glueᶜ'-FRAC A-⊤ A-abs α .α• =
  ●ᶜ.map (α ⨾ᶜ η◦ᶜ {A = A-abs})

opaque
  unfolding Glueᶜ'

  Glueᶜ'-id-fracture : {A : 𝒞} → Glueᶜ' A A (idᶜ {A = A}) ≡ 𝒞-fromFRAC (𝒞-toFRAC A)
  Glueᶜ'-id-fracture {A} =
    𝒞-path refl λ i c q →
      record
        { • = ●ᶜ A .charge c (q .•)
        ; ◦ = ◯ᶜ A .charge c (q .◦)
        ; •→◦ =
            isProp→PathP
              (λ i → ●ᶜ (◯ᶜ A) .is-set
                (●ᶜ.map (η◦ᶜ {A = A}) .U (●ᶜ A .charge c (q .•)))
                (η• (◯ᶜ A .charge c (q .◦))))
              (Glueᶜ' A A (idᶜ {A = A}) .charge c q .•→◦)
              (𝒞-fromFRAC (𝒞-toFRAC A) .charge c q .•→◦)
              i
        }

  Glueᶜ'-id : {A : 𝒞} → Glueᶜ' A A (idᶜ {A = A}) ≡ A
  Glueᶜ'-id {A} =
    Glueᶜ'-id-fracture {A = A} ∙ 𝒞-glue-fracture-retract A

  squareᶜ' : ∀ {A-⊤ A-abs α B-⊤ B-abs β} (f-⊤ : A-⊤ ⊸ B-⊤) (f-abs : A-abs ⊸ B-abs)
    → ((a-⊤ : U A-⊤) → U β (U f-⊤ a-⊤) ≡ U f-abs (U α a-⊤))
    → Glueᶜ' A-⊤ A-abs α ⊸ Glueᶜ' B-⊤ B-abs β
  squareᶜ' {A-abs = A-abs} {α = α} {B-abs = B-abs} {β = β} f-⊤ f-abs f-coherence .U q .• =
    ●ᶜ.map f-⊤ .U (q .•)
  squareᶜ' {A-abs = A-abs} {α = α} {B-abs = B-abs} {β = β} f-⊤ f-abs f-coherence .U q .◦ =
    ◯.map (f-abs .U) (q .◦)
  squareᶜ' {A-abs = A-abs} {α = α} {B-abs = B-abs} {β = β} f-⊤ f-abs f-coherence .U q .•→◦ =
      ●.map (η◦ᶜ {A = B-abs} .U ∘ β .U) (●ᶜ.map f-⊤ .U (q .•))
    ≡⟨ ●.map-∘ (f-⊤ .U) (η◦ᶜ {A = B-abs} .U ∘ β .U) (q .•) ⟩
      ●.map (λ a → η◦ᶜ {A = B-abs} .U (β .U (f-⊤ .U a))) (q .•)
    ≡⟨ cong (λ f → ●.map f (q .•)) (funExt λ a → cong (η◦ᶜ {A = B-abs} .U) (f-coherence a)) ⟩
      ●.map (λ a → η◦ᶜ {A = B-abs} .U (f-abs .U (α .U a))) (q .•)
    ≡⟨ sym (●.map-∘ (η◦ᶜ {A = A-abs} .U ∘ α .U) (◯.map (f-abs .U)) (q .•)) ⟩
      ●.map (◯.map (f-abs .U)) (●.map (η◦ᶜ {A = A-abs} .U ∘ α .U) (q .•))
    ≡⟨ cong (●.map (◯.map (f-abs .U))) (q .•→◦) ⟩
      ●.map (◯.map (f-abs .U)) (η• (q .◦))
    ≡⟨ refl ⟩
      η• (◯.map (f-abs .U) (q .◦))
    ∎
  squareᶜ' {A-abs = A-abs} {α = α} {B-abs = B-abs} {β = β} f-⊤ f-abs f-coherence .charge c q i .• =
    ●ᶜ.map f-⊤ .charge c (q .•) i
  squareᶜ' {A-abs = A-abs} {α = α} {B-abs = B-abs} {β = β} f-⊤ f-abs f-coherence .charge c q i .◦ p =
    f-abs .charge c (q .◦ p) i
  squareᶜ' {A-⊤ = A-⊤} {A-abs = A-abs} {α = α} {B-⊤ = B-⊤} {B-abs = B-abs} {β = β} f-⊤ f-abs f-coherence .charge c q i .•→◦ =
    isProp→PathP
      (λ i → ●ᶜ (◯ᶜ B-abs) .is-set
        (●ᶜ.map (β ⨾ᶜ η◦ᶜ {A = B-abs}) .U (●ᶜ.map f-⊤ .charge c (q .•) i))
        (η• (λ p → f-abs .charge c (q .◦ p) i)))
      (squareᶜ' {A-⊤ = A-⊤} {A-abs = A-abs} {α = α} {B-⊤ = B-⊤} {B-abs = B-abs} {β = β}
        f-⊤ f-abs f-coherence .U (Glueᶜ' A-⊤ A-abs α .charge c q) .•→◦)
      (Glueᶜ' B-⊤ B-abs β .charge c
        (squareᶜ' {A-⊤ = A-⊤} {A-abs = A-abs} {α = α} {B-⊤ = B-⊤} {B-abs = B-abs} {β = β}
          f-⊤ f-abs f-coherence .U q) .•→◦)
      i

  ●ᶜ-map-CHARGE
    : (c : ℂ) (a• : U (●ᶜ A))
    → ●ᶜ.map (CHARGE {A = A} c) .U a• ≡ ●ᶜ A .charge c a•
  ●ᶜ-map-CHARGE c (η• a) = refl
  ●ᶜ-map-CHARGE c (∗ p) = refl
  ●ᶜ-map-CHARGE {A = A} c (law a p i) =
    isProp→PathP
      (λ i → ●ᶜ A .is-set
        (●ᶜ.map (CHARGE {A = A} c) .U (law a p i))
        (●ᶜ A .charge c (law a p i)))
      refl
      refl
      i

  squareᶜ'-charge
    : ∀ {A-⊤ A-abs α c}
    → (α-charge : (a : U A-⊤) → α .U (A-⊤ .charge c a) ≡ A-abs .charge c (α .U a))
    → squareᶜ'
        {A-⊤ = A-⊤} {A-abs = A-abs} {α = α}
        {B-⊤ = A-⊤} {B-abs = A-abs} {β = α}
        (CHARGE c) (CHARGE c)
        α-charge
      ≡ CHARGE {A = Glueᶜ' A-⊤ A-abs α} c
  squareᶜ'-charge {A-⊤} {A-abs} {α} {c} α-charge =
    ⊸-path
      {A₀ = Glueᶜ' A-⊤ A-abs α}
      {A₁ = Glueᶜ' A-⊤ A-abs α}
      {B₀ = Glueᶜ' A-⊤ A-abs α}
      {B₁ = Glueᶜ' A-⊤ A-abs α}
      refl refl
      (funExt λ q → λ i → record
        { • = ●ᶜ-map-CHARGE {A = A-⊤} c (q .•) i
        ; ◦ = λ p → A-abs .charge c (q .◦ p)
        ; •→◦ =
            isProp→PathP
              (λ i → ●ᶜ (◯ᶜ A-abs) .is-set
                (●ᶜ.map (α ⨾ᶜ η◦ᶜ {A = A-abs}) .U
                  (●ᶜ-map-CHARGE {A = A-⊤} c (q .•) i))
                (η• (λ p → A-abs .charge c (q .◦ p))))
              (squareᶜ'
                {A-⊤ = A-⊤} {A-abs = A-abs} {α = α}
                {B-⊤ = A-⊤} {B-abs = A-abs} {β = α}
                (CHARGE c) (CHARGE c)
                α-charge
                .U q .•→◦)
              (Glueᶜ' A-⊤ A-abs α .charge c q .•→◦)
              i
        })

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

  fracture-map-natural
    : (f : A ⊸ B) (q : U (𝒞-fromFRAC (𝒞-toFRAC A)))
    → invEq (𝒞-fracture-equiv B) (fracture-map f .U q)
      ≡ f .U (invEq (𝒞-fracture-equiv A) q)
  fracture-map-natural {A} {B} f q =
    isEmbedding→Inj (isEquiv→isEmbedding (𝒞-fracture-equiv B .snd))
      (invEq (𝒞-fracture-equiv B) (fracture-map f .U q))
      (f .U (invEq (𝒞-fracture-equiv A) q))
      (  fracture {X = U B} (invEq (𝒞-fracture-equiv B) (fracture-map f .U q))
       ≡⟨ secEq (𝒞-fracture-equiv B) (fracture-map f .U q) ⟩
         fracture-map f .U q
       ≡⟨ cong (fracture-map f .U) (sym (secEq (𝒞-fracture-equiv A) q)) ⟩
         fracture-map f .U (fracture {X = U A} (invEq (𝒞-fracture-equiv A) q))
       ≡⟨ fracture-map-fracture {A = A} {B = B} f (invEq (𝒞-fracture-equiv A) q) ⟩
         fracture {X = U B} (f .U (invEq (𝒞-fracture-equiv A) q))
       ∎)

  fracture-map-same-U
    : (f : A ⊸ B)
    → PathP
        (λ i →
          𝒞-glue-fracture-retract-U-path A i
          → 𝒞-glue-fracture-retract-U-path B i)
        (fracture-map f .U)
        (f .U)
  fracture-map-same-U {A} {B} f =
    ua→ {e = invEquiv (𝒞-fracture-equiv A)} λ q →
      ua-gluePath
        (invEquiv (𝒞-fracture-equiv B))
        (fracture-map-natural f q)

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
      (fracture-map-same-U f)

  triangleᶜ' : ∀ {B-⊤ B-abs β} (b-⊤ : U B-⊤) (b-abs : U B-abs)
    → β .U b-⊤ ≡ b-abs
    → U (Glueᶜ' B-⊤ B-abs β)
  triangleᶜ' b-⊤ b-abs b-coherence .• = η• b-⊤
  triangleᶜ' {B-abs = B-abs} b-⊤ b-abs b-coherence .◦ = η◦ᶜ {A = B-abs} .U b-abs
  triangleᶜ' {B-abs = B-abs} b-⊤ b-abs b-coherence .•→◦ =
    cong (λ b → η• (η◦ᶜ {A = B-abs} .U b)) b-coherence

  squareᶜ'-FRAC
    : ∀ {A-⊤ A-abs α B-⊤ B-abs β}
    → (f-⊤ : A-⊤ ⊸ B-⊤) (f-abs : A-abs ⊸ B-abs)
    → ((a-⊤ : U A-⊤) → U β (U f-⊤ a-⊤) ≡ U f-abs (U α a-⊤))
    → 𝒞-fromFRAC (Glueᶜ'-FRAC A-⊤ A-abs α)
        ⊸ 𝒞-fromFRAC (Glueᶜ'-FRAC B-⊤ B-abs β)
  squareᶜ'-FRAC f-⊤ f-abs f-coherence =
    squareᶜ' f-⊤ f-abs f-coherence

  Glueᶜ'-glue•-out-square
    : ∀ {A-⊤ A-abs α B-⊤ B-abs β f-⊤ f-abs f-coherence}
    → (q• : U (●ᶜ (𝒞-fromFRAC (Glueᶜ'-FRAC A-⊤ A-abs α))))
    → glue•-out
        (𝒞-FRAC→FRAC (Glueᶜ'-FRAC B-⊤ B-abs β))
        (●ᶜ.map (squareᶜ'-FRAC {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} f-⊤ f-abs f-coherence) .U q•)
      ≡ ●ᶜ.map f-⊤ .U
        (glue•-out
          (𝒞-FRAC→FRAC (Glueᶜ'-FRAC A-⊤ A-abs α))
          q•)
  Glueᶜ'-glue•-out-square {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} {f-⊤} {f-abs} {f-coherence} q• =
    isEmbedding→Inj
      (isEquiv→isEmbedding (Glueᶜ'-FRAC B-⊤ B-abs β .A• .snd))
      (glue•-out
        (𝒞-FRAC→FRAC (Glueᶜ'-FRAC B-⊤ B-abs β))
        (●ᶜ.map (squareᶜ'-FRAC {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} f-⊤ f-abs f-coherence) .U q•))
      (●ᶜ.map f-⊤ .U
        (glue•-out
          (𝒞-FRAC→FRAC (Glueᶜ'-FRAC A-⊤ A-abs α))
          q•))
      (  η•
          (glue•-out
            (𝒞-FRAC→FRAC (Glueᶜ'-FRAC B-⊤ B-abs β))
            (●ᶜ.map (squareᶜ'-FRAC {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} f-⊤ f-abs f-coherence) .U q•))
       ≡⟨ secIsEq
          (Glueᶜ'-FRAC B-⊤ B-abs β .A• .snd)
          (●ᶜ.map (proj•ᶜ (Glueᶜ'-FRAC B-⊤ B-abs β)) .U
            (●ᶜ.map (squareᶜ'-FRAC {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} f-⊤ f-abs f-coherence) .U q•)) ⟩
         ●ᶜ.map (proj•ᶜ (Glueᶜ'-FRAC B-⊤ B-abs β)) .U
           (●ᶜ.map (squareᶜ'-FRAC {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} f-⊤ f-abs f-coherence) .U q•)
       ≡⟨ ●.map-∘
          (squareᶜ'-FRAC {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} f-⊤ f-abs f-coherence .U)
          (proj•ᶜ (Glueᶜ'-FRAC B-⊤ B-abs β) .U)
          q• ⟩
         ●.map (λ q → ●ᶜ.map f-⊤ .U (q .•)) q•
       ≡⟨ sym (●.map-∘
          (proj•ᶜ (Glueᶜ'-FRAC A-⊤ A-abs α) .U)
          (●ᶜ.map f-⊤ .U)
          q•) ⟩
         ●ᶜ.map (●ᶜ.map f-⊤) .U
           (●ᶜ.map (proj•ᶜ (Glueᶜ'-FRAC A-⊤ A-abs α)) .U q•)
       ≡⟨ cong (●.map (●ᶜ.map f-⊤ .U))
          (sym (secIsEq
            (Glueᶜ'-FRAC A-⊤ A-abs α .A• .snd)
            (●ᶜ.map (proj•ᶜ (Glueᶜ'-FRAC A-⊤ A-abs α)) .U q•))) ⟩
         η•
           (●ᶜ.map f-⊤ .U
             (glue•-out
               (𝒞-FRAC→FRAC (Glueᶜ'-FRAC A-⊤ A-abs α))
               q•))
       ∎)

  Glueᶜ'-Glueᶜ'-α•-path
    : ∀ {A-⊤ A-abs α B-⊤ B-abs β f-⊤ f-abs f-coherence}
    → PathP
        (λ i →
          𝒞-glue•-path (Glueᶜ'-FRAC A-⊤ A-abs α) i .fst
            ⊸ ●ᶜ (𝒞-glue◦-path (Glueᶜ'-FRAC B-⊤ B-abs β) i .fst))
        (●ᶜ.map
          (squareᶜ'-FRAC {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} f-⊤ f-abs f-coherence
            ⨾ᶜ η◦ᶜ {A = 𝒞-fromFRAC (Glueᶜ'-FRAC B-⊤ B-abs β)}))
        (●ᶜ.map ((α ⨾ᶜ f-abs) ⨾ᶜ η◦ᶜ {A = B-abs}))
  Glueᶜ'-Glueᶜ'-α•-path {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} {f-⊤} {f-abs} {f-coherence} =
    ⊸-path
      (λ i → 𝒞-glue•-path (Glueᶜ'-FRAC A-⊤ A-abs α) i .fst)
      (λ i → ●ᶜ (𝒞-glue◦-path (Glueᶜ'-FRAC B-⊤ B-abs β) i .fst))
      (ua→
        {e = glue•-equiv (𝒞-FRAC→FRAC (Glueᶜ'-FRAC A-⊤ A-abs α))}
        λ q• →
          toPathP
            (  transport
                (λ i → U (●ᶜ (𝒞-glue◦-path (Glueᶜ'-FRAC B-⊤ B-abs β) i .fst)))
                (●.map
                  (η◦ᶜ {A = 𝒞-fromFRAC (Glueᶜ'-FRAC B-⊤ B-abs β)} .U
                    ∘ squareᶜ'-FRAC {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} f-⊤ f-abs f-coherence .U)
                  q•)
             ≡⟨ cong
                  (transport
                    (λ i → U (●ᶜ (𝒞-glue◦-path (Glueᶜ'-FRAC B-⊤ B-abs β) i .fst))))
                  (sym (●.map-∘
                    (squareᶜ'-FRAC {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} f-⊤ f-abs f-coherence .U)
                    (η◦ᶜ {A = 𝒞-fromFRAC (Glueᶜ'-FRAC B-⊤ B-abs β)} .U)
                    q•)) ⟩
               transport
                (λ i → U (●ᶜ (𝒞-glue◦-path (Glueᶜ'-FRAC B-⊤ B-abs β) i .fst)))
                (●.map (η◦ᶜ {A = 𝒞-fromFRAC (Glueᶜ'-FRAC B-⊤ B-abs β)} .U)
                  (●.map
                    (squareᶜ'-FRAC {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} f-⊤ f-abs f-coherence .U)
                    q•))
             ≡⟨ fromPathP
                (glue-χ-path-base
                  (𝒞-FRAC→FRAC (Glueᶜ'-FRAC B-⊤ B-abs β))
                  (●ᶜ.map (squareᶜ'-FRAC {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} f-⊤ f-abs f-coherence) .U q•)) ⟩
               Glueᶜ'-FRAC B-⊤ B-abs β .α• .U
                (glue•-out
                  (𝒞-FRAC→FRAC (Glueᶜ'-FRAC B-⊤ B-abs β))
                  (●ᶜ.map (squareᶜ'-FRAC {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} f-⊤ f-abs f-coherence) .U q•))
             ≡⟨ cong
                (λ q → Glueᶜ'-FRAC B-⊤ B-abs β .α• .U q)
                (Glueᶜ'-glue•-out-square
                  {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} {f-⊤} {f-abs} {f-coherence}
                  q•) ⟩
               Glueᶜ'-FRAC B-⊤ B-abs β .α• .U
                (●ᶜ.map f-⊤ .U
                  (glue•-out
                    (𝒞-FRAC→FRAC (Glueᶜ'-FRAC A-⊤ A-abs α))
                    q•))
             ≡⟨ ●.map-∘
                (f-⊤ .U)
                ((β ⨾ᶜ η◦ᶜ {A = B-abs}) .U)
                (glue•-out
                  (𝒞-FRAC→FRAC (Glueᶜ'-FRAC A-⊤ A-abs α))
                  q•) ⟩
               ●.map (((β ⨾ᶜ η◦ᶜ {A = B-abs}) .U) ∘ f-⊤ .U)
                (glue•-out
                  (𝒞-FRAC→FRAC (Glueᶜ'-FRAC A-⊤ A-abs α))
                  q•)
             ≡⟨ cong
                (λ h → ●.map h
                  (glue•-out
                    (𝒞-FRAC→FRAC (Glueᶜ'-FRAC A-⊤ A-abs α))
                    q•))
                (funExt λ a →
                  cong (η◦ᶜ {A = B-abs} .U) (f-coherence a)) ⟩
               ●.map (((α ⨾ᶜ f-abs) ⨾ᶜ η◦ᶜ {A = B-abs}) .U)
                (glue•-out
                  (𝒞-FRAC→FRAC (Glueᶜ'-FRAC A-⊤ A-abs α))
                  q•)
             ∎))

  Glueᶜ'-Glueᶜ'-FRAC
    : ∀ {A-⊤ A-abs α B-⊤ B-abs β f-⊤ f-abs f-coherence}
    → Glueᶜ'-FRAC
        (𝒞-fromFRAC (Glueᶜ'-FRAC A-⊤ A-abs α))
        (𝒞-fromFRAC (Glueᶜ'-FRAC B-⊤ B-abs β))
        (squareᶜ'-FRAC {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} f-⊤ f-abs f-coherence)
      ≡ Glueᶜ'-FRAC A-⊤ B-abs (α ⨾ᶜ f-abs)
  Glueᶜ'-Glueᶜ'-FRAC {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} {f-⊤} {f-abs} {f-coherence} =
    𝒞-FRAC-path
      (𝒞-glue•-path (Glueᶜ'-FRAC A-⊤ A-abs α))
      (𝒞-glue◦-path (Glueᶜ'-FRAC B-⊤ B-abs β))
      (Glueᶜ'-Glueᶜ'-α•-path {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} {f-⊤} {f-abs} {f-coherence})

  Glueᶜ'-Glueᶜ' : ∀ {A-⊤ A-abs α B-⊤ B-abs β f-⊤ f-abs f-coherence} →
    Glueᶜ' (Glueᶜ' A-⊤ A-abs α) (Glueᶜ' B-⊤ B-abs β) (squareᶜ' {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} f-⊤ f-abs f-coherence)
    ≡ Glueᶜ' A-⊤ B-abs (α ⨾ᶜ f-abs)
  Glueᶜ'-Glueᶜ' {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} {f-⊤} {f-abs} {f-coherence} =
      cong 𝒞-fromFRAC
        (Glueᶜ'-Glueᶜ'-FRAC
          {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} {f-⊤} {f-abs} {f-coherence})

module _ where
  open import Calf.Computation.Free

  PotentialFunction : (X → ℂ) → 𝒞
  PotentialFunction {X} Φ = Glueᶜ' (F X) (F X) (bind' λ x → F _ .charge (Φ x) (ret x))
