open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence using (ua)
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
