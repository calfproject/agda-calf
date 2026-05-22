open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Calf.Computation.Glue (φ : Type) (φ-isProp : isProp φ) where

open import Calf.Core.Cost
open import Calf.Computation
open import Calf.Value
open import Calf.Value.Closed φ φ-isProp using (η•)
open import Calf.Value.Open φ φ-isProp using (η∘)
open import Calf.Value.Glue φ φ-isProp
open import Calf.Computation.Open φ φ-isProp as ◯
open import Calf.Computation.Closed φ φ-isProp as ●
open import Cubical.Data.Sigma
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence using (ua; ua→; ua-gluePath)
open import Cubical.Functions.Embedding

Glueᶜ : (A• : 𝒞•) (A∘ : 𝒞∘) (α : A• .fst ⊸ ●ᶜ (A∘ .fst)) → 𝒞
Glueᶜ A• A∘ α .U = Glueᵛ (U• A•) (U∘ A∘) (α .U)
Glueᶜ A• A∘ α .charge c a .• = A• .fst .charge c (a .•)
Glueᶜ A• A∘ α .charge c a .∘ = A∘ .fst .charge c (a .∘)
Glueᶜ A• A∘ α .charge c a .•→∘ = α .charge c (a .•) ∙ cong (●ᶜ (A∘ .fst) .charge c) (a .•→∘)
Glueᶜ A• A∘ α .charge/0 {a} i .• = A• .fst .charge/0 {a .•} i
Glueᶜ A• A∘ α .charge/0 {a} i .∘ = A∘ .fst .charge/0 {a .∘} i
Glueᶜ A• A∘ α .charge/0 {a} i .•→∘ =
  isProp→PathP
    (λ i → 𝒱.isSet𝒱 (●ᶜ (A∘ .fst) .U)
      (α .U (A• .fst .charge/0 {a .•} i))
      (η• (A∘ .fst .charge/0 {a .∘} i)))
    (α .charge 0ℂ (a .•) ∙ cong (●ᶜ (A∘ .fst) .charge 0ℂ) (a .•→∘))
    (a .•→∘)
    i
Glueᶜ A• A∘ α .charge/+ {a} {c₁} {c₂} i .• =
  A• .fst .charge/+ {a .•} {c₁} {c₂} i
Glueᶜ A• A∘ α .charge/+ {a} {c₁} {c₂} i .∘ =
  A∘ .fst .charge/+ {a .∘} {c₁} {c₂} i
Glueᶜ A• A∘ α .charge/+ {a} {c₁} {c₂} i .•→∘ =
  isProp→PathP
    (λ i → 𝒱.isSet𝒱 (●ᶜ (A∘ .fst) .U)
      (α .U (A• .fst .charge/+ {a .•} {c₁} {c₂} i))
      (η• (A∘ .fst .charge/+ {a .∘} {c₁} {c₂} i)))
    (α .charge (c₁ +ℂ c₂) (a .•) ∙ cong (●ᶜ (A∘ .fst) .charge (c₁ +ℂ c₂)) (a .•→∘))
    (α .charge c₁ (A• .fst .charge c₂ (a .•))
      ∙ cong (●ᶜ (A∘ .fst) .charge c₁)
        (α .charge c₂ (a .•) ∙ cong (●ᶜ (A∘ .fst) .charge c₂) (a .•→∘)))
    i

record 𝒞-FRAC : Type₁ where
  field
    A• : 𝒞•
    A∘ : 𝒞∘
    α : A• .fst ⊸ ●ᶜ (A∘ .fst)
open 𝒞-FRAC

isPropCharge/0
  : {U : 𝒱} (charge : val ℂ → val U → val U)
  → isProp (∀ {a} → charge 0ℂ a ≡ a)
isPropCharge/0 {U} charge =
  isPropImplicitΠ λ a → 𝒱.isSet𝒱 U (charge 0ℂ a) a

isPropCharge/+
  : {U : 𝒱} (charge : val ℂ → val U → val U)
  → isProp (∀ {a c₁ c₂} → charge (c₁ +ℂ c₂) a ≡ charge c₁ (charge c₂ a))
isPropCharge/+ {U} charge =
  isPropImplicitΠ3 λ a c₁ c₂ →
    𝒱.isSet𝒱 U (charge (c₁ +ℂ c₂) a) (charge c₁ (charge c₂ a))

𝒞-path
  : {A B : 𝒞}
  → (U-path : A .U ≡ B .U)
  → PathP
      (λ i → val ℂ → val (U-path i) → val (U-path i))
      (A .charge)
      (B .charge)
  → A ≡ B
𝒞-path {A} {B} U-path charge-path i .U = U-path i
𝒞-path {A} {B} U-path charge-path i .charge = charge-path i
𝒞-path {A} {B} U-path charge-path i .charge/0 =
  isProp→PathP
    (λ i → isPropCharge/0 {U = U-path i} (charge-path i))
    (A .charge/0)
    (B .charge/0)
    i
𝒞-path {A} {B} U-path charge-path i .charge/+ =
  isProp→PathP
    (λ i → isPropCharge/+ {U = U-path i} (charge-path i))
    (A .charge/+)
    (B .charge/+)
    i

𝒞•-path : {A• B• : 𝒞•} → A• .fst ≡ B• .fst → A• ≡ B•
𝒞•-path p = Σ≡Prop (λ A → isPropIsEquiv (η•ᶜ {A} .U)) p

𝒞∘-path : {A∘ B∘ : 𝒞∘} → A∘ .fst ≡ B∘ .fst → A∘ ≡ B∘
𝒞∘-path p = Σ≡Prop (λ A → isPropIsEquiv (η∘ᶜ {A} .U)) p

isProp⊸charge
  : (A B : 𝒞) (f : cmp A → cmp B)
  → isProp ((c : val ℂ) (a : cmp A) → f (A .charge c a) ≡ B .charge c (f a))
isProp⊸charge A B f =
  isPropΠ2 λ c a → 𝒱.isSet𝒱 (B .U) (f (A .charge c a)) (B .charge c (f a))

⊸-path
  : {A₀ A₁ B₀ B₁ : 𝒞}
  → (A-path : A₀ ≡ A₁)
  → (B-path : B₀ ≡ B₁)
  → {f₀ : A₀ ⊸ B₀}
  → {f₁ : A₁ ⊸ B₁}
  → PathP (λ i → cmp (A-path i) → cmp (B-path i)) (f₀ .U) (f₁ .U)
  → PathP (λ i → A-path i ⊸ B-path i) f₀ f₁
⊸-path A-path B-path {f₀ = f₀} {f₁ = f₁} U-path i .U = U-path i
⊸-path A-path B-path {f₀ = f₀} {f₁ = f₁} U-path i .charge =
  isProp→PathP
    (λ i → isProp⊸charge (A-path i) (B-path i) (U-path i))
    (f₀ .charge)
    (f₁ .charge)
    i

𝒞-FRAC→𝒱-FRAC : 𝒞-FRAC → 𝒱-FRAC
𝒞-FRAC→𝒱-FRAC F =
  record
    { X• = U• (F .A•)
    ; X∘ = U∘ (F .A∘)
    ; χ = F .α .U
    }

charge-path-inv
  : {X Y : Type}
  → (e : X ≃ Y)
  → (chargeX : val ℂ → X → X)
  → (chargeY : val ℂ → Y → Y)
  → ((c : val ℂ) (y : Y) → invEq e (chargeY c y) ≡ chargeX c (invEq e y))
  → PathP
      (λ i → val ℂ → ua (invEquiv e) i → ua (invEquiv e) i)
      chargeY
      chargeX
charge-path-inv e chargeX chargeY h =
  funExt λ c →
    ua→ {e = invEquiv e} λ y →
      ua-gluePath (invEquiv e) (h c y)

charge-path
  : {X Y : Type}
  → (e : X ≃ Y)
  → (chargeX : val ℂ → X → X)
  → (chargeY : val ℂ → Y → Y)
  → ((c : val ℂ) (x : X) → e .fst (chargeX c x) ≡ chargeY c (e .fst x))
  → PathP
      (λ i → val ℂ → ua e i → ua e i)
      chargeX
      chargeY
charge-path e chargeX chargeY h =
  funExt λ c →
    ua→ {e = e} λ x →
      ua-gluePath e (h c x)

𝒞-toFRAC : 𝒞 → 𝒞-FRAC
𝒞-toFRAC A .A• = ●ᶜ A , ●-η-isEquiv
𝒞-toFRAC A .A∘ = ◯ᶜ A , ◯-η-isEquiv
𝒞-toFRAC A .α = ●.map η∘ᶜ

𝒞-fromFRAC : 𝒞-FRAC → 𝒞
𝒞-fromFRAC F = Glueᶜ (F .A•) (F .A∘) (F .α)

proj•ᶜ : (F : 𝒞-FRAC) → 𝒞-fromFRAC F ⊸ F .A• .fst
proj•ᶜ F .U g = g .•
proj•ᶜ F .charge c g = refl

proj∘ᶜ : (F : 𝒞-FRAC) → 𝒞-fromFRAC F ⊸ F .A∘ .fst
proj∘ᶜ F .U g = g .∘
proj∘ᶜ F .charge c g = refl

glue•-out-charge
  : (F : 𝒞-FRAC) (c : val ℂ) (g• : cmp (●ᶜ (𝒞-fromFRAC F)))
  → glue•-out (𝒱-FRAC→FRAC (𝒞-FRAC→𝒱-FRAC F)) (●ᶜ (𝒞-fromFRAC F) .charge c g•)
    ≡ F .A• .fst .charge c
      (glue•-out (𝒱-FRAC→FRAC (𝒞-FRAC→𝒱-FRAC F)) g•)
glue•-out-charge F c g• =
  isEmbedding→Inj (isEquiv→isEmbedding (F .A• .snd))
    (glue•-out (𝒱-FRAC→FRAC (𝒞-FRAC→𝒱-FRAC F)) (●ᶜ (𝒞-fromFRAC F) .charge c g•))
    (F .A• .fst .charge c
      (glue•-out (𝒱-FRAC→FRAC (𝒞-FRAC→𝒱-FRAC F)) g•))
    (secIsEq (F .A• .snd) (map (proj•ᶜ F) .U (●ᶜ (𝒞-fromFRAC F) .charge c g•))
      ∙ map (proj•ᶜ F) .charge c g•
      ∙ cong (●ᶜ (F .A• .fst) .charge c)
        (sym (secIsEq (F .A• .snd) (map (proj•ᶜ F) .U g•))))

glue∘-out-charge
  : (F : 𝒞-FRAC) (c : val ℂ) (g∘ : cmp (◯ᶜ (𝒞-fromFRAC F)))
  → glue∘-out (𝒱-FRAC→FRAC (𝒞-FRAC→𝒱-FRAC F)) (◯ᶜ (𝒞-fromFRAC F) .charge c g∘)
    ≡ F .A∘ .fst .charge c
      (glue∘-out (𝒱-FRAC→FRAC (𝒞-FRAC→𝒱-FRAC F)) g∘)
glue∘-out-charge F c g∘ =
  isEmbedding→Inj (isEquiv→isEmbedding (F .A∘ .snd))
    (glue∘-out (𝒱-FRAC→FRAC (𝒞-FRAC→𝒱-FRAC F)) (◯ᶜ (𝒞-fromFRAC F) .charge c g∘))
    (F .A∘ .fst .charge c
      (glue∘-out (𝒱-FRAC→FRAC (𝒞-FRAC→𝒱-FRAC F)) g∘))
    (secIsEq (F .A∘ .snd) (λ p → F .A∘ .fst .charge c (g∘ p .∘))
      ∙ funExt (λ p →
        cong (F .A∘ .fst .charge c)
          (sym (funExt⁻ (secIsEq (F .A∘ .snd) (λ p → g∘ p .∘)) p))))

𝒞-glue•-path : (F : 𝒞-FRAC) →
  (●ᶜ (𝒞-fromFRAC F) , ●-η-isEquiv) ≡ F .A•
𝒞-glue•-path F =
  𝒞•-path
    (𝒞-path
      (cong fst (𝒱-glue•-path (𝒞-FRAC→𝒱-FRAC F)))
      (charge-path
        (glue•-equiv (𝒱-FRAC→FRAC (𝒞-FRAC→𝒱-FRAC F)))
        (●ᶜ (𝒞-fromFRAC F) .charge)
        (F .A• .fst .charge)
        (glue•-out-charge F)))

𝒞-glue∘-path : (F : 𝒞-FRAC) →
  (◯ᶜ (𝒞-fromFRAC F) , ◯-η-isEquiv) ≡ F .A∘
𝒞-glue∘-path F =
  𝒞∘-path
    (𝒞-path
      (cong fst (𝒱-glue∘-path (𝒞-FRAC→𝒱-FRAC F)))
      (charge-path
        (glue∘-equiv (𝒱-FRAC→FRAC (𝒞-FRAC→𝒱-FRAC F)))
        (◯ᶜ (𝒞-fromFRAC F) .charge)
        (F .A∘ .fst .charge)
        (glue∘-out-charge F)))

𝒞-glue-fracture-section : section 𝒞-toFRAC 𝒞-fromFRAC
𝒞-glue-fracture-section F i .A• = 𝒞-glue•-path F i
𝒞-glue-fracture-section F i .A∘ = 𝒞-glue∘-path F i
𝒞-glue-fracture-section F i .α =
  ⊸-path
    (λ i → 𝒞-glue•-path F i .fst)
    (λ i → ●ᶜ (𝒞-glue∘-path F i .fst))
    {f₀ = map η∘ᶜ}
    {f₁ = F .α}
    (λ i → FRAC.χ (glue-fracture-section (𝒱-FRAC→FRAC (𝒞-FRAC→𝒱-FRAC F)) i))
    i

𝒞-fracture-equiv : (A : 𝒞) → cmp A ≃ cmp (𝒞-fromFRAC (𝒞-toFRAC A))
𝒞-fracture-equiv A = fracture , fracture-isEquiv

fracture-charge
  : (A : 𝒞) (c : val ℂ) (a : cmp A)
  → 𝒞-fromFRAC (𝒞-toFRAC A) .charge c (fracture {X = cmp A} a)
    ≡ fracture {X = cmp A} (A .charge c a)
fracture-charge A c a i .• = η• (A .charge c a)
fracture-charge A c a i .∘ = η∘ (A .charge c a)
fracture-charge A c a i .•→∘ =
  isProp→PathP
    (λ i → 𝒱.isSet𝒱 (●ᶜ (◯ᶜ A) .U)
      (𝒞-fromFRAC (𝒞-toFRAC A) .charge c (fracture a) .•→∘ i0)
      (η• (η∘ (A .charge c a))))
    (𝒞-fromFRAC (𝒞-toFRAC A) .charge c (fracture a) .•→∘)
    refl
    i

fracture-inv-charge
  : (A : 𝒞) (c : val ℂ) (g : cmp (𝒞-fromFRAC (𝒞-toFRAC A)))
  → invEq (𝒞-fracture-equiv A) (𝒞-fromFRAC (𝒞-toFRAC A) .charge c g)
    ≡ A .charge c (invEq (𝒞-fracture-equiv A) g)
fracture-inv-charge A c g =
  isEmbedding→Inj (isEquiv→isEmbedding (𝒞-fracture-equiv A .snd))
    (invEq (𝒞-fracture-equiv A) (𝒞-fromFRAC (𝒞-toFRAC A) .charge c g))
    (A .charge c (invEq (𝒞-fracture-equiv A) g))
    (secEq (𝒞-fracture-equiv A) (𝒞-fromFRAC (𝒞-toFRAC A) .charge c g)
      ∙ sym (cong (𝒞-fromFRAC (𝒞-toFRAC A) .charge c) (secEq (𝒞-fracture-equiv A) g))
      ∙ fracture-charge A c (invEq (𝒞-fracture-equiv A) g))

𝒞-glue-fracture-retract-U-path : (A : 𝒞) → 𝒞-fromFRAC (𝒞-toFRAC A) .U ≡ A .U
𝒞-glue-fracture-retract-U-path A =
  𝒱-path
    {X = 𝒞-fromFRAC (𝒞-toFRAC A) .U}
    {Y = A .U}
    (ua (invEquiv (𝒞-fracture-equiv A)))

𝒞-glue-fracture-retract-charge
  : (A : 𝒞)
  → PathP
      (λ i →
        val ℂ
        → val (𝒞-glue-fracture-retract-U-path A i)
        → val (𝒞-glue-fracture-retract-U-path A i))
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
