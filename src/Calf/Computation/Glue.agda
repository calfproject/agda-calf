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
import Calf.Value.Closed as ●ᵛ
import Calf.Value.Open as ◯ᵛ
open import Calf.Value.Glue public
open import Calf.Computation.Open as ◯
open import Calf.Computation.Closed as ●ᶜ

Glueᶜ : (A• : 𝒞•) (A◦ : 𝒞◦) (α : A• .fst ⊸ ●ᶜ (A◦ .fst)) → 𝒞
Glueᶜ A• A◦ α .U = Glueᵛ (U• A•) (U◦ A◦) (α .U)
Glueᶜ A• A◦ α .charge c a .• = A• .fst .charge c (a .•)
Glueᶜ A• A◦ α .charge c a .◦ = A◦ .fst .charge c (a .◦)
Glueᶜ A• A◦ α .charge c a .•→◦ = α .charge c (a .•) ∙ cong (●ᶜ (A◦ .fst) .charge c) (a .•→◦)
Glueᶜ A• A◦ α .charge/0 {a} i .• = A• .fst .charge/0 {a .•} i
Glueᶜ A• A◦ α .charge/0 {a} i .◦ = A◦ .fst .charge/0 {a .◦} i
Glueᶜ A• A◦ α .charge/0 {a} i .•→◦ =
  isProp→PathP
    (λ i → ●ᶜ (A◦ .fst) .U .is-set
      (α .U (A• .fst .charge/0 {a .•} i))
      (η• (A◦ .fst .charge/0 {a .◦} i)))
    (α .charge 0ℂ (a .•) ∙ cong (●ᶜ (A◦ .fst) .charge 0ℂ) (a .•→◦))
    (a .•→◦)
    i
Glueᶜ A• A◦ α .charge/+ {a} {c₁} {c₂} i .• =
  A• .fst .charge/+ {a .•} {c₁} {c₂} i
Glueᶜ A• A◦ α .charge/+ {a} {c₁} {c₂} i .◦ =
  A◦ .fst .charge/+ {a .◦} {c₁} {c₂} i
Glueᶜ A• A◦ α .charge/+ {a} {c₁} {c₂} i .•→◦ =
  isProp→PathP
    (λ i → ●ᶜ (A◦ .fst) .U .is-set
      (α .U (A• .fst .charge/+ {a .•} {c₁} {c₂} i))
      (η• (A◦ .fst .charge/+ {a .◦} {c₁} {c₂} i)))
    (α .charge (c₁ +ℂ c₂) (a .•) ∙ cong (●ᶜ (A◦ .fst) .charge (c₁ +ℂ c₂)) (a .•→◦))
    (α .charge c₁ (A• .fst .charge c₂ (a .•))
      ∙ cong (●ᶜ (A◦ .fst) .charge c₁)
        (α .charge c₂ (a .•) ∙ cong (●ᶜ (A◦ .fst) .charge c₂) (a .•→◦)))
    i

record 𝒞-FRAC : Type₁ where
  field
    A• : 𝒞•
    A◦ : 𝒞◦
    α : A• .fst ⊸ ●ᶜ (A◦ .fst)
open 𝒞-FRAC

𝒞-FRAC→𝒱-FRAC : 𝒞-FRAC → 𝒱-FRAC
𝒞-FRAC→𝒱-FRAC F =
  record
    { X• = U• (F .A•)
    ; X◦ = U◦ (F .A◦)
    ; χ = F .α .U
    }

𝒞-toFRAC : 𝒞 → 𝒞-FRAC
𝒞-toFRAC A .A• = ●ᶜ A , ●ᶜ-η•ᶜ-isEquiv {A}
𝒞-toFRAC A .A◦ = ◯ᶜ A , ◯ᶜ-ηᶜ-isEquiv
𝒞-toFRAC A .α = ●ᶜ.map η◦ᶜ

𝒞-fromFRAC : 𝒞-FRAC → 𝒞
𝒞-fromFRAC F = Glueᶜ (F .A•) (F .A◦) (F .α)

proj•ᶜ : (F : 𝒞-FRAC) → 𝒞-fromFRAC F ⊸ F .A• .fst
proj•ᶜ F .U g = g .•
proj•ᶜ F .charge c g = refl

proj◦ᶜ : (F : 𝒞-FRAC) → 𝒞-fromFRAC F ⊸ F .A◦ .fst
proj◦ᶜ F .U g = g .◦
proj◦ᶜ F .charge c g = refl

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
    (secIsEq (F .A• .snd) (●ᶜ.map (proj•ᶜ F) .U (●ᶜ (𝒞-fromFRAC F) .charge c g•))
      ∙ ●ᶜ.map (proj•ᶜ F) .charge c g•
      ∙ cong (●ᶜ (F .A• .fst) .charge c)
        (sym (secIsEq (F .A• .snd) (●ᶜ.map (proj•ᶜ F) .U g•))))

glue◦-out-charge
  : (F : 𝒞-FRAC) (c : val ℂ) (g◦ : cmp (◯ᶜ (𝒞-fromFRAC F)))
  → glue◦-out (𝒱-FRAC→FRAC (𝒞-FRAC→𝒱-FRAC F)) (◯ᶜ (𝒞-fromFRAC F) .charge c g◦)
    ≡ F .A◦ .fst .charge c
      (glue◦-out (𝒱-FRAC→FRAC (𝒞-FRAC→𝒱-FRAC F)) g◦)
glue◦-out-charge F c g◦ =
  isEmbedding→Inj (isEquiv→isEmbedding (F .A◦ .snd))
    (glue◦-out (𝒱-FRAC→FRAC (𝒞-FRAC→𝒱-FRAC F)) (◯ᶜ (𝒞-fromFRAC F) .charge c g◦))
    (F .A◦ .fst .charge c
      (glue◦-out (𝒱-FRAC→FRAC (𝒞-FRAC→𝒱-FRAC F)) g◦))
    (secIsEq (F .A◦ .snd) (λ p → F .A◦ .fst .charge c (g◦ p .◦))
      ∙ funExt (λ p →
        cong (F .A◦ .fst .charge c)
          (sym (funExt⁻ (secIsEq (F .A◦ .snd) (λ p → g◦ p .◦)) p))))

𝒞-glue•-path : (F : 𝒞-FRAC) →
  (●ᶜ (𝒞-fromFRAC F) , ●ᶜ-η•ᶜ-isEquiv {𝒞-fromFRAC F}) ≡ F .A•
𝒞-glue•-path F =
  𝒞•-path
    (𝒞-path
      (cong fst (𝒱-glue•-path (𝒞-FRAC→𝒱-FRAC F)))
      (charge-path
        (glue•-equiv (𝒱-FRAC→FRAC (𝒞-FRAC→𝒱-FRAC F)))
        (●ᶜ (𝒞-fromFRAC F) .charge)
        (F .A• .fst .charge)
        (glue•-out-charge F)))

𝒞-glue◦-path : (F : 𝒞-FRAC) →
  (◯ᶜ (𝒞-fromFRAC F) , ◯ᶜ-ηᶜ-isEquiv) ≡ F .A◦
𝒞-glue◦-path F =
  𝒞◦-path
    (𝒞-path
      (cong fst (𝒱-glue◦-path (𝒞-FRAC→𝒱-FRAC F)))
      (charge-path
        (glue◦-equiv (𝒱-FRAC→FRAC (𝒞-FRAC→𝒱-FRAC F)))
        (◯ᶜ (𝒞-fromFRAC F) .charge)
        (F .A◦ .fst .charge)
        (glue◦-out-charge F)))

𝒞-glue-fracture-section : section 𝒞-toFRAC 𝒞-fromFRAC
𝒞-glue-fracture-section F i .A• = 𝒞-glue•-path F i
𝒞-glue-fracture-section F i .A◦ = 𝒞-glue◦-path F i
𝒞-glue-fracture-section F i .α =
  ⊸-path
    (λ i → 𝒞-glue•-path F i .fst)
    (λ i → ●ᶜ (𝒞-glue◦-path F i .fst))
    {f₀ = ●ᶜ.map η◦ᶜ}
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
fracture-charge A c a i .◦ = η◦ (A .charge c a)
fracture-charge A c a i .•→◦ =
  isProp→PathP
    (λ i → ●ᶜ (◯ᶜ A) .U .is-set
      (𝒞-fromFRAC (𝒞-toFRAC A) .charge c (fracture a) .•→◦ i0)
      (η• (η◦ (A .charge c a))))
    (𝒞-fromFRAC (𝒞-toFRAC A) .charge c (fracture a) .•→◦)
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

Glueᶜ' : (A-⊤ A-abs : 𝒞) → (A-⊤ ⊸ A-abs) → 𝒞
Glueᶜ' A-⊤ A-abs α = Glueᶜ (●ᶜ A-⊤ , ●ᶜ-η•ᶜ-isEquiv {A-⊤}) (◯ᶜ A-abs , ◯ᶜ-ηᶜ-isEquiv) (●ᶜ.map (α ⨾⊸ η◦ᶜ))

square' : ∀ {A-⊤ A-abs α B-⊤ B-abs β} (f-⊤ : A-⊤ ⊸ B-⊤) (f-abs : A-abs ⊸ B-abs)
  → ((a-⊤ : cmp A-⊤) → U β (U f-⊤ a-⊤) ≡ U f-abs (U α a-⊤))
  → Glueᶜ' A-⊤ A-abs α ⊸ Glueᶜ' B-⊤ B-abs β
square' {A-abs = A-abs} {α = α} {B-abs = B-abs} {β = β} f-⊤ f-abs f-coherence .U q .• =
  ●ᶜ.map f-⊤ .U (q .•)
square' {A-abs = A-abs} {α = α} {B-abs = B-abs} {β = β} f-⊤ f-abs f-coherence .U q .◦ =
  ◯ᵛ.map (f-abs .U) (q .◦)
square' {A-abs = A-abs} {α = α} {B-abs = B-abs} {β = β} f-⊤ f-abs f-coherence .U q .•→◦ =
    ●ᵛ.map (η◦ᶜ {A = B-abs} .U ∘ β .U) (●ᶜ.map f-⊤ .U (q .•))
  ≡⟨ ●ᵛ.●-map-∘ (f-⊤ .U) (η◦ᶜ {A = B-abs} .U ∘ β .U) (q .•) ⟩
    ●ᵛ.map (λ a → η◦ᶜ {A = B-abs} .U (β .U (f-⊤ .U a))) (q .•)
  ≡⟨ cong (λ f → ●ᵛ.map f (q .•)) (funExt λ a → cong (η◦ᶜ {A = B-abs} .U) (f-coherence a)) ⟩
    ●ᵛ.map (λ a → η◦ᶜ {A = B-abs} .U (f-abs .U (α .U a))) (q .•)
  ≡⟨ sym (●ᵛ.●-map-∘ (η◦ᶜ {A = A-abs} .U ∘ α .U) (◯ᵛ.map (f-abs .U)) (q .•)) ⟩
    ●ᵛ.map (◯ᵛ.map (f-abs .U)) (●ᵛ.map (η◦ᶜ {A = A-abs} .U ∘ α .U) (q .•))
  ≡⟨ cong (●ᵛ.map (◯ᵛ.map (f-abs .U))) (q .•→◦) ⟩
    ●ᵛ.map (◯ᵛ.map (f-abs .U)) (η• (q .◦))
  ≡⟨ refl ⟩
    η• (◯ᵛ.map (f-abs .U) (q .◦))
  ∎
square' {A-abs = A-abs} {α = α} {B-abs = B-abs} {β = β} f-⊤ f-abs f-coherence .charge c q i .• =
  ●ᶜ.map f-⊤ .charge c (q .•) i
square' {A-abs = A-abs} {α = α} {B-abs = B-abs} {β = β} f-⊤ f-abs f-coherence .charge c q i .◦ p =
  f-abs .charge c (q .◦ p) i
square' {A-⊤ = A-⊤} {A-abs = A-abs} {α = α} {B-⊤ = B-⊤} {B-abs = B-abs} {β = β} f-⊤ f-abs f-coherence .charge c q i .•→◦ =
  isProp→PathP
    (λ i → ●ᶜ (◯ᶜ B-abs) .U .is-set
      (●ᶜ.map (β ⨾⊸ η◦ᶜ {A = B-abs}) .U (●ᶜ.map f-⊤ .charge c (q .•) i))
      (η• (λ p → f-abs .charge c (q .◦ p) i)))
    (square' {A-⊤ = A-⊤} {A-abs = A-abs} {α = α} {B-⊤ = B-⊤} {B-abs = B-abs} {β = β}
      f-⊤ f-abs f-coherence .U (Glueᶜ' A-⊤ A-abs α .charge c q) .•→◦)
    (Glueᶜ' B-⊤ B-abs β .charge c
      (square' {A-⊤ = A-⊤} {A-abs = A-abs} {α = α} {B-⊤ = B-⊤} {B-abs = B-abs} {β = β}
        f-⊤ f-abs f-coherence .U q) .•→◦)
    i

triangle' : ∀ {B-⊤ B-abs β} (b-⊤ : cmp B-⊤) (b-abs : cmp B-abs)
  → β .U b-⊤ ≡ b-abs
  → cmp (Glueᶜ' B-⊤ B-abs β)
triangle' b-⊤ b-abs b-coherence .• = η• b-⊤
triangle' {B-abs = B-abs} b-⊤ b-abs b-coherence .◦ = η◦ᶜ {A = B-abs} .U b-abs
triangle' {B-abs = B-abs} b-⊤ b-abs b-coherence .•→◦ =
  cong (λ b → η• (η◦ᶜ {A = B-abs} .U b)) b-coherence
