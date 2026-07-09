module Calf.Computation.Glue.Fracture where

open import Calf.Core.Cost
open import Calf.Value
open import Calf.Value.Glue public
open import Calf.Computation
open import Calf.Computation.Open as ◯ᶜ
open import Calf.Computation.Closed as ●ᶜ
open import Cubical.Functions.Embedding

open import Calf.Computation.Glue.Base
open 𝒞-FRAC

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

𝒞-fracture-and-gluing-square : (A ⊸ B) ≡ 𝒞-Square (𝒞-toFRAC A) (𝒞-toFRAC B)
𝒞-fracture-and-gluing-square = {!   !}
