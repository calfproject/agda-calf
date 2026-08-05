module Calf.Computation.Glue.Base where

open import Cubical.Data.Sigma
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels using (isPropΠ)
open import Cubical.Foundations.Isomorphism

open import Calf.Core.Cost
open import Calf.Value
open import Calf.Computation
open import Calf.Computation.Open as ◯ᶜ
open import Calf.Computation.Closed as ●ᶜ

open import Calf.Value.Glue public

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

record 𝒞-FRAC : 𝒱₁ where
  field
    A• : 𝒞•
    A◦ : 𝒞◦
    α• : ⟨ A• ⟩ᶜ ⊸ ●ᶜ ⟨ A◦ ⟩ᶜ
open 𝒞-FRAC

𝒞-fromFRAC : 𝒞-FRAC → 𝒞
𝒞-fromFRAC F = Glueᶜ (F .A•) (F .A◦) (F .α•)

𝒞-toFRAC : 𝒞 → 𝒞-FRAC
𝒞-toFRAC A .A• = ●ᶜ• A
𝒞-toFRAC A .A◦ = ◯ᶜ◦ A
𝒞-toFRAC A .α• = ●ᶜ.map η◦ᶜ

proj•ᶜ : (F : 𝒞-FRAC) → 𝒞-fromFRAC F ⊸ ⟨ F .A• ⟩ᶜ
proj•ᶜ F .U g = g .•
proj•ᶜ F .charge c g = refl

proj◦ᶜ : (F : 𝒞-FRAC) → 𝒞-fromFRAC F ⊸ ⟨ F .A◦ ⟩ᶜ
proj◦ᶜ F .U g = g .◦
proj◦ᶜ F .charge c g = refl

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

U-FRACTURE : 𝒞-FRAC → 𝒱-FRACTURE
U-FRACTURE F =
  record
    { X• = U• (F .A•)
    ; X◦ = U◦ (F .A◦)
    ; χ• = F .α• .U
    }

record 𝒞-Square (A B : 𝒞-FRAC) : 𝒱 where
  field
    f• : ⟨ A .A• ⟩ᶜ ⊸ ⟨ B .A• ⟩ᶜ
    f◦ : ⟨ A .A◦ ⟩ᶜ ⊸ ⟨ B .A◦ ⟩ᶜ
    f-coh : (a• : U ⟨ A .A• ⟩ᶜ) → B .α• .U (f• .U a•) ≡ ●ᶜ.map f◦ .U (A .α• .U a•)

squareᶜ
  : ∀ {A• A◦ α B• B◦ β}
  → (f• : ⟨ A• ⟩ᶜ ⊸ ⟨ B• ⟩ᶜ)
  → (f◦ : ⟨ A◦ ⟩ᶜ ⊸ ⟨ B◦ ⟩ᶜ)
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
    (λ i → ●ᶜ ⟨ B◦ ⟩ᶜ .is-set
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

⊸-Glueᶜ-≃ : {A : 𝒞} {F : 𝒞-FRAC}
  → (A ⊸ 𝒞-fromFRAC F)
  ≃ (Σ[ (h◦ , h•) ∈ (A ⊸ ⟨ F .A◦ ⟩ᶜ) × (A ⊸ ⟨ F .A• ⟩ᶜ) ]
      (h◦ ⨾ᶜ η•ᶜ ≡ h• ⨾ᶜ F .α•))
⊸-Glueᶜ-≃ {A} {F} = isoToEquiv (iso fwd bwd sec ret)
  where
    fwd : (A ⊸ 𝒞-fromFRAC F)
      → Σ[ (h◦ , h•) ∈ (A ⊸ ⟨ F .A◦ ⟩ᶜ) × (A ⊸ ⟨ F .A• ⟩ᶜ) ]
          (h◦ ⨾ᶜ η•ᶜ ≡ h• ⨾ᶜ F .α•)
    fwd k = (k ⨾ᶜ proj◦ᶜ F , k ⨾ᶜ proj•ᶜ F) ,
      ⊸-path refl refl (funExt λ a → sym (k .U a .•→◦))

    bwd : (Σ[ (h◦ , h•) ∈ (A ⊸ ⟨ F .A◦ ⟩ᶜ) × (A ⊸ ⟨ F .A• ⟩ᶜ) ]
            (h◦ ⨾ᶜ η•ᶜ ≡ h• ⨾ᶜ F .α•))
      → (A ⊸ 𝒞-fromFRAC F)
    bwd ((h◦ , h•) , coh) .U a .• = h• .U a
    bwd ((h◦ , h•) , coh) .U a .◦ = h◦ .U a
    bwd ((h◦ , h•) , coh) .U a .•→◦ = sym (funExt⁻ (cong (λ w → w .U) coh) a)
    bwd ((h◦ , h•) , coh) .charge c a i .• = h• .charge c a i
    bwd ((h◦ , h•) , coh) .charge c a i .◦ = h◦ .charge c a i
    bwd ((h◦ , h•) , coh) .charge c a i .•→◦ =
      isProp→PathP
        (λ i → ●ᶜ ⟨ F .A◦ ⟩ᶜ .is-set
          (F .α• .U (h• .charge c a i))
          (η• (h◦ .charge c a i)))
        _ _ i

    sec : section fwd bwd
    sec ((h◦ , h•) , coh) =
      Σ≡Prop (λ _ → isSet⊸ _ _)
        (ΣPathP (⊸-path refl refl refl , ⊸-path refl refl refl))

    ret : retract fwd bwd
    ret k = ⊸-path refl refl (funExt λ a i → record
      { • = k .U a .•
      ; ◦ = k .U a .◦
      ; •→◦ = ●ᶜ ⟨ F .A◦ ⟩ᶜ .is-set _ _
          (bwd (fwd k) .U a .•→◦)
          (k .U a .•→◦)
          i
      })

Squareᶜ-pullback-≃ : {F G : 𝒞-FRAC}
  → 𝒞-Square F G
  ≃ (Σ[ (f◦ , f•) ∈ (⟨ F .A◦ ⟩ᶜ ⊸ ⟨ G .A◦ ⟩ᶜ) × (⟨ F .A• ⟩ᶜ ⊸ ⟨ G .A• ⟩ᶜ) ]
      (F .α• ⨾ᶜ ●ᶜ.map f◦ ≡ f• ⨾ᶜ G .α•))
Squareᶜ-pullback-≃ {F} {G} = isoToEquiv (iso fwd bwd sec ret)
  where
    fwd : 𝒞-Square F G
      → Σ[ (f◦ , f•) ∈ (⟨ F .A◦ ⟩ᶜ ⊸ ⟨ G .A◦ ⟩ᶜ) × (⟨ F .A• ⟩ᶜ ⊸ ⟨ G .A• ⟩ᶜ) ]
          (F .α• ⨾ᶜ ●ᶜ.map f◦ ≡ f• ⨾ᶜ G .α•)
    fwd S = (S .𝒞-Square.f◦ , S .𝒞-Square.f•) ,
      ⊸-path refl refl (funExt λ a• → sym (S .𝒞-Square.f-coh a•))

    bwd : (Σ[ (f◦ , f•) ∈ (⟨ F .A◦ ⟩ᶜ ⊸ ⟨ G .A◦ ⟩ᶜ) × (⟨ F .A• ⟩ᶜ ⊸ ⟨ G .A• ⟩ᶜ) ]
            (F .α• ⨾ᶜ ●ᶜ.map f◦ ≡ f• ⨾ᶜ G .α•))
      → 𝒞-Square F G
    bwd ((f◦ , f•) , coh) = record
      { f• = f•
      ; f◦ = f◦
      ; f-coh = λ a• → sym (funExt⁻ (cong (λ w → w .U) coh) a•)
      }

    sec : section fwd bwd
    sec w = Σ≡Prop (λ _ → isSet⊸ _ _) refl

    ret : retract fwd bwd
    ret S i = record
      { f• = S .𝒞-Square.f•
      ; f◦ = S .𝒞-Square.f◦
      ; f-coh =
          isPropΠ (λ a• → ●ᶜ ⟨ G .A◦ ⟩ᶜ .is-set _ _)
            (bwd (fwd S) .𝒞-Square.f-coh)
            (S .𝒞-Square.f-coh)
            i
      }
