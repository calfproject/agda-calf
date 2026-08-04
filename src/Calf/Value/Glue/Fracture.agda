open import Cubical.Foundations.Prelude

module Calf.Value.Glue.Fracture where

open import Calf.Core.Abstract
open import Calf.Value
open import Calf.Value.Open as ◯
open import Calf.Value.Closed as ●

open import Calf.Value.Glue.Base

open import Cubical.Data.Sigma
open import Cubical.Foundations.GroupoidLaws using (symInvo; rUnit)
open import Cubical.Foundations.Path
open import Cubical.Foundations.Univalence using (ua; ua→; ua-gluePath; pathToEquiv)
open import Cubical.Foundations.Equiv.Properties using (congEquiv)
open import Cubical.Functions.FunExtEquiv using (funExtEquiv)
open import Cubical.Modalities.Modality

module _ where
  open 𝒱-FRACTURE

  FractureGlue : 𝒱 → 𝒱
  FractureGlue = 𝒱-Glue ∘ 𝒱-Fracture

  fracture : X → FractureGlue X
  fracture x .• = η• x
  fracture x .◦ = η◦ x
  fracture x .•→◦ = refl

  fracture-modal : ●.isModalMap (fracture {X})
  fracture-modal {X} g =
    subst ●.isModal (sym (ua e)) $
    ●.isModalΣ (isConnected◯→isModal● (◯.isConnectedMapη _)) λ _ →
    ●.isModalPathP $ ●.isModalΣ ●.isModal● λ _ → ●-≡-isModal _ _
    where
      e : _
      e =
        Σ-cong-equiv-snd (λ _ →
          congEquiv (Glue-pullback-≃ ∙ₑ Σ-assoc-≃)
          ∙ₑ invEquiv ΣPath≃PathΣ)
        ∙ₑ invEquiv Σ-assoc-≃

  fracture-connected : ●.isConnectedMap (fracture {X})
  fracture-connected {X} g =
    subst ●.isConnected (sym (ua e)) $
    ●.isConnectedΣ (●.isConnectedMapη _) λ _ →
    ●.isConnectedPathP isLex● $ ●.isConnectedMapη _
    where
      e : _
      e =
        Σ-cong-equiv-snd (λ _ →
          congEquiv
            (Glue-pullback-≃ ∙ₑ Σ-cong-equiv-fst Σ-swap-≃ ∙ₑ Σ-assoc-≃)
          ∙ₑ invEquiv ΣPath≃PathΣ)
        ∙ₑ invEquiv Σ-assoc-≃

  fracture-isEquiv : isEquiv (fracture {X})
  fracture-isEquiv = ●.isModal+isConnected→isEquiv fracture-modal fracture-connected

  -- This proof is a direct adaptation of https://agda.monade.li/ErasureOpen.html
  glue-fracture-retract : retract 𝒱-Fracture 𝒱-Glue
  glue-fracture-retract X = sym (ua (fracture , fracture-isEquiv))

  opaque
    proj•-connected-contract : (F : 𝒱-FRACTURE)
      → ●.isConnectedMap (λ (g : 𝒱-Glue F) → g .•)
    proj•-connected-contract F x• =
      ●.isConnected-≃
        (invEquiv
          ( Σ-cong-equiv-fst Glue-pullback-≃
          ∙ₑ invEquiv (Σ-cong-equiv-fst (Σ-cong-equiv-fst Σ-swap-≃))
          ∙ₑ Σ-cong-equiv-fst Σ-assoc-≃
          ∙ₑ invEquiv (fiberProjEquiv _ _ x•)))
        (●.isConnectedMapη (F .χ• x•))

  proj•-connected : (F : 𝒱-FRACTURE) → ●.isConnectedMap (λ (g : 𝒱-Glue F) → g .•)
  proj•-connected F x• .fst =
    ●.map (λ (x◦ , p) → record { • = x• ; ◦ = x◦ ; •→◦ = sym p } , refl)
      (●.isConnectedMapη (F .χ• x•) .fst)
  proj•-connected F x• .snd =
    isContr→isProp (proj•-connected-contract F x•) _

  opaque
    proj◦-connected-contract : (F : 𝒱-FRACTURE)
      → ◯.isConnectedMap (λ (g : 𝒱-Glue F) → g .◦)
    proj◦-connected-contract F x◦ =
      ◯.isConnected-≃
        (invEquiv
          ( Σ-cong-equiv-fst Glue-pullback-≃
          ∙ₑ Σ-cong-equiv-fst Σ-assoc-≃
          ∙ₑ invEquiv (fiberProjEquiv _ _ x◦)))
        (isModal●→isConnected◯
          (●.isModalΣ (F .X• .snd) λ x• → ●-≡-isModal _ _))

  proj◦-connected : (F : 𝒱-FRACTURE) → ◯.isConnectedMap (λ (g : 𝒱-Glue F) → g .◦)
  proj◦-connected F x◦ .fst abs =
    record
      { • = invIsEq (F .X• .snd) (∗ abs)
      ; ◦ = x◦
      ; •→◦ = ◯-isProp● abs (F .χ• (invIsEq (F .X• .snd) (∗ abs))) (η• x◦)
      } , refl
  proj◦-connected F x◦ .snd =
    isContr→isProp (proj◦-connected-contract F x◦) _

  glue•-out : (F : 𝒱-FRACTURE) → ● (𝒱-Glue F) → ⟨ F .X• ⟩
  glue•-out F = ●.elim (λ _ → F .X• .snd) (λ g → g .•)

  glue•-in : (F : 𝒱-FRACTURE) → ⟨ F .X• ⟩ → ● (𝒱-Glue F)
  glue•-in F = ●.reflection-inv (F .X• .snd) (proj•-connected F)

  glue•-equiv : (F : 𝒱-FRACTURE) → ● (𝒱-Glue F) ≃ ⟨ F .X• ⟩
  glue•-equiv F =
    isoToEquiv
      (iso (glue•-out F) (glue•-in F)
        (●.reflection-sec (F .X• .snd) (proj•-connected F))
        (●.reflection-ret (F .X• .snd) (proj•-connected F)))

  glue◦-out : (F : 𝒱-FRACTURE) → ◯ (𝒱-Glue F) → ⟨ F .X◦ ⟩
  glue◦-out F = ◯.elim (λ _ → F .X◦ .snd) (λ g → g .◦)

  glue◦-in : (F : 𝒱-FRACTURE) → ⟨ F .X◦ ⟩ → ◯ (𝒱-Glue F)
  glue◦-in F = ◯.reflection-inv (F .X◦ .snd) (proj◦-connected F)

  glue◦-equiv : (F : 𝒱-FRACTURE) → ◯ (𝒱-Glue F) ≃ ⟨ F .X◦ ⟩
  glue◦-equiv F =
    isoToEquiv
      (iso (glue◦-out F) (glue◦-in F)
        (◯.reflection-sec (F .X◦ .snd) (proj◦-connected F))
        (◯.reflection-ret (F .X◦ .snd) (proj◦-connected F)))

  glue•-β : (F : 𝒱-FRACTURE) (g : 𝒱-Glue F)
    → equivFun (glue•-equiv F) (η• g) ≡ g .•
  glue•-β F = ●.reflection-β (F .X• .snd) (proj•-connected F)

  glue◦-β : (F : 𝒱-FRACTURE) (g : 𝒱-Glue F)
    → equivFun (glue◦-equiv F) (η◦ g) ≡ g .◦
  glue◦-β F = ◯.reflection-β (F .X◦ .snd) (proj◦-connected F)

  opaque
    glue-χ-path : (F : 𝒱-FRACTURE) (g• : ● (𝒱-Glue F))
      → PathP (λ i → ● (ua (glue◦-equiv F) i))
          (●.map η◦ g•)
          (F .χ• (equivFun (glue•-equiv F) g•))
    glue-χ-path F =
      ●.elim (λ g• → ●.isModalPathP ●.isModal●) λ g →
        congP (λ _ → η•) (◯.reflection-ua-gluePath (F .X◦ .snd) (proj◦-connected F) g)
        ▷ ( sym (g .•→◦)
          ∙ cong (F .χ•) (sym (●.reflection-β (F .X• .snd) (proj•-connected F) g)))

  opaque
    glue-fracture-χ•-path : (F : 𝒱-FRACTURE)
      → PathP (λ i → ua (glue•-equiv F) i → ● (ua (glue◦-equiv F) i))
          (●.map η◦)
          (F .χ•)
    glue-fracture-χ•-path F =
      ua→ {e = glue•-equiv F} {B = λ i → ● (ua (glue◦-equiv F) i)}
        {f₀ = ●.map η◦} {f₁ = F .χ•}
        (glue-χ-path F)

  glue-fracture-section : section 𝒱-Fracture 𝒱-Glue
  glue-fracture-section F i .X• =
    𝒱•-path (●• (𝒱-Glue F)) (F .X•) (ua (glue•-equiv F)) i
  glue-fracture-section F i .X◦ =
    𝒱◦-path (◯◦ (𝒱-Glue F)) (F .X◦) (ua (glue◦-equiv F)) i
  glue-fracture-section F i .χ• = glue-fracture-χ•-path F i

  fracture-and-gluing : 𝒱 ≃ 𝒱-FRACTURE
  fracture-and-gluing =
    isoToEquiv (iso 𝒱-Fracture 𝒱-Glue glue-fracture-section glue-fracture-retract)


module _ where
  toSquare : (X → Y) → 𝒱-Square (𝒱-Fracture X) (𝒱-Fracture Y)
  toSquare f .𝒱-Square.f• = ●.map f
  toSquare f .𝒱-Square.f◦ = ◯.map f
  toSquare f .𝒱-Square.f-coh = ●.elim (λ x• → ●-≡-isModal _ _) (λ _ → refl)

  fracture-and-gluing-square : (X → Y) ≃ 𝒱-Square (𝒱-Fracture X) (𝒱-Fracture Y)
  fracture-and-gluing-square {X} {Y} =
      (X → Y)
    ≃⟨ equivΠCod (λ _ → fracture , fracture-isEquiv) ⟩
      (X → FractureGlue Y)
    ≃⟨ equivΠCod (λ _ → Glue-pullback-≃) ⟩
      (X → Σ[ (x◦ , x•) ∈ ◯ Y × ● Y ] (η• x◦ ≡ ●.map η◦ x•))
    ≃⟨ isoToEquiv Σ-Π-Iso ⟩
      (Σ[ h ∈ (X → ◯ Y × ● Y) ] ((x : X) → η• (h x .fst) ≡ ●.map η◦ (h x .snd)))
    ≃⟨ Σ-cong-equiv-fst (isoToEquiv Σ-Π-Iso) ⟩
      (Σ[ (h◦ , h•) ∈ (X → ◯ Y) × (X → ● Y) ]
        ((x : X) → η• (h◦ x) ≡ ●.map η◦ (h• x)))
    ≃⟨ Σ-cong-equiv-snd (λ _ → funExtEquiv) ⟩
      (Σ[ (h◦ , h•) ∈ (X → ◯ Y) × (X → ● Y) ] (η• ∘ h◦ ≡ ●.map η◦ ∘ h•))
    ≃⟨ invEquiv (Σ-cong-equiv (≃-× precomp◦ precomp•)
         (λ (f◦ , f•) → congEquiv precomp•●◯)) ⟩
      (Σ[ (f◦ , f•) ∈ (◯ X → ◯ Y) × (● X → ● Y) ]
        (●.map f◦ ∘ ●.map η◦ ≡ ●.map η◦ ∘ f•))
    ≃⟨ invEquiv Square-pullback-≃ ⟩
      𝒱-Square (𝒱-Fracture X) (𝒱-Fracture Y)
    ■
    where
      precomp◦ : (◯ X → ◯ Y) ≃ (X → ◯ Y)
      precomp◦ = ◯.precomp-η-≃ ◯.isModal◯

      precomp• : (● X → ● Y) ≃ (X → ● Y)
      precomp• = ●.precomp-η-≃ ●.isModal●

      precomp•●◯ : (● X → ● (◯ Y)) ≃ (X → ● (◯ Y))
      precomp•●◯ = ●.precomp-η-≃ ●.isModal●
