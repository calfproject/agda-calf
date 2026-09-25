module Calf.Value.Glue.Fracture where

open import Cubical.Foundations.Equiv.Properties using (congEquiv)
open import Cubical.Foundations.Path
open import Cubical.Foundations.Univalence using (ua; ua→; ua-gluePath)
open import Cubical.Data.Sigma
open import Cubical.Functions.FunExtEquiv using (funExtEquiv)

open import Calf.Core.Abstract
open import Calf.Value
open import Calf.Value.Closed as ●
open import Calf.Value.Open as ◯

open import Calf.Value.Glue.Base

module _ where
  open Fracture

  FractureGlue : 𝒱 → 𝒱
  FractureGlue = fromFracture ∘ toFracture

  fracture : X → FractureGlue X
  fracture x = (η• x , η◦ x) , refl

  fracture-modal : ●.isModalMap (fracture {X})
  fracture-modal {X} g =
    ●.isModal-≃ (invEquiv e) $
    ●.isModalΣ (isConnected◯→isModal● (◯.isConnectedMapη _)) λ _ →
    ●.isModalPathP $ ●.isModalΣ ●.isModal● λ _ → ●-≡-isModal _ _
    where
      e : _
      e =
        Σ-cong-equiv-snd (λ _ →
          congEquiv (Σ-cong-equiv-fst Σ-swap-≃ ∙ₑ Σ-assoc-≃)
          ∙ₑ invEquiv ΣPath≃PathΣ)
        ∙ₑ invEquiv Σ-assoc-≃

  fracture-connected : ●.isConnectedMap (fracture {X})
  fracture-connected {X} g =
    ●.isConnected-≃ (invEquiv e) $
    ●.isConnectedΣ (●.isConnectedMapη _) λ _ →
    ●.isConnectedPathP isLex● $ ●.isConnectedMapη _
    where
      e : _
      e =
        Σ-cong-equiv-snd (λ _ →
          congEquiv
            (Σ-cong-equiv-snd (λ _ → isoToEquiv symIso) ∙ₑ Σ-assoc-≃)
          ∙ₑ invEquiv ΣPath≃PathΣ)
        ∙ₑ invEquiv Σ-assoc-≃

  fracture-isEquiv : isEquiv (fracture {X})
  fracture-isEquiv = ●.isModal+isConnected→isEquiv fracture-modal fracture-connected

  -- This proof is a direct adaptation of https://agda.monade.li/ErasureOpen.html
  glue-fracture-retract : retract toFracture fromFracture
  glue-fracture-retract X = sym (ua (fracture , fracture-isEquiv))

  glue•-equiv : (F : Fracture) → ● (fromFracture F) ≃ ⟨ F .X• ⟩
  glue•-equiv F =
      ● (Glue ⟨ F .X• ⟩ ⟨ F .X◦ ⟩ (F .χ•))
    ≃⟨ ●-pullback ⟩
      (Σ[ (x•• , x◦•) ∈ ● ⟨ F .X• ⟩ × ● ⟨ F .X◦ ⟩ ] ●.map (F .χ•) x•• ≡ ●.map η• x◦•)
    ≃⟨ Σ-assoc-≃ ⟩
      (Σ[ x•• ∈ ● ⟨ F .X• ⟩ ] Σ[ x◦• ∈ ● ⟨ F .X◦ ⟩ ] ●.map (F .χ•) x•• ≡ ●.map η• x◦•)
    ≃⟨ Σ-cong-equiv-snd (λ _ → Σ-cong-equiv-fst (_ , ●.map-η-isEquiv)) ⟩
      (Σ[ x•• ∈ ● ⟨ F .X• ⟩ ] Σ[ x◦•• ∈ ● (● ⟨ F .X◦ ⟩) ] ●.map (F .χ•) x•• ≡ x◦••)
    ≃⟨ Σ-contractSnd (λ _ → isContrSingl _) ⟩
      ● ⟨ F .X• ⟩
    ≃⟨ invEquiv (η• , str (F .X•)) ⟩
      ⟨ F .X• ⟩
    ■

  Glue-open-≃ : (F : Fracture) → ⟨ ABS ⟩ → fromFracture F ≃ ⟨ F .X◦ ⟩
  Glue-open-≃ F abs =
      Σ[ (x• , x◦) ∈ ⟨ F .X• ⟩ × ⟨ F .X◦ ⟩ ] F .χ• x• ≡ η• x◦
    ≃⟨ Σ-contractSnd (λ _ → isContr→isContrPath (◯-isConnected abs) _ _) ⟩
      ⟨ F .X• ⟩ × ⟨ F .X◦ ⟩
    ≃⟨ Σ-contractFst (isConnected→◯isContr (isModal●→isConnected◯ (str (F .X•))) abs) ⟩
      ⟨ F .X◦ ⟩
    ■

  glue◦-equiv : (F : Fracture) → ◯ (fromFracture F) ≃ ⟨ F .X◦ ⟩
  glue◦-equiv F =
      ◯ (Glue ⟨ F .X• ⟩ ⟨ F .X◦ ⟩ (F .χ•))
    ≃⟨ ◯-pullback ⟩
      (Σ[ (x•◦ , x◦◦) ∈ ◯ ⟨ F .X• ⟩ × ◯ ⟨ F .X◦ ⟩ ] ◯.map (F .χ•) x•◦ ≡ ◯.map η• x◦◦)
    ≃⟨ Σ-contractSnd (λ _ → isContr→isContrPath (isModal●→isConnected◯ isModal●) _ _) ⟩
      ◯ ⟨ F .X• ⟩ × ◯ ⟨ F .X◦ ⟩
    ≃⟨ Σ-contractFst (isModal●→isConnected◯ (str (F .X•))) ⟩
      ◯ ⟨ F .X◦ ⟩
    ≃⟨ invEquiv (η◦ , str (F .X◦)) ⟩
      ⟨ F .X◦ ⟩
    ■

--   glue•-β : (F : Fracture) (g : fromFracture F)
--     → equivFun (glue•-equiv F) (η• g) ≡ • g
--   glue•-β F = ●.elim-β (λ _ → F .X• .snd) (λ g → • g)

--   glue◦-β : (F : Fracture) (g : fromFracture F)
--     → equivFun (glue◦-equiv F) (η◦ g) ≡ ◦ g
--   glue◦-β F = ◯.elim-β (λ _ → F .X◦ .snd) (λ g → ◦ g)

--   opaque
--     square-χ•-path : {F G : Fracture}
--       → (h : fromFracture F → fromFracture G)
--       → (k : ⟨ F .X• ⟩ → ● ⟨ G .X◦ ⟩)
--       → ((g : fromFracture F) → η• (◦ (h g)) ≡ k (• g))
--       → PathP (λ i → ua (glue•-equiv F) i → ● (ua (glue◦-equiv G) i))
--           (●.map (η◦ ∘ h))
--           k
--     square-χ•-path {F} {G} h k coh =
--       ua→ (●.elim (λ _ → ●.isModalPathP ●.isModal●) λ g →
--         congP (λ _ → η•) (ua-gluePath (glue◦-equiv G) (glue◦-β G (h g)))
--         ▷ (coh g ∙ cong k (sym (glue•-β F g))))

--   glue-fracture-χ•-path : (F : Fracture)
--     → PathP (λ i → ua (glue•-equiv F) i → ● (ua (glue◦-equiv F) i))
--         (●.map η◦)
--         (F .χ•)
--   glue-fracture-χ•-path F = square-χ•-path (λ g → g) (F .χ•) (λ g → sym (•→◦ g))

  glue-fracture-section : section toFracture fromFracture
  glue-fracture-section F =
    Fracture-path
      (𝒱•-path (ua (glue•-equiv F)))
      (𝒱◦-path (ua (glue◦-equiv F)))
      {!   !}
      -- (glue-fracture-χ•-path F)

  fracture-and-gluing : 𝒱 ≃ Fracture
  fracture-and-gluing =
    isoToEquiv (iso toFracture fromFracture glue-fracture-section glue-fracture-retract)

module _ where
  fracture-and-gluing-square : (X → Y) ≃ Fracture-Square (toFracture X) (toFracture Y)
  fracture-and-gluing-square {X} {Y} =
      (X → Y)
    ≃⟨ equivΠCod (λ _ → fracture , fracture-isEquiv) ⟩
      (X → FractureGlue Y)
    ≃⟨ Σ-Π-≃ ⟩
      (Σ[ f ∈ (X → ● Y × ◯ Y) ] ((x : X) → ●.map η◦ (f x .fst) ≡ η• (f x .snd)))
    ≃⟨ Σ-cong-equiv-fst Σ-Π-≃ ⟩
      (Σ[ (f• , f◦) ∈ (X → ● Y) × (X → ◯ Y) ] ((x : X) → ●.map η◦ (f• x) ≡ η• (f◦ x)))
    ≃⟨ Σ-cong-equiv-snd (λ _ → funExtEquiv) ⟩
      (Σ[ (f• , f◦) ∈ (X → ● Y) × (X → ◯ Y) ] (●.map η◦ ∘ f• ≡ η• ∘ f◦))
    ≃⟨
      invEquiv
        (Σ-cong-equiv
          (≃-× (●.precomp-η-≃ ●.isModal●) (◯.precomp-η-≃ ◯.isModal◯))
          (λ (f• , f◦) → congEquiv (●.precomp-η-≃ ●.isModal●)))
    ⟩
      Fracture-Square (toFracture X) (toFracture Y)
    ■

  toSquare : (X → Y) → Fracture-Square (toFracture X) (toFracture Y)
  toSquare = equivFun fracture-and-gluing-square
