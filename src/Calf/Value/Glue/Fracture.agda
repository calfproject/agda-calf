module Calf.Value.Glue.Fracture where

open import Cubical.Foundations.Equiv.Properties using (congEquiv)
open import Cubical.Foundations.Path
open import Cubical.Foundations.Univalence using (ua)
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

  glue•-β : (F : Fracture) (g : fromFracture F)
    → equivFun (glue•-equiv F) (η• g) ≡ • g
  glue•-β F g =
      equivFun (glue•-equiv F) (η• g)
    ≡⟨ cong (invIsEq (str (F .X•))) (●-pullback-β₁ g) ⟩
      invIsEq (str (F .X•)) (η• (• g))
    ≡⟨ retIsEq (str (F .X•)) (• g) ⟩
      • g
    ∎

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

  glue◦-β : (F : Fracture) (g : fromFracture F)
    → equivFun (glue◦-equiv F) (η◦ g) ≡ ◦ g
  glue◦-β F g =
      equivFun (glue◦-equiv F) (η◦ g)
    ≡⟨ cong (invIsEq (str (F .X◦))) (transportRefl _) ⟩
      invIsEq (str (F .X◦)) (equivFun ◯-pullback (η◦ g) .fst .snd)
    ≡⟨ cong (invIsEq (str (F .X◦))) (◯-pullback-β₂ g) ⟩
      invIsEq (str (F .X◦)) (η◦ (◦ g))
    ≡⟨ retIsEq (str (F .X◦)) (◦ g) ⟩
      ◦ g
    ∎

  glue-fracture-section : section toFracture fromFracture
  glue-fracture-section F =
    Fracture-ua (glue•-equiv F) (glue◦-equiv F) $
    ●.η-ext (λ _ → ●.isModal●) $ funExt λ x →
      cong (F .χ•) (glue•-β F x) ∙ •→◦ x ∙ cong η• (sym (glue◦-β F x))

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
