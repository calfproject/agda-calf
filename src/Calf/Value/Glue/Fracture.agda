-- This proof is largely due to https://agda.monade.li/ErasureOpen.html
module Calf.Value.Glue.Fracture where

open import Calf.Core.Abstract
open import Calf.Value
open import Calf.Value.Open as ◯
open import Calf.Value.Closed as ●
open import Calf.Value.Glue.Base

open import Cubical.Data.Sigma
open import Cubical.Foundations.GroupoidLaws using (symInvo)
open import Cubical.Foundations.Path
open import Cubical.Foundations.Univalence using (ua; ua→; ua-gluePath)

open 𝒱-FRAC

module _ where
  glue•-in : (F : 𝒱-FRAC) → ⟨ F .X• ⟩ → ● (fromFRAC F)
  glue•-in F x• =
    ●.map
      (λ (x◦ , p) →
        record
          { • = x•
          ; ◦ = x◦
          ; •→◦ = sym p
          })
      (η-fiber (F .χ• x•))

  glue•-out : (F : 𝒱-FRAC) → ● (fromFRAC F) → ⟨ F .X• ⟩
  glue•-out F g• = invIsEq (F .X• .snd) (●.map (λ g → g .•) g•)

  glue•-in-proj : (F : 𝒱-FRAC) (x• : ⟨ F .X• ⟩) →
    ●.map (λ g → g .•) (glue•-in F x•) ≡ η• x•
  glue•-in-proj F x• =
    ●.map-∘
      (λ (x◦ , p) →
        record
          { • = x•
          ; ◦ = x◦
          ; •→◦ = sym p
          })
      (λ g → g .•)
      (η-fiber (F .χ• x•))
    ∙ ●-map-const x• (η-fiber (F .χ• x•))

  glue•-rightInv : (F : 𝒱-FRAC) → section (glue•-out F) (glue•-in F)
  glue•-rightInv F x• =
    cong (invIsEq (F .X• .snd)) (glue•-in-proj F x•)
    ∙ retIsEq (F .X• .snd) x•

  glue•-in-point : (F : 𝒱-FRAC) (x• : ⟨ F .X• ⟩) (x◦ : ⟨ F .X◦ ⟩)
    (h : F .χ• x• ≡ η• x◦) →
    glue•-in F x• ≡
      η• (record { • = x• ; ◦ = x◦ ; •→◦ = h })
  glue•-in-point F x• x◦ h =
    cong
      (●.map
        (λ (x◦ , p) →
          record
            { • = x•
            ; ◦ = x◦
            ; •→◦ = sym p
            }))
      (η-fiber-point (F .χ• x•) (x◦ , sym h))
    ∙ cong η• (λ i → record { • = x• ; ◦ = x◦ ; •→◦ = symInvo h (~ i) })

  glue•-leftInv : (F : 𝒱-FRAC) → retract (glue•-out F) (glue•-in F)
  glue•-leftInv F = ind R η•-case ∗-case law-case
    where
      R : ● (fromFRAC F) → 𝒱
      R g• = glue•-in F (glue•-out F g•) ≡ g•

      η•-case : (g : fromFRAC F) → R (η• g)
      η•-case g =
        cong (glue•-in F) (retIsEq (F .X• .snd) (g .•))
        ∙ glue•-in-point F (g .•) (g .◦) (g .•→◦)

      ∗-case : (abs : ⟨ ABS ⟩) → R (∗ abs)
      ∗-case abs = ●-path-to-star abs (glue•-in F (glue•-out F (∗ abs)))

      law-case : (g : fromFRAC F) (abs : ⟨ ABS ⟩) → PathP (λ i → R (law g abs i)) (η•-case g) (∗-case abs)
      law-case g abs =
        isProp→PathP
          (λ i → isProp→isSet (●-isProp abs)
            (glue•-in F (glue•-out F (law g abs i)))
            (law g abs i))
          (η•-case g)
          (∗-case abs)

  glue•-equiv : (F : 𝒱-FRAC) → ● (fromFRAC F) ≃ ⟨ F .X• ⟩
  glue•-equiv F = isoToEquiv (iso (glue•-out F) (glue•-in F) (glue•-rightInv F) (glue•-leftInv F))

  glue•-in-isEquiv : (F : 𝒱-FRAC) → isEquiv (glue•-in F)
  glue•-in-isEquiv F =
    isoToIsEquiv (iso (glue•-in F) (glue•-out F) (glue•-leftInv F) (glue•-rightInv F))

  glue•-path : (F : 𝒱-FRAC) → (● (fromFRAC F) , ●.η-isEquiv) ≡ F .X•
  glue•-path F = Σ≡Prop (λ X → isPropIsEquiv (η• {X})) (ua (glue•-equiv F))


module _ where
  glue◦-fiber : (F : 𝒱-FRAC) (x◦ : ⟨ F .X◦ ⟩) →
    ◯ (Σ[ g ∈ fromFRAC F ] g .◦ ≡ x◦)
  glue◦-fiber F x◦ p =
    (record
      { • = 𝒱•-at-open-isContr (F .X•) p .fst
      ; ◦ = x◦
      ; •→◦ = ●-isProp p (F .χ• (𝒱•-at-open-isContr (F .X•) p .fst)) (η• x◦)
      })
    , refl

  glue◦-in : (F : 𝒱-FRAC) → ⟨ F .X◦ ⟩ → ◯ (fromFRAC F)
  glue◦-in F x◦ p = glue◦-fiber F x◦ p .fst

  glue◦-out : (F : 𝒱-FRAC) → ◯ (fromFRAC F) → ⟨ F .X◦ ⟩
  glue◦-out F g◦ = invIsEq (F .X◦ .snd) (◯.map (λ g → g .◦) g◦)

  glue◦-rightInv : (F : 𝒱-FRAC) → section (glue◦-out F) (glue◦-in F)
  glue◦-rightInv F x◦ = retIsEq (F .X◦ .snd) x◦

  glue◦-leftInv : (F : 𝒱-FRAC) → retract (glue◦-out F) (glue◦-in F)
  glue◦-leftInv F g◦ = funExt λ p → λ i →
    record
      { • = closed-path p i
      ; ◦ = open-path p i
      ; •→◦ = proof-path p i
      }
    where
      closed-path : (abs : ⟨ ABS ⟩) →
        𝒱•-at-open-isContr (F .X•) abs .fst ≡ g◦ abs .•
      closed-path abs = 𝒱•-at-open-isContr (F .X•) abs .snd (g◦ abs .•)

      open-path : (abs : ⟨ ABS ⟩) → glue◦-out F g◦ ≡ g◦ abs .◦
      open-path abs = funExt⁻ (secIsEq (F .X◦ .snd) (◯.map (λ g → g .◦) g◦)) abs

      proof-path : (abs : ⟨ ABS ⟩) →
        PathP
          (λ i → F .χ• (closed-path abs i) ≡ η• (open-path abs i))
          (●-isProp abs (F .χ• (𝒱•-at-open-isContr (F .X•) abs .fst)) (η• (glue◦-out F g◦)))
          (g◦ abs .•→◦)
      proof-path p =
        isProp→PathP
          (λ i → isProp→isSet (●-isProp p)
            (F .χ• (closed-path p i))
            (η• (open-path p i)))
          (●-isProp p (F .χ• (𝒱•-at-open-isContr (F .X•) p .fst)) (η• (glue◦-out F g◦)))
          (g◦ p .•→◦)

  glue◦-equiv : (F : 𝒱-FRAC) → ◯ (fromFRAC F) ≃ ⟨ F .X◦ ⟩
  glue◦-equiv F = isoToEquiv (iso (glue◦-out F) (glue◦-in F) (glue◦-rightInv F) (glue◦-leftInv F))

  glue◦-path : (F : 𝒱-FRAC) → (◯ (fromFRAC F) , ◯.η-isEquiv) ≡ F .X◦
  glue◦-path F = Σ≡Prop (λ X → isPropIsEquiv (η◦ {X})) (ua (glue◦-equiv F))

glue-χ-path-base : (F : 𝒱-FRAC) (g• : ● (fromFRAC F)) →
  PathP
    (λ i → ● ⟨ glue◦-path F i ⟩)
    (●.map η◦ g•)
    (F .χ• (glue•-out F g•))
glue-χ-path-base F = ind R η•-case ∗-case law-case
  where
    B : I → 𝒱
    B i = ● ⟨ glue◦-path F i ⟩

    R : ● (fromFRAC F) → 𝒱
    R g• = PathP B (●.map η◦ g•) (F .χ• (glue•-out F g•))

    η•-case : (g : fromFRAC F) → R (η• g)
    η•-case g = toPathP (fromPathP closed-open-step ∙ endpoint-step)
      where
        open-step : PathP (λ i → ⟨ glue◦-path F i ⟩) (η◦ g) (glue◦-out F (η◦ g))
        open-step = ua-gluePath (glue◦-equiv F) refl

        closed-open-step : PathP B (η• (η◦ g)) (η• (glue◦-out F (η◦ g)))
        closed-open-step i = η• (open-step i)

        endpoint-step : η• (glue◦-out F (η◦ g)) ≡ F .χ• (glue•-out F (η• g))
        endpoint-step =
          cong η• (retIsEq (F .X◦ .snd) (g .◦))
          ∙ sym (g .•→◦)
          ∙ sym (cong (F .χ•) (retIsEq (F .X• .snd) (g .•)))

    ∗-case : (abs : ⟨ ABS ⟩) → R (∗ abs)
    ∗-case abs =
      toPathP (fromPathP (sym (●-path-to-star abs (F .χ• (glue•-out F (∗ abs))))))

    law-case : (g : fromFRAC F) (abs : ⟨ ABS ⟩) → PathP (λ i → R (law g abs i)) (η•-case g) (∗-case abs)
    law-case g abs =
      isProp→PathP
        (λ i → isProp→isPropPathP (λ _ → ●-isProp abs)
          (●.map η◦ (law g abs i))
          (F .χ• (glue•-out F (law g abs i))))
        (η•-case g)
        (∗-case abs)

FractureGlue : 𝒱 → 𝒱
FractureGlue = fromFRAC ∘ toFRAC

fracture : {X : 𝒱} → X → FractureGlue X
fracture x .• = η• x
fracture x .◦ = η◦ x
fracture x .•→◦ = refl

fracture-open-path : {X : 𝒱} (abs : ⟨ ABS ⟩) (g : FractureGlue X) → fracture (g .◦ abs) ≡ g
fracture-open-path abs g i .• = ●-isProp abs (η• (g .◦ abs)) (g .•) i
fracture-open-path abs g i .◦ = (funExt λ q → cong (g .◦) (str ABS abs q)) i
fracture-open-path abs g i .•→◦ =
  isProp→PathP
    (λ i → isProp→isSet (●-isProp abs)
      (●.map η◦ (●-isProp abs (η• (g .◦ abs)) (g .•) i))
      (η• ((funExt λ q → cong (g .◦) (str ABS abs q)) i)))
    refl
    (g .•→◦)
    i

fracture-open-isEquiv : {X : 𝒱} (abs : ⟨ ABS ⟩) → isEquiv (fracture {X})
fracture-open-isEquiv abs =
  isoToIsEquiv (iso fracture (λ g → g .◦ abs) (fracture-open-path abs) (λ x → refl))

fracture-modal : {X : 𝒱} → ●.isModalMap (fracture {X})
fracture-modal g = ◯-isContr→isModal λ abs → fracture-open-isEquiv abs .equiv-proof g

fracture-●map-path : {X : 𝒱} (x• : ● X) →
  glue•-in (toFRAC X) x• ≡ ●.map (fracture {X}) x•
fracture-●map-path {X} (η• x) =
  glue•-in-point (toFRAC X) (η• x) (η◦ x) refl
fracture-●map-path {X} (∗ abs) = refl
fracture-●map-path {X} (law x abs i) =
  isProp→PathP
    (λ i → isProp→isSet (●-isProp abs)
      (glue•-in (toFRAC X) (law x abs i))
      (●.map (fracture {X}) (law x abs i)))
    (fracture-●map-path (η• x))
    (fracture-●map-path (∗ abs))
    i

fracture-●map-isEquiv : {X : 𝒱} → isEquiv (●.map (fracture {X}))
fracture-●map-isEquiv {X} =
  subst isEquiv (funExt fracture-●map-path) (glue•-in-isEquiv (toFRAC X))

fracture-connected : {X : 𝒱} → isConnectedMap (fracture {X})
fracture-connected = ●-map-isEquiv→connected-map fracture fracture-●map-isEquiv

fracture-isEquiv : {X : 𝒱} → isEquiv (fracture {X})
fracture-isEquiv = isModal+isConnected→isEquiv fracture-modal fracture-connected

glue-fracture-section : section toFRAC fromFRAC
glue-fracture-section F i .X• = glue•-path F i
glue-fracture-section F i .X◦ = glue◦-path F i
glue-fracture-section F i .χ• =
  ua→
    {e = glue•-equiv F}
    {B = λ i → ● ⟨ glue◦-path F i ⟩}
    {f₀ = ●.map η◦}
    {f₁ = F .χ•}
    (glue-χ-path-base F)
    i

glue-fracture-retract : retract toFRAC fromFRAC
glue-fracture-retract X = sym (ua (fracture , fracture-isEquiv))

fracture-and-gluing : 𝒱 ≃ 𝒱-FRAC
fracture-and-gluing .fst = toFRAC
fracture-and-gluing .snd = isoToIsEquiv (iso toFRAC fromFRAC glue-fracture-section glue-fracture-retract)

fracture-and-gluing-square : (X → Y) ≡ 𝒱-Square (toFRAC X) (toFRAC Y)
fracture-and-gluing-square = {!   !}
