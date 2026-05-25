open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws using (symInvo)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Univalence using (ua; ua→; ua-gluePath)

module Calf.Phase.Glue (φ : Type) (φ-isProp : isProp φ) where

open import Calf.Phase.Open φ φ-isProp as ◯
open import Calf.Phase.Closed φ φ-isProp as ●

record Glue (X• : Type•) (X∘ : Type∘) (χ : ⟨ X• ⟩ → ● ⟨ X∘ ⟩) : Type where
  field
    • : ⟨ X• ⟩
    ∘ : ⟨ X∘ ⟩
    •→∘ : χ • ≡ η• ∘
open Glue public

record FRAC : Type₁ where
  field
    X• : Type•
    X∘ : Type∘
    χ : ⟨ X• ⟩ → ● ⟨ X∘ ⟩
open FRAC

fromFRAC : FRAC → Type
fromFRAC F = Glue (F .X•) (F .X∘) (F .χ)

glue•-in : (F : FRAC) → ⟨ F .X• ⟩ → ● (fromFRAC F)
glue•-in F x• =
  ●.map
    (λ (x∘ , p) →
      record
        { • = x•
        ; ∘ = x∘
        ; •→∘ = sym p
        })
    (●-η-fiber (F .χ x•))

glue•-out : (F : FRAC) → ● (fromFRAC F) → ⟨ F .X• ⟩
glue•-out F g• = invIsEq (F .X• .snd) (●.map (λ g → g .•) g•)

glue•-in-proj : (F : FRAC) (x• : ⟨ F .X• ⟩) →
  ●.map (λ g → g .•) (glue•-in F x•) ≡ η• x•
glue•-in-proj F x• =
  ●-map-∘
    (λ (x∘ , p) →
      record
        { • = x•
        ; ∘ = x∘
        ; •→∘ = sym p
        })
    (λ g → g .•)
    (●-η-fiber (F .χ x•))
  ∙ ●-map-const x• (●-η-fiber (F .χ x•))

glue•-rightInv : (F : FRAC) → section (glue•-out F) (glue•-in F)
glue•-rightInv F x• =
  cong (invIsEq (F .X• .snd)) (glue•-in-proj F x•)
  ∙ retIsEq (F .X• .snd) x•

glue•-in-point : (F : FRAC) (x• : ⟨ F .X• ⟩) (x∘ : ⟨ F .X∘ ⟩)
  (h : F .χ x• ≡ η• x∘) →
  glue•-in F x• ≡
    η• (record { • = x• ; ∘ = x∘ ; •→∘ = h })
glue•-in-point F x• x∘ h =
  cong
    (●.map
      (λ (x∘ , p) →
        record
          { • = x•
          ; ∘ = x∘
          ; •→∘ = sym p
          }))
    (●-η-fiber-point (F .χ x•) (x∘ , sym h))
  ∙ cong η• (λ i → record { • = x• ; ∘ = x∘ ; •→∘ = symInvo h (~ i) })

glue•-leftInv : (F : FRAC) → retract (glue•-out F) (glue•-in F)
glue•-leftInv F =
  ind R η•-case ∗-case law-case
  where
  R : ● (fromFRAC F) → Type
  R g• = glue•-in F (glue•-out F g•) ≡ g•

  η•-case : (g : fromFRAC F) → R (η• g)
  η•-case g =
    cong (glue•-in F) (retIsEq (F .X• .snd) (g .•))
    ∙ glue•-in-point F (g .•) (g .∘) (g .•→∘)

  ∗-case : (p : φ) → R (∗ p)
  ∗-case p = ●-path-to-star p (glue•-in F (glue•-out F (∗ p)))

  law-case : (g : fromFRAC F) (p : φ) → PathP (λ i → R (law g p i)) (η•-case g) (∗-case p)
  law-case g p =
    isProp→PathP
      (λ i → isProp→isSet (●-isProp p)
        (glue•-in F (glue•-out F (law g p i)))
        (law g p i))
      (η•-case g)
      (∗-case p)

glue•-equiv : (F : FRAC) → ● (fromFRAC F) ≃ ⟨ F .X• ⟩
glue•-equiv F = isoToEquiv (iso (glue•-out F) (glue•-in F) (glue•-rightInv F) (glue•-leftInv F))

glue•-in-isEquiv : (F : FRAC) → isEquiv (glue•-in F)
glue•-in-isEquiv F =
  isoToIsEquiv (iso (glue•-in F) (glue•-out F) (glue•-leftInv F) (glue•-rightInv F))

glue∘-fiber : (F : FRAC) (x∘ : ⟨ F .X∘ ⟩) →
  ◯ (Σ[ g ∈ fromFRAC F ] g .∘ ≡ x∘)
glue∘-fiber F x∘ p =
  (record
    { • = Type•-at-open-isContr (F .X•) p .fst
    ; ∘ = x∘
    ; •→∘ = ●-isProp p (F .χ (Type•-at-open-isContr (F .X•) p .fst)) (η• x∘)
    })
  , refl

glue∘-in : (F : FRAC) → ⟨ F .X∘ ⟩ → ◯ (fromFRAC F)
glue∘-in F x∘ p = glue∘-fiber F x∘ p .fst

glue∘-out : (F : FRAC) → ◯ (fromFRAC F) → ⟨ F .X∘ ⟩
glue∘-out F g∘ = invIsEq (F .X∘ .snd) (◯.map (λ g → g .∘) g∘)

glue∘-rightInv : (F : FRAC) → section (glue∘-out F) (glue∘-in F)
glue∘-rightInv F x∘ = retIsEq (F .X∘ .snd) x∘

glue∘-leftInv : (F : FRAC) → retract (glue∘-out F) (glue∘-in F)
glue∘-leftInv F g∘ = funExt λ p → λ i →
  record
    { • = concrete-path p i
    ; ∘ = open-path p i
    ; •→∘ = proof-path p i
    }
  where
  concrete-path : (p : φ) →
    Type•-at-open-isContr (F .X•) p .fst ≡ g∘ p .•
  concrete-path p = Type•-at-open-isContr (F .X•) p .snd (g∘ p .•)

  open-path : (p : φ) → glue∘-out F g∘ ≡ g∘ p .∘
  open-path p = funExt⁻ (secIsEq (F .X∘ .snd) (◯.map (λ g → g .∘) g∘)) p

  proof-path : (p : φ) →
    PathP
      (λ i → F .χ (concrete-path p i) ≡ η• (open-path p i))
      (●-isProp p (F .χ (Type•-at-open-isContr (F .X•) p .fst)) (η• (glue∘-out F g∘)))
      (g∘ p .•→∘)
  proof-path p =
    isProp→PathP
      (λ i → isProp→isSet (●-isProp p)
        (F .χ (concrete-path p i))
        (η• (open-path p i)))
      (●-isProp p (F .χ (Type•-at-open-isContr (F .X•) p .fst)) (η• (glue∘-out F g∘)))
      (g∘ p .•→∘)

glue∘-equiv : (F : FRAC) → ◯ (fromFRAC F) ≃ ⟨ F .X∘ ⟩
glue∘-equiv F = isoToEquiv (iso (glue∘-out F) (glue∘-in F) (glue∘-rightInv F) (glue∘-leftInv F))

glue•-path : (F : FRAC) → (● (fromFRAC F) , ●-η-isEquiv) ≡ F .X•
glue•-path F = Σ≡Prop (λ X → isPropIsEquiv (η• {X})) (ua (glue•-equiv F))

glue∘-path : (F : FRAC) → (◯ (fromFRAC F) , ◯-η-isEquiv) ≡ F .X∘
glue∘-path F = Σ≡Prop (λ X → isPropIsEquiv (η∘ {X})) (ua (glue∘-equiv F))

glue-χ-path-base : (F : FRAC) (g• : ● (fromFRAC F)) →
  PathP
    (λ i → ● ⟨ glue∘-path F i ⟩)
    (●.map η∘ g•)
    (F .χ (glue•-out F g•))
glue-χ-path-base F =
  ind R η•-case ∗-case law-case
  where
  B : I → Type
  B i = ● ⟨ glue∘-path F i ⟩

  R : ● (fromFRAC F) → Type
  R g• = PathP B (●.map η∘ g•) (F .χ (glue•-out F g•))

  η•-case : (g : fromFRAC F) → R (η• g)
  η•-case g =
    toPathP (fromPathP closed-open-step ∙ endpoint-step)
    where
    open-step : PathP (λ i → ⟨ glue∘-path F i ⟩) (η∘ g) (glue∘-out F (η∘ g))
    open-step = ua-gluePath (glue∘-equiv F) refl

    closed-open-step : PathP B (η• (η∘ g)) (η• (glue∘-out F (η∘ g)))
    closed-open-step i = η• (open-step i)

    endpoint-step : η• (glue∘-out F (η∘ g)) ≡ F .χ (glue•-out F (η• g))
    endpoint-step =
      cong η• (retIsEq (F .X∘ .snd) (g .∘))
      ∙ sym (g .•→∘)
      ∙ sym (cong (F .χ) (retIsEq (F .X• .snd) (g .•)))

  ∗-case : (p : φ) → R (∗ p)
  ∗-case p =
    toPathP (fromPathP (sym (●-path-to-star p (F .χ (glue•-out F (∗ p))))))

  law-case : (g : fromFRAC F) (p : φ) → PathP (λ i → R (law g p i)) (η•-case g) (∗-case p)
  law-case g p =
    isProp→PathP
      (λ i → isProp→isPropPathP (λ _ → ●-isProp p)
        (●.map η∘ (law g p i))
        (F .χ (glue•-out F (law g p i))))
      (η•-case g)
      (∗-case p)

toFRAC : Type → FRAC
toFRAC X .X• = ● X , ●-η-isEquiv
toFRAC X .X∘ = ◯ X , ◯-η-isEquiv
toFRAC X .χ = ●.map η∘

FractureGlue : Type → Type
FractureGlue X = Glue (● X , ●-η-isEquiv) (◯ X , ◯-η-isEquiv) (●.map η∘)

fracture : {X : Type} → X → FractureGlue X
fracture x .• = η• x
fracture x .∘ = η∘ x
fracture x .•→∘ = refl

fracture-open-path : {X : Type} (p : φ) (g : FractureGlue X) → fracture (g .∘ p) ≡ g
fracture-open-path p g i .• = ●-isProp p (η• (g .∘ p)) (g .•) i
fracture-open-path p g i .∘ = (funExt λ q → cong (g .∘) (φ-isProp p q)) i
fracture-open-path p g i .•→∘ =
  isProp→PathP
    (λ i → isProp→isSet (●-isProp p)
      (●.map η∘ (●-isProp p (η• (g .∘ p)) (g .•) i))
      (η• ((funExt λ q → cong (g .∘) (φ-isProp p q)) i)))
    refl
    (g .•→∘)
    i

fracture-open-isEquiv : {X : Type} (p : φ) → isEquiv (fracture {X})
fracture-open-isEquiv p =
  isoToIsEquiv (iso fracture (λ g → g .∘ p) (fracture-open-path p) (λ x → refl))

fracture-modal : {X : Type} → ●-modal-map (fracture {X})
fracture-modal g = ◯-isContr→●-modal λ p → fracture-open-isEquiv p .equiv-proof g

fracture-●map-path : {X : Type} (x• : ● X) →
  glue•-in (toFRAC X) x• ≡ ●.map (fracture {X}) x•
fracture-●map-path {X} (η• x) =
  glue•-in-point (toFRAC X) (η• x) (η∘ x) refl
fracture-●map-path {X} (∗ p) = refl
fracture-●map-path {X} (law x p i) =
  isProp→PathP
    (λ i → isProp→isSet (●-isProp p)
      (glue•-in (toFRAC X) (law x p i))
      (●.map (fracture {X}) (law x p i)))
    (fracture-●map-path (η• x))
    (fracture-●map-path (∗ p))
    i

fracture-●map-isEquiv : {X : Type} → isEquiv (●.map (fracture {X}))
fracture-●map-isEquiv {X} =
  subst isEquiv (funExt fracture-●map-path) (glue•-in-isEquiv (toFRAC X))

fracture-connected : {X : Type} → ●-connected-map (fracture {X})
fracture-connected = ●-map-isEquiv→connected-map fracture fracture-●map-isEquiv

fracture-isEquiv : {X : Type} → isEquiv (fracture {X})
fracture-isEquiv = ●-modal+connected→isEquiv fracture-modal fracture-connected

glue-fracture-section : section toFRAC fromFRAC
glue-fracture-section F i .X• = glue•-path F i
glue-fracture-section F i .X∘ = glue∘-path F i
glue-fracture-section F i .χ =
  ua→
    {e = glue•-equiv F}
    {B = λ i → ● ⟨ glue∘-path F i ⟩}
    {f₀ = ●.map η∘}
    {f₁ = F .χ}
    (glue-χ-path-base F)
    i

-- This proof is largely due to https://agda.monade.li/ErasureOpen.html
glue-fracture-retract : retract toFRAC fromFRAC
glue-fracture-retract X = sym (ua (fracture , fracture-isEquiv))

fracture-and-gluing : Type ≃ FRAC
fracture-and-gluing .fst = toFRAC
fracture-and-gluing .snd = isoToIsEquiv (iso toFRAC fromFRAC glue-fracture-section glue-fracture-retract)
