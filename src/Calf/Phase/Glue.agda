open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Calf.Phase.Glue (φ : Type) (φ-isProp : isProp φ) where

open import Calf.Phase.Open φ φ-isProp as ◯
open import Calf.Phase.Closed φ φ-isProp as ●
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Unit.Properties
open import Cubical.Foundations.CartesianKanOps
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws using (symInvo)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Univalence using (ua; ua→; ua-gluePath)

funext-dep
  : ∀ {A : I → Type} {B : (i : I) → A i → Type} {f g}
  → ( ∀ {x₀ x₁} (p : PathP A x₀ x₁)
    → PathP (λ i → B i (p i)) (f x₀) (g x₁) )
  → PathP (λ i → (x : A i) → B i x) f g
funext-dep {A = A} {B} h i x =
  transp (λ k → B i (coei→i A i x k)) (i ∨ ~ i)
    (h (λ j → coei→j A i j x) i)

funext-dep-i0
  : ∀ {A : I → Type} {B : (i : I) → A i → Type} {f g}
  → ( ∀ (x : A i0)
    → PathP (λ i → B i (coe0→i A i x)) (f x) (g (coe0→1 A x)))
  → PathP (λ i → (x : A i) → B i x) f g
funext-dep-i0 {A = A} {B} {f} {g} h =
  funext-dep λ {x₀} {x₁} p →
  subst (λ (p : (i : I) → A i) → PathP (λ i → B i (p i)) (f (p i0)) (g (p i1)))
    (λ j i → coePath A (λ i → p i) i0 i j)
    (h x₀)

◯-join : {X : Type} → ◯ (◯ X) → ◯ X
◯-join x p = x p p

◯-η-isEquiv : {X : Type} → isEquiv (η∘ {◯ X})
◯-η-isEquiv = isoToIsEquiv (iso η∘ ◯-join sec ret)
  where
  sec : {X : Type} → (x : ◯ (◯ X)) → η∘ (◯-join x) ≡ x
  sec x = funExt λ p → funExt λ q → cong (λ r → x r q) (φ-isProp q p)

  ret : {X : Type} → (x : ◯ X) → ◯-join (η∘ x) ≡ x
  ret x = refl

●-path-to-star : {X : Type} → (p : φ) → (x : ● X) → x ≡ ∗ p
●-path-to-star p (η• x) = law x p
●-path-to-star p (∗ q) = cong ∗ (φ-isProp q p)
●-path-to-star p (law x q i) j =
  hcomp
    (λ k → λ
      { (i = i0) → law x p (j ∧ k)
      ; (i = i1) → law x (φ-isProp q p j) k
      ; (j = i0) → law x q (i ∧ k)
      ; (j = i1) → law x p k })
    (η• x)

●-isProp : {X : Type} → φ → isProp (● X)
●-isProp p x y = ●-path-to-star p x ∙ sym (●-path-to-star p y)

●-isContr : {X : Type} → φ → isContr (● X)
●-isContr p .fst = ∗ p
●-isContr p .snd x = sym (●-path-to-star p x)

●-encode : ∀ {X} → X → ● X → Type
●-encode x (η• x') = ● (x ≡ x')
●-encode x (∗ p) = Unit
●-encode x (law x' p i) = isContr→≡Unit (●-isContr {X = x ≡ x'} p) i

●-lex : ∀ {X} {x : X} {y : ● X} → η• x ≡ y → ●-encode x y
●-lex {x = x} h = J (λ y _ → ●-encode x y) (η• refl) h

●-unlex : ∀ {X} {x x' : X} → ● (x ≡ x') → η• x ≡ η• x'
●-unlex (η• h) = cong η• h
●-unlex {x = x} {x'} (∗ p) = law x p ∙ sym (law x' p)
●-unlex {x = x} {x'} (law h p i) =
  isProp→isSet (●-isProp p) (η• x) (η• x')
    (cong η• h)
    (law x p ∙ sym (law x' p))
    i

●-lex-unlex : ∀ {X} {x x' : X} (e : ● (x ≡ x')) → ●-lex (●-unlex e) ≡ e
●-lex-unlex {x = x} (η• h) =
  J
    (λ x' h → ●-lex (cong η• h) ≡ η• h)
    (JRefl {x = η• x} (λ y _ → ●-encode x y) (η• refl))
    h
●-lex-unlex {x = x} {x'} (∗ p) =
  ●-isProp p
    (●-lex (law x p ∙ sym (law x' p)))
    (∗ p)
●-lex-unlex {x = x} {x'} (law h p i) =
  isProp→PathP
    (λ i → isProp→isSet (●-isProp p)
      (●-lex (●-unlex (law h p i)))
      (law h p i))
    (●-lex-unlex (η• h))
    (●-lex-unlex (∗ p))
    i

●-join : {X : Type} → ● (● X) → ● X
●-join (η• x) = x
●-join (∗ p) = ∗ p
●-join (law x p i) = ●-path-to-star p x i

●-η-isEquiv : {X : Type} → isEquiv (η• {● X})
●-η-isEquiv = isoToIsEquiv (iso η• ●-join sec ret)
  where
  ret : {X : Type} → (x : ● X) → ●-join (η• x) ≡ x
  ret x = refl

  sec : {X : Type} → (x : ● (● X)) → η• (●-join x) ≡ x
  sec (η• x) = refl
  sec (∗ p) = law (∗ p) p
  sec (law x p i) =
    isProp→PathP
      (λ i → isProp→isSet (●-isProp {X = ● _} p)
        (η• (●-path-to-star p x i))
        (law x p i))
      refl
      (law (∗ p) p)
      i

●-η-fiber : {X : Type} (x• : ● X) → ● (Σ[ x ∈ X ] η• x ≡ x•)
●-η-fiber (η• x) = η• (x , refl)
●-η-fiber (∗ p) = ∗ p
●-η-fiber (law x p i) = law (x , λ j → law x p (i ∧ j)) p i

●-η-fiber-point
  : {X : Type} (x• : ● X) (u : Σ[ x ∈ X ] η• x ≡ x•)
  → ●-η-fiber x• ≡ η• u
●-η-fiber-point x• (x , p) =
  J (λ y q → ●-η-fiber y ≡ η• (x , q)) refl p

●-modal : Type → Type
●-modal X = isEquiv (η• {X})

●-connected : Type → Type
●-connected X = isContr (● X)

●-modal-map : {X Y : Type} → (X → Y) → Type
●-modal-map {Y = Y} f = (y : Y) → ●-modal (fiber f y)

●-connected-map : {X Y : Type} → (X → Y) → Type
●-connected-map {Y = Y} f = (y : Y) → ●-connected (fiber f y)

●-modal+connected→contr : {X : Type} → ●-modal X → ●-connected X → isContr X
●-modal+connected→contr X-modal X-connected =
  isOfHLevelRespectEquiv 0 (invEquiv (η• , X-modal)) X-connected

●-modal+connected→isEquiv
  : {X Y : Type} {f : X → Y}
  → ●-modal-map f
  → ●-connected-map f
  → isEquiv f
●-modal+connected→isEquiv f-modal f-connected .equiv-proof y =
  ●-modal+connected→contr (f-modal y) (f-connected y)

◯-isContr→●-modal : {X : Type} → ◯ (isContr X) → ●-modal X
◯-isContr→●-modal c = isoToIsEquiv (iso η• (out c) (sec c) (ret c))
  where
  out : {X : Type} → ◯ (isContr X) → ● X → X
  out c (η• x) = x
  out c (∗ p) = c p .fst
  out c (law x p i) = c p .snd x (~ i)

  sec : {X : Type} (c : ◯ (isContr X)) → section η• (out c)
  sec c (η• x) = refl
  sec c (∗ p) = law (c p .fst) p
  sec c (law x p i) =
    isProp→PathP
      (λ i → isProp→isSet (●-isProp p)
        (η• (c p .snd x (~ i)))
        (law x p i))
      refl
      (law (c p .fst) p)
      i

  ret : {X : Type} (c : ◯ (isContr X)) → retract η• (out c)
  ret c x = refl

●-map-const : {X Y : Type} (x : X) (y• : ● Y) → ●.map (λ _ → x) y• ≡ η• x
●-map-const x (η• y) = refl
●-map-const x (∗ p) = sym (law x p)
●-map-const x (law y p i) j = law x p (i ∧ ~ j)

●-map-∘ : {X Y Z : Type} (f : X → Y) (g : Y → Z) (x• : ● X) →
  ●.map g (●.map f x•) ≡ ●.map (λ x → g (f x)) x•
●-map-∘ f g (η• x) = refl
●-map-∘ f g (∗ p) = refl
●-map-∘ f g (law x p i) = refl

●-fiber-map-isProp-at
  : {X Y : Type} (f : X → Y) (y : Y) (p : φ)
  → isProp (fiber (●.map f) (η• y))
●-fiber-map-isProp-at f y p =
  isPropΣ (●-isProp p) λ x• →
    isProp→isSet (●-isProp p) (●.map f x•) (η• y)

●-fiber-out
  : {X Y : Type} (f : X → Y) (y : Y)
  → ● (fiber f y) → fiber (●.map f) (η• y)
●-fiber-out f y =
  ind R η•-case ∗-case law-case
  where
  R : ● (fiber f y) → Type
  R _ = fiber (●.map f) (η• y)

  η•-case : (u : fiber f y) → R (η• u)
  η•-case (x , q) = η• x , cong η• q

  ∗-case : (p : φ) → R (∗ p)
  ∗-case p = ∗ p , sym (law y p)

  law-case : (u : fiber f y) (p : φ) → PathP (λ i → R (law u p i)) (η•-case u) (∗-case p)
  law-case u p =
    isProp→PathP (λ _ → ●-fiber-map-isProp-at f y p) (η•-case u) (∗-case p)

●-fiber-in
  : {X Y : Type} (f : X → Y) (y : Y)
  → fiber (●.map f) (η• y) → ● (fiber f y)
●-fiber-in f y (x• , q) =
  ind R η•-case ∗-case law-case x• q
  where
  R : ● _ → Type
  R x• = ●.map f x• ≡ η• y → ● (fiber f y)

  η•-case : (x : _) → R (η• x)
  η•-case x q = ●.map (λ r → x , r) (●-lex q)

  ∗-case : (p : φ) → R (∗ p)
  ∗-case p q = ∗ p

  law-case : (x : _) (p : φ) → PathP (λ i → R (law x p i)) (η•-case x) (∗-case p)
  law-case x p =
    funext-dep-i0 λ q →
      isProp→PathP
        (λ _ → ●-isProp p)
        (η•-case x q)
        (∗-case p (coe0→1 (λ i → ●.map f (law x p i) ≡ η• y) q))

●-fiber-in-out
  : {X Y : Type} (f : X → Y) (y : Y) (u• : ● (fiber f y))
  → ●-fiber-in f y (●-fiber-out f y u•) ≡ u•
●-fiber-in-out f y =
  ind R η•-case ∗-case law-case
  where
  R : ● (fiber f y) → Type
  R u• = ●-fiber-in f y (●-fiber-out f y u•) ≡ u•

  η•-case : (u : fiber f y) → R (η• u)
  η•-case (x , q) =
    cong (●.map (λ r → x , r)) (●-lex-unlex (η• q))

  ∗-case : (p : φ) → R (∗ p)
  ∗-case p = refl

  law-case : (u : fiber f y) (p : φ) → PathP (λ i → R (law u p i)) (η•-case u) (∗-case p)
  law-case u p =
    isProp→PathP
      (λ i → isProp→isSet (●-isProp p)
        (●-fiber-in f y (●-fiber-out f y (law u p i)))
        (law u p i))
      (η•-case u)
      (∗-case p)

●-map-isEquiv→connected-map
  : {X Y : Type} (f : X → Y)
  → isEquiv (●.map f)
  → ●-connected-map f
●-map-isEquiv→connected-map f f•-isEquiv y .fst =
  ●-fiber-in f y (f•-isEquiv .equiv-proof (η• y) .fst)
●-map-isEquiv→connected-map f f•-isEquiv y .snd u• =
  cong (●-fiber-in f y) (f•-isEquiv .equiv-proof (η• y) .snd (●-fiber-out f y u•))
  ∙ ●-fiber-in-out f y u•

Type•-at-open-isContr : (X• : Type•) → φ → isContr ⟨ X• ⟩
Type•-at-open-isContr X• p .fst = invIsEq (X• .snd) (∗ p)
Type•-at-open-isContr X• p .snd x =
  cong (invIsEq (X• .snd)) (sym (law x p)) ∙ retIsEq (X• .snd) x

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
    toPathP (fromPathP star-step ∙ sym (●-path-to-star p (F .χ (glue•-out F (∗ p)))))
    where
    star-step : PathP B (∗ p) (∗ p)
    star-step i = ∗ p

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

glue-fracture-retract : retract toFRAC fromFRAC
glue-fracture-retract X = sym (ua (fracture , fracture-isEquiv))

fracture-and-gluing : Type ≃ FRAC
fracture-and-gluing .fst = toFRAC
fracture-and-gluing .snd = isoToIsEquiv (iso toFRAC fromFRAC glue-fracture-section glue-fracture-retract)
