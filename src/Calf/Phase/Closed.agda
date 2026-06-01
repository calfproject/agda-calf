open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.CartesianKanOps
open import Cubical.Data.Unit

module Calf.Phase.Closed (φ : Type) (φ-isProp : isProp φ) where

open import Calf.Phase.Open φ φ-isProp using (◯)

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

data ● (X : Type) : Type where
  η• : (x : X) → ● X
  ∗ : (p : φ) → ● X
  law : (x : X) (p : φ) → η• x ≡ ∗ p

ind : {X : Type} (R : ● X → Type)
  → (η•-case : (x : X) → R (η• x))
  → (∗-case : (p : φ) → R (∗ p))
  → (law-case : (x : X) (p : φ) → PathP (λ i → R (law x p i)) (η•-case x) (∗-case p))
  → (x• : ● X) → R x•
ind R η•-case ∗-case law-case (η• x) = η•-case x
ind R η•-case ∗-case law-case (∗ p) = ∗-case p
ind R η•-case ∗-case law-case (law x p i) = law-case x p i

map : {X Y : Type} → (X → Y) → ● X → ● Y
map f (η• x) = η• (f x)
map f (∗ p) = ∗ p
map f (law x p i) = law (f x) p i

Type• : Type₁
Type• = TypeWithStr _ λ X → isEquiv (η• {X})

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

●-isContr : {X : Type} → φ → isContr (● X)
●-isContr p .fst = ∗ p
●-isContr p .snd x = sym (●-path-to-star p x)

●-isProp : {X : Type} → φ → isProp (● X)
●-isProp p = isContr→isProp (●-isContr p)

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

●-map-const : {X Y : Type} (x : X) (y• : ● Y) → map (λ _ → x) y• ≡ η• x
●-map-const x (η• y) = refl
●-map-const x (∗ p) = sym (law x p)
●-map-const x (law y p i) j = law x p (i ∧ ~ j)

●-map-∘ : {X Y Z : Type} (f : X → Y) (g : Y → Z) (x• : ● X) →
  map g (map f x•) ≡ map (λ x → g (f x)) x•
●-map-∘ f g (η• x) = refl
●-map-∘ f g (∗ p) = refl
●-map-∘ f g (law x p i) = refl

●-fiber-map-isProp-at
  : {X Y : Type} (f : X → Y) (y : Y) (p : φ)
  → isProp (fiber (map f) (η• y))
●-fiber-map-isProp-at f y p =
  isPropΣ (●-isProp p) λ x• →
    isProp→isSet (●-isProp p) (map f x•) (η• y)

●-fiber-out
  : {X Y : Type} (f : X → Y) (y : Y)
  → ● (fiber f y) → fiber (map f) (η• y)
●-fiber-out f y =
  ind R η•-case ∗-case law-case
  where
  R : ● (fiber f y) → Type
  R _ = fiber (map f) (η• y)

  η•-case : (u : fiber f y) → R (η• u)
  η•-case (x , q) = η• x , cong η• q

  ∗-case : (p : φ) → R (∗ p)
  ∗-case p = ∗ p , sym (law y p)

  law-case : (u : fiber f y) (p : φ) → PathP (λ i → R (law u p i)) (η•-case u) (∗-case p)
  law-case u p =
    isProp→PathP (λ _ → ●-fiber-map-isProp-at f y p) (η•-case u) (∗-case p)

●-fiber-in
  : {X Y : Type} (f : X → Y) (y : Y)
  → fiber (map f) (η• y) → ● (fiber f y)
●-fiber-in f y (x• , q) =
  ind R η•-case ∗-case law-case x• q
  where
  R : ● _ → Type
  R x• = map f x• ≡ η• y → ● (fiber f y)

  η•-case : (x : _) → R (η• x)
  η•-case x q = map (λ r → x , r) (●-lex q)

  ∗-case : (p : φ) → R (∗ p)
  ∗-case p q = ∗ p

  law-case : (x : _) (p : φ) → PathP (λ i → R (law x p i)) (η•-case x) (∗-case p)
  law-case x p =
    funext-dep-i0 λ q →
      isProp→PathP
        (λ _ → ●-isProp p)
        (η•-case x q)
        (∗-case p (coe0→1 (λ i → map f (law x p i) ≡ η• y) q))

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
    cong (map (λ r → x , r)) (●-lex-unlex (η• q))

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
  → isEquiv (map f)
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

isSet● : ∀ {X} → isSet X → isSet (● X)
isSet● isSetX = {!   !}
