open import Calf.Core.Abstract
open import Calf.Value

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.CartesianKanOps
open import Cubical.Data.Unit

module Calf.Value.Closed where

open import Calf.Value.Open using (◯)

-- The following two proofs are imported from the 1Lab: https://1lab.dev/1Lab.𝒱.Pi.html
funext-dep
  : ∀ {A : I → 𝒱} {B : (i : I) → A i → 𝒱} {f g}
  → ( ∀ {x₀ x₁} (p : PathP A x₀ x₁)
    → PathP (λ i → B i (p i)) (f x₀) (g x₁) )
  → PathP (λ i → (x : A i) → B i x) f g
funext-dep {A = A} {B} h i x =
  transp (λ k → B i (coei→i A i x k)) (i ∨ ~ i)
    (h (λ j → coei→j A i j x) i)

funext-dep-i0
  : ∀ {A : I → 𝒱} {B : (i : I) → A i → 𝒱} {f g}
  → ( ∀ (x : A i0)
    → PathP (λ i → B i (coe0→i A i x)) (f x) (g (coe0→1 A x)))
  → PathP (λ i → (x : A i) → B i x) f g
funext-dep-i0 {A = A} {B} {f} {g} h =
  funext-dep λ {x₀} {x₁} p →
  subst (λ (p : (i : I) → A i) → PathP (λ i → B i (p i)) (f (p i0)) (g (p i1)))
    (λ j i → coePath A (λ i → p i) i0 i j)
    (h x₀)

data ● (X : 𝒱) : 𝒱 where
  η• : (x : X) → ● X
  ∗ : (abs : ⟨ ABS ⟩) → ● X
  law : (x : X) (abs : ⟨ ABS ⟩) → η• x ≡ ∗ abs

ind : {X : 𝒱} (R : ● X → 𝒱)
  → (η•-case : (x : X) → R (η• x))
  → (∗-case : (abs : ⟨ ABS ⟩) → R (∗ abs))
  → (law-case : (x : X) (abs : ⟨ ABS ⟩) → PathP (λ i → R (law x abs i)) (η•-case x) (∗-case abs))
  → (x• : ● X) → R x•
ind R η•-case ∗-case law-case (η• x) = η•-case x
ind R η•-case ∗-case law-case (∗ abs) = ∗-case abs
ind R η•-case ∗-case law-case (law x abs i) = law-case x abs i

map : {X Y : 𝒱} → (X → Y) → ● X → ● Y
map f (η• x) = η• (f x)
map f (∗ abs) = ∗ abs
map f (law x abs i) = law (f x) abs i

𝒱• : 𝒱₁
𝒱• = TypeWithStr _ λ X → isEquiv (η• {X})

●-path-to-star : {X : 𝒱} → (abs : ⟨ ABS ⟩) → (x : ● X) → x ≡ ∗ abs
●-path-to-star abs (η• x) = law x abs
●-path-to-star abs (∗ q) = cong ∗ (str ABS q abs)
●-path-to-star abs (law x q i) j =
  hcomp
    (λ k → λ
      { (i = i0) → law x abs (j ∧ k)
      ; (i = i1) → law x (str ABS q abs j) k
      ; (j = i0) → law x q (i ∧ k)
      ; (j = i1) → law x abs k })
    (η• x)

●-isContr : {X : 𝒱} → ⟨ ABS ⟩ → isContr (● X)
●-isContr abs .fst = ∗ abs
●-isContr abs .snd x = sym (●-path-to-star abs x)

●-isProp : {X : 𝒱} → ⟨ ABS ⟩ → isProp (● X)
●-isProp abs = isContr→isProp (●-isContr abs)

●-encode : ∀ {X} → X → ● X → 𝒱
●-encode x (η• x') = ● (x ≡ x')
●-encode x (∗ abs) = Unit
●-encode x (law x' abs i) = isContr→≡Unit (●-isContr {X = x ≡ x'} abs) i

●-lex : ∀ {X} {x : X} {y : ● X} → η• x ≡ y → ●-encode x y
●-lex {x = x} h = J (λ y _ → ●-encode x y) (η• refl) h

●-unlex : ∀ {X} {x x' : X} → ● (x ≡ x') → η• x ≡ η• x'
●-unlex (η• h) = cong η• h
●-unlex {x = x} {x'} (∗ abs) = law x abs ∙ sym (law x' abs)
●-unlex {x = x} {x'} (law h abs i) =
  isProp→isSet (●-isProp abs) (η• x) (η• x')
    (cong η• h)
    (law x abs ∙ sym (law x' abs))
    i

●-unlex' : ∀ {X} {x : X} {y : ● X} → ●-encode x y → η• x ≡ y
●-unlex' {X} {x} {y} e =
  ind R η•-case ∗-case law-case y e
  where
  R : ● X → 𝒱
  R y = ●-encode x y → η• x ≡ y

  η•-case : (x' : X) → R (η• x')
  η•-case x' e = ●-unlex e

  ∗-case : (abs : ⟨ ABS ⟩) → R (∗ abs)
  ∗-case abs _ = law x abs

  law-case : (x' : X) (abs : ⟨ ABS ⟩) → PathP (λ i → R (law x' abs i)) (η•-case x') (∗-case abs)
  law-case x' abs =
    funext-dep-i0 λ e →
      isProp→PathP
        (λ i → isProp→isSet (●-isProp abs)
          (η• x)
          (law x' abs i))
        (η•-case x' e)
        (∗-case abs (coe0→1 (λ i → ●-encode x (law x' abs i)) e))

●-lex-unlex : ∀ {X} {x x' : X} (e : ● (x ≡ x')) → ●-lex (●-unlex e) ≡ e
●-lex-unlex {x = x} (η• h) =
  J
    (λ x' h → ●-lex (cong η• h) ≡ η• h)
    (JRefl {x = η• x} (λ y _ → ●-encode x y) (η• refl))
    h
●-lex-unlex {x = x} {x'} (∗ abs) =
  ●-isProp abs
    (●-lex (law x abs ∙ sym (law x' abs)))
    (∗ abs)
●-lex-unlex {x = x} {x'} (law h abs i) =
  isProp→PathP
    (λ i → isProp→isSet (●-isProp abs)
      (●-lex (●-unlex (law h abs i)))
      (law h abs i))
    (●-lex-unlex (η• h))
    (●-lex-unlex (∗ abs))
    i

●-unlex-lex : ∀ {X} {x x' : X} (h : η• x ≡ η• x') → ●-unlex (●-lex h) ≡ h
●-unlex-lex {X} {x} h =
  J
    (λ y h → ●-unlex' (●-lex h) ≡ h)
    (cong
      (λ e → ●-unlex' {X = X} {x = x} {y = η• x} e)
      (JRefl {x = η• x} (λ y _ → ●-encode x y) (η• {X = x ≡ x} refl)))
    h

join : {X : 𝒱} → ● (● X) → ● X
join (η• x) = x
join (∗ abs) = ∗ abs
join (law x abs i) = ●-path-to-star abs x i

bind : {X Y : 𝒱} → ● X → (X → ● Y) → ● Y
bind x• k = join (map k x•)

η-isEquiv : {X : 𝒱} → isEquiv (η• {● X})
η-isEquiv = isoToIsEquiv (iso η• join sec ret)
  where
  ret : {X : 𝒱} → (x : ● X) → join (η• x) ≡ x
  ret x = refl

  sec : {X : 𝒱} → (x : ● (● X)) → η• (join x) ≡ x
  sec (η• x) = refl
  sec (∗ abs) = law (∗ abs) abs
  sec (law x abs i) =
    isProp→PathP
      (λ i → isProp→isSet (●-isProp {X = ● _} abs)
        (η• (●-path-to-star abs x i))
        (law x abs i))
      refl
      (law (∗ abs) abs)
      i

η-fiber : {X : 𝒱} (x• : ● X) → ● (Σ[ x ∈ X ] η• x ≡ x•)
η-fiber (η• x) = η• (x , refl)
η-fiber (∗ abs) = ∗ abs
η-fiber (law x abs i) = law (x , λ j → law x abs (i ∧ j)) abs i

η-fiber-point
  : {X : 𝒱} (x• : ● X) (u : Σ[ x ∈ X ] η• x ≡ x•)
  → η-fiber x• ≡ η• u
η-fiber-point x• (x , abs) =
  J (λ y q → η-fiber y ≡ η• (x , q)) refl abs

isModal : 𝒱 → 𝒱
isModal X = isEquiv (η• {X})

isConnected : 𝒱 → 𝒱
isConnected X = isContr (● X)

isModalMap : {X Y : 𝒱} → (X → Y) → 𝒱
isModalMap {Y = Y} f = (y : Y) → isModal (fiber f y)

isConnectedMap : {X Y : 𝒱} → (X → Y) → 𝒱
isConnectedMap {Y = Y} f = (y : Y) → isConnected (fiber f y)

isModal+isConnected→isContr : {X : 𝒱} → isModal X → isConnected X → isContr X
isModal+isConnected→isContr X-modal X-connected =
  isOfHLevelRespectEquiv 0 (invEquiv (η• , X-modal)) X-connected

isModal+isConnected→isEquiv
  : {X Y : 𝒱} {f : X → Y}
  → isModalMap f
  → isConnectedMap f
  → isEquiv f
isModal+isConnected→isEquiv f-modal f-connected .equiv-proof y =
  isModal+isConnected→isContr (f-modal y) (f-connected y)

◯-isContr→isModal : {X : 𝒱} → ◯ (isContr X) → isModal X
◯-isContr→isModal c = isoToIsEquiv (iso η• (out c) (sec c) (ret c))
  where
    out : {X : 𝒱} → ◯ (isContr X) → ● X → X
    out c (η• x) = x
    out c (∗ abs) = c abs .fst
    out c (law x abs i) = c abs .snd x (~ i)

    sec : {X : 𝒱} (c : ◯ (isContr X)) → section η• (out c)
    sec c (η• x) = refl
    sec c (∗ abs) = law (c abs .fst) abs
    sec c (law x abs i) =
      isProp→PathP
        (λ i → isProp→isSet (●-isProp abs)
          (η• (c abs .snd x (~ i)))
          (law x abs i))
        refl
        (law (c abs .fst) abs)
        i

    ret : {X : 𝒱} (c : ◯ (isContr X)) → retract η• (out c)
    ret c x = refl

●-map-const : {X Y : 𝒱} (x : X) (y• : ● Y) → map (λ _ → x) y• ≡ η• x
●-map-const x (η• y) = refl
●-map-const x (∗ abs) = sym (law x abs)
●-map-const x (law y abs i) j = law x abs (i ∧ ~ j)

map-∘ : {X Y Z : 𝒱} (f : X → Y) (g : Y → Z) (x• : ● X) →
  map g (map f x•) ≡ map (g ∘ f) x•
map-∘ f g (η• x) = refl
map-∘ f g (∗ abs) = refl
map-∘ f g (law x abs i) = refl

●-fiber-map-isProp-at
  : {X Y : 𝒱} (f : X → Y) (y : Y) (abs : ⟨ ABS ⟩)
  → isProp (fiber (map f) (η• y))
●-fiber-map-isProp-at f y abs =
  isPropΣ (●-isProp abs) λ x• →
    isProp→isSet (●-isProp abs) (map f x•) (η• y)

●-fiber-out
  : {X Y : 𝒱} (f : X → Y) (y : Y)
  → ● (fiber f y) → fiber (map f) (η• y)
●-fiber-out f y =
  ind R η•-case ∗-case law-case
  where
    R : ● (fiber f y) → 𝒱
    R _ = fiber (map f) (η• y)

    η•-case : (u : fiber f y) → R (η• u)
    η•-case (x , q) = η• x , cong η• q

    ∗-case : (abs : ⟨ ABS ⟩) → R (∗ abs)
    ∗-case abs = ∗ abs , sym (law y abs)

    law-case : (u : fiber f y) (abs : ⟨ ABS ⟩) → PathP (λ i → R (law u abs i)) (η•-case u) (∗-case abs)
    law-case u abs =
      isProp→PathP (λ _ → ●-fiber-map-isProp-at f y abs) (η•-case u) (∗-case abs)

●-fiber-in
  : {X Y : 𝒱} (f : X → Y) (y : Y)
  → fiber (map f) (η• y) → ● (fiber f y)
●-fiber-in f y (x• , q) =
  ind R η•-case ∗-case law-case x• q
  where
    R : ● _ → 𝒱
    R x• = map f x• ≡ η• y → ● (fiber f y)

    η•-case : (x : _) → R (η• x)
    η•-case x q = map (λ r → x , r) (●-lex q)

    ∗-case : (abs : ⟨ ABS ⟩) → R (∗ abs)
    ∗-case abs q = ∗ abs

    law-case : (x : _) (abs : ⟨ ABS ⟩) → PathP (λ i → R (law x abs i)) (η•-case x) (∗-case abs)
    law-case x abs =
      funext-dep-i0 λ q →
        isProp→PathP
          (λ _ → ●-isProp abs)
          (η•-case x q)
          (∗-case abs (coe0→1 (λ i → map f (law x abs i) ≡ η• y) q))

●-fiber-in-out
  : {X Y : 𝒱} (f : X → Y) (y : Y) (u• : ● (fiber f y))
  → ●-fiber-in f y (●-fiber-out f y u•) ≡ u•
●-fiber-in-out f y =
  ind R η•-case ∗-case law-case
  where
    R : ● (fiber f y) → 𝒱
    R u• = ●-fiber-in f y (●-fiber-out f y u•) ≡ u•

    η•-case : (u : fiber f y) → R (η• u)
    η•-case (x , q) =
      cong (map (λ r → x , r)) (●-lex-unlex (η• q))

    ∗-case : (abs : ⟨ ABS ⟩) → R (∗ abs)
    ∗-case abs = refl

    law-case : (u : fiber f y) (abs : ⟨ ABS ⟩) → PathP (λ i → R (law u abs i)) (η•-case u) (∗-case abs)
    law-case u abs =
      isProp→PathP
        (λ i → isProp→isSet (●-isProp abs)
          (●-fiber-in f y (●-fiber-out f y (law u abs i)))
          (law u abs i))
        (η•-case u)
        (∗-case abs)

●-map-isEquiv→connected-map
  : {X Y : 𝒱} (f : X → Y)
  → isEquiv (map f)
  → isConnectedMap f
●-map-isEquiv→connected-map f f•-isEquiv y .fst =
  ●-fiber-in f y (f•-isEquiv .equiv-proof (η• y) .fst)
●-map-isEquiv→connected-map f f•-isEquiv y .snd u• =
  cong (●-fiber-in f y) (f•-isEquiv .equiv-proof (η• y) .snd (●-fiber-out f y u•))
  ∙ ●-fiber-in-out f y u•

𝒱•-at-open-isContr : (X• : 𝒱•) → ⟨ ABS ⟩ → isContr ⟨ X• ⟩
𝒱•-at-open-isContr X• abs .fst = invIsEq (X• .snd) (∗ abs)
𝒱•-at-open-isContr X• abs .snd x =
  cong (invIsEq (X• .snd)) (sym (law x abs)) ∙ retIsEq (X• .snd) x

●-path-to-point : ∀ {X} → isProp X → (x : X) (x• : ● X) → x• ≡ η• x
●-path-to-point {X} X-isProp x =
  ind R η•-case ∗-case law-case
  where
    R : ● X → 𝒱
    R x• = x• ≡ η• x

    η•-case : (y : X) → R (η• y)
    η•-case y = cong η• (X-isProp y x)

    ∗-case : (abs : ⟨ ABS ⟩) → R (∗ abs)
    ∗-case abs = sym (law x abs)

    law-case : (y : X) (abs : ⟨ ABS ⟩) → PathP (λ i → R (law y abs i)) (η•-case y) (∗-case abs)
    law-case y abs =
      isProp→PathP
        (λ i → isProp→isSet (●-isProp abs) (law y abs i) (η• x))
        (η•-case y)
        (∗-case abs)

●-preserves-isProp : ∀ {X} → isProp X → isProp (● X)
●-preserves-isProp {X} X-isProp =
  ind R η•-case ∗-case law-case
  where
  R : ● X → 𝒱
  R x• = (y• : ● X) → x• ≡ y•

  η•-case : (x : X) → R (η• x)
  η•-case x y• = sym (●-path-to-point X-isProp x y•)

  ∗-case : (abs : ⟨ ABS ⟩) → R (∗ abs)
  ∗-case abs y• = ●-isProp abs (∗ abs) y•

  law-case : (x : X) (abs : ⟨ ABS ⟩) → PathP (λ i → R (law x abs i)) (η•-case x) (∗-case abs)
  law-case x abs i y• =
    isProp→PathP
      (λ i → isProp→isSet (●-isProp abs) (law x abs i) y•)
      (η•-case x y•)
      (∗-case abs y•)
      i

●-isPropPath : ∀ {X} → isSet X → (x• y• : ● X) → isProp (x• ≡ y•)
●-isPropPath {X} X-isSet = ind R η•-case ∗-case law-case
  where
    R : ● X → 𝒱
    R x• = (y• : ● X) → isProp (x• ≡ y•)

    η•η•-case : (x y : X) → isProp (η• x ≡ η• y)
    η•η•-case x y h h' =
      sym (●-unlex-lex h)
      ∙ cong ●-unlex (●-preserves-isProp (X-isSet x y) (●-lex h) (●-lex h'))
      ∙ ●-unlex-lex h'

    η•-case : (x : X) → R (η• x)
    η•-case x = ind S η•η•-case' ∗-case' law-case'
      where
        S : ● X → 𝒱
        S y• = isProp (η• x ≡ y•)

        η•η•-case' : (y : X) → S (η• y)
        η•η•-case' y = η•η•-case x y

        ∗-case' : (abs : ⟨ ABS ⟩) → S (∗ abs)
        ∗-case' abs = isProp→isSet (●-isProp abs) (η• x) (∗ abs)

        law-case' : (y : X) (abs : ⟨ ABS ⟩) → PathP (λ i → S (law y abs i)) (η•η•-case' y) (∗-case' abs)
        law-case' y abs =
          isProp→PathP
            (λ _ → isPropIsProp)
            (η•η•-case' y)
            (∗-case' abs)

    ∗-case : (abs : ⟨ ABS ⟩) → R (∗ abs)
    ∗-case abs y• = isProp→isSet (●-isProp abs) (∗ abs) y•

    law-case : (x : X) (abs : ⟨ ABS ⟩) → PathP (λ i → R (law x abs i)) (η•-case x) (∗-case abs)
    law-case x abs i y• =
      isProp→PathP
        (λ j → isPropIsProp {A = law x abs j ≡ y•})
        (η•-case x y•)
        (∗-case abs y•)
        i

opaque
  ●-preserves-isSet : isSet X → isSet (● X)
  ●-preserves-isSet X-isSet x• y• = ●-isPropPath X-isSet x• y•
