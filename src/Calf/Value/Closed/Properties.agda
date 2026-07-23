module Calf.Value.Closed.Properties where

open import Calf.Core.Abstract
open import Calf.Value
open import Calf.Value.Closed.Base
open import Calf.Value.Closed.Lex

open import 1Lab.Set.Pi
open import Cubical.Foundations.CartesianKanOps
open import Cubical.Data.Sigma using (ΣPathP)

𝒱•-at-open-isContr : (X• : 𝒱•) → ⟨ ABS ⟩ → isContr ⟨ X• ⟩
𝒱•-at-open-isContr X• abs .fst = invIsEq (X• .snd) (∗ abs)
𝒱•-at-open-isContr X• abs .snd x =
  cong (invIsEq (X• .snd)) (sym (law x abs)) ∙ retIsEq (X• .snd) x

map-∘ : {X Y Z : 𝒱} (f : X → Y) (g : Y → Z) (x• : ● X) →
  map g (map f x•) ≡ map (g ∘ f) x•
map-∘ f g (η• x) = refl
map-∘ f g (∗ abs) = refl
map-∘ f g (law x abs i) = refl

η-fiber : {X : 𝒱} (x• : ● X) → ● (Σ[ x ∈ X ] η• x ≡ x•)
η-fiber (η• x) = η• (x , refl)
η-fiber (∗ abs) = ∗ abs
η-fiber (law x abs i) = law (x , λ j → law x abs (i ∧ j)) abs i

η-fiber-point
  : {X : 𝒱} (x• : ● X) (u : Σ[ x ∈ X ] η• x ≡ x•)
  → η-fiber x• ≡ η• u
η-fiber-point x• (x , abs) =
  J (λ y q → η-fiber y ≡ η• (x , q)) refl abs

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

●-map-const : {X Y : 𝒱} (x : X) (y• : ● Y) → map (λ _ → x) y• ≡ η• x
●-map-const x (η• y) = refl
●-map-const x (∗ abs) = sym (law x abs)
●-map-const x (law y abs i) j = law x abs (i ∧ ~ j)

●-map-isEquiv→connected-map
  : {X Y : 𝒱} (f : X → Y)
  → isEquiv (map f)
  → isConnectedMap f
●-map-isEquiv→connected-map f f•-isEquiv y .fst =
  ●-fiber-in f y (f•-isEquiv .equiv-proof (η• y) .fst)
●-map-isEquiv→connected-map f f•-isEquiv y .snd u• =
  cong (●-fiber-in f y) (f•-isEquiv .equiv-proof (η• y) .snd (●-fiber-out f y u•))
  ∙ ●-fiber-in-out f y u•

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


module _ where
  open import Calf.Value.Open using (◯)

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

module _
  {X Y Z : 𝒱} (X-set : isSet X) (Y-set : isSet Y) (Z-set : isSet Z)
  (f : X → Z) (g : Y → Z)
  where

  private
    P : 𝒱
    P = Σ[ x ∈ X ] Σ[ y ∈ Y ] (f x ≡ g y)

    Q : 𝒱
    Q = Σ[ x• ∈ ● X ] Σ[ y• ∈ ● Y ] (map f x• ≡ map g y•)

    P-isSet : isSet P
    P-isSet = isSetΣ X-set λ _ → isSetΣ Y-set λ _ → isProp→isSet (Z-set _ _)

    Q-isSet : isSet Q
    Q-isSet =
      isSetΣ (●-preserves-isSet X-set) λ _ →
      isSetΣ (●-preserves-isSet Y-set) λ _ →
      isProp→isSet (●-preserves-isSet Z-set _ _)

    Q-isProp-at : ⟨ ABS ⟩ → isProp Q
    Q-isProp-at abs =
      isPropΣ (●-isProp abs) λ _ →
      isPropΣ (●-isProp abs) λ _ →
      isProp→isSet (●-isProp abs) _ _

  ●-pullback-fwd : ● P → Q
  ●-pullback-fwd w =
      map (λ t → t .fst) w
    , map (λ t → t .snd .fst) w
    , map-∘ (λ t → t .fst) f w
      ∙ cong (λ h → map h w) (funExt (λ t → t .snd .snd))
      ∙ sym (map-∘ (λ t → t .snd .fst) g w)

  ●-pullback-inv : Q → ● P
  ●-pullback-inv (x• , y• , q) =
    bind (η-fiber x•) λ { (x , px) →
    bind (η-fiber y•) λ { (y , py) →
    map (λ r → x , y , r) (●-lex (cong (map f) px ∙ q ∙ sym (cong (map g) py))) } }

  private
    ●-pullback-ret : (w : ● P) → ●-pullback-inv (●-pullback-fwd w) ≡ w
    ●-pullback-ret =
      ●-elimProp _ (λ _ → ●-preserves-isSet P-isSet _ _)
        (λ { (x , y , p) →
          cong (map (λ r → x , y , r))
            (●-preserves-isProp (Z-set _ _)
              (●-lex (refl ∙ ●-pullback-fwd (η• (x , y , p)) .snd .snd ∙ refl))
              (η• p)) })
        (λ _ → refl)

    ●-pullback-sec : (w : Q) → ●-pullback-fwd (●-pullback-inv w) ≡ w
    ●-pullback-sec (x• , y• , q) =
      ●-elimProp R R-isProp η•-caseY (λ abs _ _ → Q-isProp-at abs _ _) y• x• q
      where
        R : ● Y → 𝒱
        R y• = (x• : ● X) (q : map f x• ≡ map g y•)
             → ●-pullback-fwd (●-pullback-inv (x• , y• , q)) ≡ (x• , y• , q)

        R-isProp : (y• : ● Y) → isProp (R y•)
        R-isProp y• = isPropΠ2 λ _ _ → Q-isSet _ _

        η•-caseY : (y : Y) → R (η• y)
        η•-caseY y = ●-elimProp S S-isProp η•-caseX (λ abs _ → Q-isProp-at abs _ _)
          where
            S : ● X → 𝒱
            S x• = (q : map f x• ≡ η• (g y))
                 → ●-pullback-fwd (●-pullback-inv (x• , η• y , q)) ≡ (x• , η• y , q)

            S-isProp : (x• : ● X) → isProp (S x•)
            S-isProp x• = isPropΠ λ _ → Q-isSet _ _

            η•-caseX : (x : X) → S (η• x)
            η•-caseX x q =
              ΣPathP
                ( map-∘ mk (λ t → t .fst) e ∙ ●-map-const x e
                , ΣPathP
                  ( map-∘ mk (λ t → t .snd .fst) e ∙ ●-map-const y e
                  , isProp→PathP (λ i → ●-preserves-isSet Z-set _ _) _ _ ) )
              where
                mk : (f x ≡ g y) → P
                mk r = x , y , r
                e : ● (f x ≡ g y)
                e = ●-lex (refl ∙ q ∙ refl)

  ●-pullback-Iso : Iso (● P) Q
  ●-pullback-Iso = iso ●-pullback-fwd ●-pullback-inv ●-pullback-sec ●-pullback-ret

opaque
  isSet● : isSet X → isSet (● X)
  isSet● X-isSet x• y• = ●-isPropPath X-isSet x• y•

opaque
  unfolding 𝟚

  isPreorder● : isPreorder X → isPreorder (● X)
  isPreorder● isPreorderX =
    isSet∧isDiscrete→isPreorder (isSet● (isPreorder→isSet isPreorderX)) (⊑-beh refl)
