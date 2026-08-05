module Calf.Value.Closed where

open import Calf.Core.Abstract
open import Calf.Value
open import Calf.Value.Open as ◯ using (◯)
open import Calf.Value.Sigma
open import Calf.Value.Unit

open import 1Lab.Set.Pi
open import Cubical.Foundations.CartesianKanOps
open import Cubical.Foundations.Path using (compPathlEquiv; compPathrEquiv)
open import Cubical.Foundations.Univalence using (hPropExt)

open import Cubical.Modalities.Modality

data ● (X : 𝒱) : 𝒱 where
  η• : (x : X) → ● X
  ∗ : (abs : ⟨ ABS ⟩) → ● X
  law : (x : X) (abs : ⟨ ABS ⟩) → η• x ≡ ∗ abs

ind : (Y : ● X → 𝒱)
  → (η•-case : (x : X) → Y (η• x))
  → (∗-case : (abs : ⟨ ABS ⟩) → Y (∗ abs))
  → (law-case : (x : X) (abs : ⟨ ABS ⟩) → PathP (λ i → Y (law x abs i)) (η•-case x) (∗-case abs))
  → (x• : ● X) → Y x•
ind Y η•-case ∗-case law-case (η• x) = η•-case x
ind Y η•-case ∗-case law-case (∗ abs) = ∗-case abs
ind Y η•-case ∗-case law-case (law x abs i) = law-case x abs i

ind-prop : (Y : ● X → 𝒱)
  → ((x• : ● X) → isProp (Y x•))
  → ((x : X) → Y (η• x))
  → ((abs : ⟨ ABS ⟩) → Y (∗ abs))
  → (x• : ● X) → Y x•
ind-prop Y isPropY η•-case ∗-case =
  ind Y η•-case ∗-case
    (λ x abs → isProp→PathP (λ i → isPropY (law x abs i)) (η•-case x) (∗-case abs))

isModal : 𝒱 → 𝒱
isModal X = isEquiv (η• {X})

isConnected : 𝒱 → 𝒱
isConnected X = isContr (● X)

◯[x•≡∗] : (abs : ⟨ ABS ⟩) → (x• : ● X) → x• ≡ ∗ abs
◯[x•≡∗] abs (η• x) = law x abs
◯[x•≡∗] abs (∗ abs') = cong ∗ (str ABS abs' abs)
◯[x•≡∗] abs (law x abs' i) j =
  hcomp
    (λ k → λ
      { (i = i0) → law x abs (j ∧ k)
      ; (i = i1) → law x (str ABS abs' abs j) k
      ; (j = i0) → law x abs' (i ∧ k)
      ; (j = i1) → law x abs k })
    (η• x)

◯-isConnected : ◯ (isConnected X)
◯-isConnected abs = ∗ abs , sym ∘ ◯[x•≡∗] abs

◯-isProp● : ◯ (isProp (● X))
◯-isProp● = isContr→isProp ∘ ◯-isConnected

map : (X → Y) → ● X → ● Y
map f (η• x) = η• (f x)
map f (∗ abs) = ∗ abs
map f (law x abs i) = law (f x) abs i

map-∘ : (f : X → Y) (g : Y → Z) (x• : ● X) → map g (map f x•) ≡ map (g ∘ f) x•
map-∘ f g (η• x) = refl
map-∘ f g (∗ abs) = refl
map-∘ f g (law x abs i) = refl

join : ● (● X) → ● X
join (η• x) = x
join (∗ abs) = ∗ abs
join (law x abs i) = ◯[x•≡∗] abs x i

opaque
  isModal● : isModal (● X)
  isModal● = isoToIsEquiv (iso η• join sec ret)
    where
      ret : (x• : ● X) → join (η• x•) ≡ x•
      ret x = refl

      sec : (x•• : ● (● X)) → η• (join x••) ≡ x••
      sec (η• x•) = refl
      sec (∗ abs) = law (∗ abs) abs
      sec (law x• abs i) =
        isProp→PathP
          (λ i → isProp→isSet (◯-isProp● abs)
            (η• (◯[x•≡∗] abs x• i))
            (law x• abs i))
          refl
          (law (∗ abs) abs)
          i

opaque
  isModal●→isConnected◯ : isModal X → ◯.isConnected X
  isModal●→isConnected◯ X-modal =
    isContrΠ λ abs → isOfHLevelRespectEquiv 0 (invEquiv (η• , X-modal)) (◯-isConnected abs)

isConnected◯→isModal● : ◯.isConnected X → isModal X
isConnected◯→isModal● {X} c = isoToIsEquiv (iso η• inv sec ret)
  where
    ◯[isContrX] : ◯ (isContr X)
    ◯[isContrX] = ◯.isConnected→◯isContr c

    inv : ● X → X
    inv = ind _ id (fst ∘ ◯[isContrX]) (λ x abs → sym (◯[isContrX] abs .snd x))

    ret : (x : X) → inv (η• x) ≡ x
    ret x = refl

    sec : (x• : ● X) → η• (inv x•) ≡ x•
    sec = ind (λ x• → η• (inv x•) ≡ x•)
      (λ x → refl)
      (λ abs → law (inv (∗ abs)) abs)
      (λ x abs → isProp→PathP
        (λ i → isProp→isSet (◯-isProp● abs) (η• (inv (law x abs i))) (law x abs i))
        refl
        (law (inv (∗ abs)) abs))

opaque
  isModal●≡isConnected◯ : isModal X ≡ ◯.isConnected X
  isModal●≡isConnected◯ =
    hPropExt (isPropIsEquiv η•) isPropIsContr
      isModal●→isConnected◯ isConnected◯→isModal●

elim : {X : 𝒱} {Y : ● X → 𝒱}
  → ((x : ● X) → isModal (Y x)) → ((x : X) → Y (η• x)) → (x : ● X) → Y x
elim {X} {Y} isModalY f =
  ind Y
    f
    (λ abs → invIsEq (isModalY (∗ abs)) (∗ abs))
    (λ x abs →
      isProp→PathP
        (λ i → isContr→isProp
          (◯.isConnected→◯isContr (isModal●→isConnected◯ (isModalY (law x abs i))) abs))
        (f x)
        (invIsEq (isModalY (∗ abs)) (∗ abs)))

opaque
  elim′ : {X : 𝒱} {Y : ● X → 𝒱}
    → ((x : ● X) → isModal (Y x)) → ((x : X) → Y (η• x)) → (x : ● X) → Y x
  elim′ = elim

●Modality : Modality _
●Modality .Modality.◯ = ●
●Modality .Modality.η = η•
●Modality .Modality.isModal = isModal
●Modality .Modality.isPropIsModal = isPropIsEquiv η•
●Modality .Modality.◯-isModal = isModal●
●Modality .Modality.◯-elim = elim
●Modality .Modality.◯-elim-β isModalY f x = refl
●Modality .Modality.◯-=-isModal x• x•' =
  isConnected◯→isModal● (isContrΠ λ abs → isContr→isContrPath (◯-isConnected abs) x• x•')

open Modality ●Modality public
  renaming
    ( ◯-elim-β to elim-β
    ; ◯-=-isModal to ●-≡-isModal
    ; Π-isModal to isModalΠ
    ; →-isModal to isModal→
    ; ◯-equiv to ●-equiv
    )
  using (isModal≡)

open import Cubical.Modalities.Extras ●Modality public
  renaming
    ( map to map′
    ; map-∘ to map′-∘
    ; join to join′
    ; η-isNatural to η•-isNatural
    ; ○Σ○≃○Σ to ●Σ●≃●Σ
    )
  hiding (isConnected)

map′≡map : map′ {X} {Y} ≡ map
map′≡map = funExt λ f → sym (◯-rec-unique isModal● refl)

join′≡join : join′ {X} ≡ join
join′≡join = sym (◯-rec-unique isModal● refl)

opaque
  isLex● : IsLex◯
  isLex● {X} {x} {x'} =
    subst isEquiv
      (funExt (Modality.◯-elim ●Modality
        (λ _ → Modality.isModal≡ ●Modality (η-=-isModal {x = x} {x' = x'}))
        (λ h → sym (Modality.◯-rec-β ●Modality η-=-isModal (cong η•) h))))
      (equivIsEquiv ●-≡-equiv)
    where
      ●-encode : ∀ {X} → X → ● X → 𝒱
      ●-encode x (η• x') = ● (x ≡ x')
      ●-encode x (∗ abs) = ⊤
      ●-encode x (law x' abs i) = isContr→≡Unit (◯-isConnected {X = x ≡ x'} abs) i

      ●-lex : ∀ {X} {x : X} {y : ● X} → η• x ≡ y → ●-encode x y
      ●-lex {x = x} h = J (λ y _ → ●-encode x y) (η• refl) h

      ●-unlex : ∀ {X} {x x' : X} → ● (x ≡ x') → η• x ≡ η• x'
      ●-unlex (η• h) = cong η• h
      ●-unlex {x = x} {x'} (∗ abs) = law x abs ∙ sym (law x' abs)
      ●-unlex {x = x} {x'} (law h abs i) =
        isProp→isSet (◯-isProp● abs) (η• x) (η• x')
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
              (λ i → isProp→isSet (◯-isProp● abs)
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
        ◯-isProp● abs
          (●-lex (law x abs ∙ sym (law x' abs)))
          (∗ abs)
      ●-lex-unlex {x = x} {x'} (law h abs i) =
        isProp→PathP
          (λ i → isProp→isSet (◯-isProp● abs)
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

      ●-≡-equiv : {x x' : X} → ● (x ≡ x') ≃ (η• x ≡ η• x')
      ●-≡-equiv = isoToEquiv (iso ●-unlex ●-lex ●-unlex-lex ●-lex-unlex)


opaque
  isSet● : isSet X → isSet (● X)
  isSet● = isSet◯-lex isLex●

●-pullback : {X Y Z : 𝒱} {f : X → Z} {g : Y → Z}
  → ● (Σ[ x ∈ X ] Σ[ y ∈ Y ] (f x ≡ g y))
  ≃ (Σ[ x• ∈ ● X ] Σ[ y• ∈ ● Y ] (map f x• ≡ map g y•))
●-pullback {f = f} {g = g} =
  ◯-pullback-lex isLex●
  ∙ₑ Σ-cong-equiv-snd λ x• → Σ-cong-equiv-snd λ y• →
      compPathrEquiv (funExt⁻ (funExt⁻ map′≡map g) y•)
    ∙ₑ compPathlEquiv (sym (funExt⁻ (funExt⁻ map′≡map f) x•))


𝒱• : 𝒱₁
𝒱• = TypeWithStr _ isModal

𝒱•-path : (X• X•' : 𝒱•) → ⟨ X• ⟩ ≡ ⟨ X•' ⟩ → X• ≡ X•'
𝒱•-path X• X•' = Σ≡Prop λ _ → isPropIsEquiv _

●• : 𝒱 → 𝒱•
●• X = ● X , isModal●
