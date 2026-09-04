open import 1Lab.Set.Pi
open import Cubical.Foundations.CartesianKanOps
open import Cubical.Foundations.Equiv.Properties using (congEquiv)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Path using (compPathlEquiv; compPathrEquiv)
open import Cubical.Foundations.Univalence using (hPropExt)

open import Cubical.Foundations.Equiv.PathSplit using (fromIsEquiv; toIsEquiv)
open import Cubical.Data.Unit using (UnitToType≃)
open import Cubical.Modalities.Modality

module Calf.Value.Closed (φ : hProp _) where

open import Calf.Value
open import Calf.Value.Open φ as ◯ using (◯)
open import Calf.Value.Product
open import Calf.Value.Sigma
open import Calf.Value.Unit

data ● (X : 𝒱) : 𝒱 where
  η• : (x : X) → ● X
  ∗ : (p : ⟨ φ ⟩) → ● X
  push : (x : X) (p : ⟨ φ ⟩) → η• x ≡ ∗ p

ind : (Y : ● X → 𝒱)
  → (η•-case : (x : X) → Y (η• x))
  → (∗-case : (p : ⟨ φ ⟩) → Y (∗ p))
  → (push-case : (x : X) (p : ⟨ φ ⟩) → PathP (λ i → Y (push x p i)) (η•-case x) (∗-case p))
  → (x• : ● X) → Y x•
ind Y η•-case ∗-case push-case (η• x) = η•-case x
ind Y η•-case ∗-case push-case (∗ p) = ∗-case p
ind Y η•-case ∗-case push-case (push x p i) = push-case x p i

opaque
  ind-prop : (Y : ● X → 𝒱)
    → ((x• : ● X) → isProp (Y x•))
    → ((x : X) → Y (η• x))
    → ((p : ⟨ φ ⟩) → Y (∗ p))
    → (x• : ● X) → Y x•
  ind-prop Y isPropY η•-case ∗-case =
    ind Y η•-case ∗-case
      (λ x p → isProp→PathP (λ i → isPropY (push x p i)) (η•-case x) (∗-case p))

isModal : 𝒱 → 𝒱
isModal X = isEquiv (η• {X})

isConnected : 𝒱 → 𝒱
isConnected X = isContr (● X)

∗-open : (p : ⟨ φ ⟩) → (x• : ● X) → x• ≡ ∗ p
∗-open p (η• x) = push x p
∗-open p (∗ p') = cong ∗ (str φ p' p)
∗-open p (push x p' i) j =
  hcomp
    (λ k → λ
      { (i = i0) → push x p (j ∧ k)
      ; (i = i1) → push x (str φ p' p j) k
      ; (j = i0) → push x p' (i ∧ k)
      ; (j = i1) → push x p k })
    (η• x)

◯-isConnected : ◯ (isConnected X)
◯-isConnected p = ∗ p , sym ∘ ∗-open p

◯-isProp● : ◯ (isProp (● X))
◯-isProp● = isContr→isProp ∘ ◯-isConnected

map : (X → Y) → ● X → ● Y
map f (η• x) = η• (f x)
map f (∗ p) = ∗ p
map f (push x p i) = push (f x) p i

map-∘ : (f : X → Y) (g : Y → Z) (x• : ● X) → map g (map f x•) ≡ map (g ∘ f) x•
map-∘ f g (η• x) = refl
map-∘ f g (∗ p) = refl
map-∘ f g (push x p i) = refl

join : ● (● X) → ● X
join (η• x) = x
join (∗ p) = ∗ p
join (push x p i) = ∗-open p x i

opaque
  isModal● : isModal (● X)
  isModal● = isoToIsEquiv (iso η• join sec ret)
    where
      ret : (x• : ● X) → join (η• x•) ≡ x•
      ret x = refl

      sec : (x•• : ● (● X)) → η• (join x••) ≡ x••
      sec (η• x•) = refl
      sec (∗ p) = push (∗ p) p
      sec (push x• p i) =
        isProp→PathP
          (λ i → isProp→isSet (◯-isProp● p)
            (η• (∗-open p x• i))
            (push x• p i))
          refl
          (push (∗ p) p)
          i

opaque
  isModal●→isConnected◯ : isModal X → ◯.isConnected X
  isModal●→isConnected◯ X-modal =
    isContrΠ λ p → isOfHLevelRespectEquiv 0 (invEquiv (η• , X-modal)) (◯-isConnected p)

isConnected◯→isModal● : ◯.isConnected X → isModal X
isConnected◯→isModal● {X} c = isoToIsEquiv (iso η• inv sec ret)
  where
    ◯-isContr : ◯ (isContr X)
    ◯-isContr = ◯.isConnected→◯isContr c

    inv : ● X → X
    inv = ind _ id (fst ∘ ◯-isContr) (λ x p → sym (◯-isContr p .snd x))

    ret : (x : X) → inv (η• x) ≡ x
    ret x = refl

    sec : (x• : ● X) → η• (inv x•) ≡ x•
    sec = ind (λ x• → η• (inv x•) ≡ x•)
      (λ x → refl)
      (λ p → push (inv (∗ p)) p)
      (λ x p → isProp→PathP
        (λ i → isProp→isSet (◯-isProp● p) (η• (inv (push x p i))) (push x p i))
        refl
        (push (inv (∗ p)) p))

elim : {X : 𝒱} {Y : ● X → 𝒱}
  → ((x : ● X) → isModal (Y x)) → ((x : X) → Y (η• x)) → (x : ● X) → Y x
elim {X} {Y} isModalY f =
  ind Y
    f
    (λ p → invIsEq (isModalY (∗ p)) (∗ p))
    (λ x p →
      isProp→PathP
        (λ i → isContr→isProp
          (◯.isConnected→◯isContr (isModal●→isConnected◯ (isModalY (push x p i))) p))
        (f x)
        (invIsEq (isModalY (∗ p)) (∗ p)))

●Modality : Modality _
●Modality .Modality.◯ = ●
●Modality .Modality.η = η•
●Modality .Modality.isModal = isModal
●Modality .Modality.isPropIsModal = isPropIsEquiv η•
●Modality .Modality.◯-isModal = isModal●
●Modality .Modality.◯-elim = elim
●Modality .Modality.◯-elim-β _ _ _ = refl
●Modality .Modality.◯-=-isModal x• x•' =
  isConnected◯→isModal● (isContrΠ λ p → isContr→isContrPath (◯-isConnected p) x• x•')

open Modality ●Modality public
  renaming
    ( ◯-elim-β to elim-β
    ; ◯-=-isModal to ●-≡-isModal
    ; Π-isModal to isModalΠ
    ; →-isModal to isModal→
    ; ◯-equiv to ●-equiv
    ; ◯-preservesProp to isProp●
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

opaque
  map′≡map : map′ {X} {Y} ≡ map
  map′≡map = funExt λ f → sym (◯-rec-unique isModal● refl)

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
      ●-encode x (∗ p) = ⊤
      ●-encode x (push x' p i) = isContr→≡Unit (◯-isConnected {X = x ≡ x'} p) i

      ●-lex : ∀ {X} {x : X} {y : ● X} → η• x ≡ y → ●-encode x y
      ●-lex {x = x} h = J (λ y _ → ●-encode x y) (η• refl) h

      ●-unlex : ∀ {X} {x x' : X} → ● (x ≡ x') → η• x ≡ η• x'
      ●-unlex (η• h) = cong η• h
      ●-unlex {x = x} {x'} (∗ p) = push x p ∙ sym (push x' p)
      ●-unlex {x = x} {x'} (push h p i) =
        isProp→isSet (◯-isProp● p) (η• x) (η• x')
          (cong η• h)
          (push x p ∙ sym (push x' p))
          i

      ●-unlex′ : ∀ {X} {x : X} {y : ● X} → ●-encode x y → η• x ≡ y
      ●-unlex′ {X} {x} {y} e =
        ind R η•-case ∗-case push-case y e
        where
        R : ● X → 𝒱
        R y = ●-encode x y → η• x ≡ y

        η•-case : (x' : X) → R (η• x')
        η•-case x' e = ●-unlex e

        ∗-case : (p : ⟨ φ ⟩) → R (∗ p)
        ∗-case p _ = push x p

        push-case : (x' : X) (p : ⟨ φ ⟩) → PathP (λ i → R (push x' p i)) (η•-case x') (∗-case p)
        push-case x' p =
          funext-dep-i0 λ e →
            isProp→PathP
              (λ i → isProp→isSet (◯-isProp● p)
                (η• x)
                (push x' p i))
              (η•-case x' e)
              (∗-case p (coe0→1 (λ i → ●-encode x (push x' p i)) e))

      ●-lex-unlex : ∀ {X} {x x' : X} (e : ● (x ≡ x')) → ●-lex (●-unlex e) ≡ e
      ●-lex-unlex {x = x} (η• h) =
        J
          (λ x' h → ●-lex (cong η• h) ≡ η• h)
          (JRefl {x = η• x} (λ y _ → ●-encode x y) (η• refl))
          h
      ●-lex-unlex {x = x} {x'} (∗ p) =
        ◯-isProp● p
          (●-lex (push x p ∙ sym (push x' p)))
          (∗ p)
      ●-lex-unlex {x = x} {x'} (push h p i) =
        isProp→PathP
          (λ i → isProp→isSet (◯-isProp● p)
            (●-lex (●-unlex (push h p i)))
            (push h p i))
          (●-lex-unlex (η• h))
          (●-lex-unlex (∗ p))
          i

      ●-unlex-lex : ∀ {X} {x x' : X} (h : η• x ≡ η• x') → ●-unlex (●-lex h) ≡ h
      ●-unlex-lex {X} {x} h =
        J
          (λ y h → ●-unlex′ (●-lex h) ≡ h)
          (cong
            (λ e → ●-unlex′ {X = X} {x = x} {y = η• x} e)
            (JRefl {x = η• x} (λ y _ → ●-encode x y) (η• {X = x ≡ x} refl)))
          h

      ●-≡-equiv : {x x' : X} → ● (x ≡ x') ≃ (η• x ≡ η• x')
      ●-≡-equiv = isoToEquiv (iso ●-unlex ●-lex ●-unlex-lex ●-lex-unlex)

opaque
  isSet● : isSet X → isSet (● X)
  isSet● = isSet◯-lex isLex●

opaque
  unfolding 𝟚

  isPreorder● : isPreorder X → isPreorder (● X)
  isPreorder● isPreorderX =
    isSet∧isDiscrete→isPreorder
      (isSet● (isPreorder→isSet isPreorderX))
      (BEH⇒isDiscrete refl)

module _ {X Y Z : 𝒱} {f : X → Z} {g : Y → Z} where
  ●-pullback :
      ● (Σ[ (x , y) ∈ X × Y ] (f x ≡ g y))
    ≃ (Σ[ (x• , y•) ∈ ● X × ● Y ] (map f x• ≡ map g y•))
  ●-pullback =
    ◯-pullback-lex isLex●
    ∙ₑ Σ-cong-equiv-snd λ (x• , y•) →
        compPathrEquiv (funExt⁻ (funExt⁻ map′≡map g) y•)
      ∙ₑ compPathlEquiv (sym (funExt⁻ (funExt⁻ map′≡map f) x•))

  ●-pullback-β₁ :
    (u : Σ[ (x , y) ∈ X × Y ] (f x ≡ g y))
    → equivFun ●-pullback (η• u) .fst .fst ≡ η• (u .fst .fst)
  ●-pullback-β₁ u = cong (fst ∘ fst) (◯-pullback-lex-β isLex● u)

  ●-pullback-β₂ :
    (u : Σ[ (x , y) ∈ X × Y ] (f x ≡ g y))
    → equivFun ●-pullback (η• u) .fst .snd ≡ η• (u .fst .snd)
  ●-pullback-β₂ u = cong (snd ∘ fst) (◯-pullback-lex-β isLex● u)

𝒱• : 𝒱₁
𝒱• = TypeWithStr _ isModal

𝒱•-path : (X• X•' : 𝒱•) → ⟨ X• ⟩ ≡ ⟨ X•' ⟩ → X• ≡ X•'
𝒱•-path X• X•' = Σ≡Prop λ _ → isPropIsEquiv _

●• : 𝒱 → 𝒱•
●• X = ● X , isModal●
