module Calf.Value.Closed where

open import Calf.Core.Abstract
open import Calf.Value
open import Calf.Value.Open as ◯ using (◯)
open import Calf.Value.Product
open import Calf.Value.Sigma
open import Calf.Value.Unit

open import 1Lab.Set.Pi
open import Cubical.Foundations.CartesianKanOps
open import Cubical.Foundations.Path using (compPathlEquiv; compPathrEquiv)
open import Cubical.Foundations.Univalence using (hPropExt)

open import Cubical.Foundations.Equiv.PathSplit using (fromIsEquiv; toIsEquiv)
open import Cubical.Data.Unit using (UnitToType≃)
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

opaque
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

●Modality : Modality _
●Modality .Modality.◯ = ●
●Modality .Modality.η = η•
●Modality .Modality.isModal = isModal
●Modality .Modality.isPropIsModal = isPropIsEquiv η•
●Modality .Modality.◯-isModal = isModal●
●Modality .Modality.◯-elim = elim
●Modality .Modality.◯-elim-β _ _ _ = refl
●Modality .Modality.◯-=-isModal x• x•' =
  isConnected◯→isModal● (isContrΠ λ abs → isContr→isContrPath (◯-isConnected abs) x• x•')

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

●-𝟚 : ● (𝟚 → X) → (𝟚 → ● X)
●-𝟚 = elim (λ _ → isModalΠ λ _ → isModal●) (λ f → η• ∘ f)

opaque
  ●-𝟚-β : (p• : ● (𝟚 → X)) (𝕚 : 𝟚) → ●-𝟚 p• 𝕚 ≡ map (λ f → f 𝕚) p•
  ●-𝟚-β {X} p• 𝕚 =
    elim {Y = λ p• → ●-𝟚 p• 𝕚 ≡ map (λ f → f 𝕚) p•}
      (λ _ → ●-≡-isModal _ _)
      (λ _ → refl)
      p•

opaque
  unfolding 𝟚

  ●-𝟚-isEquiv : isEquiv (●-𝟚 {X})
  ●-𝟚-isEquiv {X} =
    subst isEquiv
      (funExt λ p• → funExt λ 𝕚 →
        funExt⁻ (funExt⁻ map′≡map (λ f → f 𝕚)) p• ∙ sym (●-𝟚-β p• 𝕚))
      (equivIsEquiv (●-equiv (UnitToType≃ X) ∙ₑ invEquiv (UnitToType≃ (● X))))

module _ {X : 𝒱} (preX : isPreorder X) where
  private
    thinX : isThin X
    thinX = isPreorder→isThin preX

    pre-abs : ⟨ ABS ⟩ → isPreorder (● X)
    pre-abs abs = isProp→isPreorder (◯-isProp● abs)

    map2● : {A B C : 𝒱} → (A → B → C) → ● A → ● B → ● C
    map2● f a• b• = elim (λ _ → isModal●) (λ a → map (f a) b•) a•

    ⊑Σ : {W : 𝒱} → W → W → 𝒱
    ⊑Σ {W} x x' = Σ[ p ∈ (𝟚 → W) ] ((p 0𝟚 ≡ x) × (p 1𝟚 ≡ x'))

    ⊑Σ-Iso : {W : 𝒱} {x x' : W} → Iso (x ⊑ x') (⊑Σ x x')
    ⊑Σ-Iso .Iso.fun e = e .path , e .path₀ , e .path₁
    ⊑Σ-Iso .Iso.inv (p , h₀ , h₁) = record { path = p ; path₀ = h₀ ; path₁ = h₁ }
    ⊑Σ-Iso .Iso.rightInv _ = refl
    ⊑Σ-Iso .Iso.leftInv _ = refl

    isModal⊑Σ : {x• y• : ● X} → isModal (⊑Σ x• y•)
    isModal⊑Σ =
      isModalΣ (isModalΠ λ _ → isModal●) λ _ →
      isModalΣ (●-≡-isModal _ _) λ _ → ●-≡-isModal _ _

    ⊑Σ-η : {a b : X} → ⊑Σ a b → ⊑Σ (η• a) (η• b)
    ⊑Σ-η = map-Σ (η• ∘_) λ _ → map-Σ (cong η•) λ _ → cong η•

    ⊑Σ-η-connected : {a b : X} → isConnectedMap (⊑Σ-η {a} {b})
    ⊑Σ-η-connected =
      isConnectedMapΣ (isConnectedMap-∘ₑ (●-𝟚 , ●-𝟚-isEquiv) isConnectedMapη)
        λ _ → isConnectedMapΣ (isConnectedMap-∘ₑ (◯-≡-≃ isLex●) isConnectedMapη)
          λ _ → isConnectedMap-∘ₑ (◯-≡-≃ isLex●) isConnectedMapη

    ⊑-● : {a b : X} → ● (a ⊑ b) ≃ (η• a ⊑ η• b)
    ⊑-● =
        ●-equiv (isoToEquiv ⊑Σ-Iso)
      ∙ₑ reflection-≃ isModal⊑Σ ⊑Σ-η-connected
      ∙ₑ invEquiv (isoToEquiv ⊑Σ-Iso)

  isThin● : isThin (● X)
  isThin● =
    ind-prop _ (λ _ → isPropΠ λ _ → isPropIsProp)
      (λ a → ind-prop _ (λ _ → isPropIsProp)
        (λ b → isOfHLevelRespectEquiv 1 ⊑-● (isProp● (thinX a b)))
        (λ abs → isPreorder→isThin (pre-abs abs) _ _))
      (λ abs _ → isPreorder→isThin (pre-abs abs) _ _)

  ⊑-trans● : (x• y• z• : ● X) → x• ⊑ y• → y• ⊑ z• → x• ⊑ z•
  ⊑-trans● =
    ind-prop _ (λ x• → isPropΠ2 λ y• z• → isPropΠ2 λ _ _ → isThin● x• z•)
      (λ a → ind-prop _ (λ y• → isPropΠ λ z• → isPropΠ2 λ _ _ → isThin● (η• a) z•)
        (λ b → ind-prop _ (λ z• → isPropΠ2 λ _ _ → isThin● (η• a) z•)
          (λ c e f →
            equivFun ⊑-● (map2● (λ u v → ⊑-trans preX u v) (invEq ⊑-● e) (invEq ⊑-● f)))
          (λ abs → ⊑-trans (pre-abs abs)))
        (λ abs z• → ⊑-trans (pre-abs abs)))
      (λ abs y• z• → ⊑-trans (pre-abs abs))

  opaque
    unfolding Fᴾ

    isPreorder● : isPreorder (● X)
    isPreorder● transitive =
      isThin∧Transitive[⊑]→isPathTransitive isThin●
        (λ {x•} {y•} {z•} → ⊑-trans● x• y• z•) _
    isPreorder● thin =
      transport (sym isBoundarySeparated≡isThin) isThin● _
    isPreorder● hset =
      fromIsEquiv _ $ equivIsEquiv $
      compEquiv (UnitToType≃ _)
        (_ , toIsEquiv _
          (transport (sym isS¹Null≡isSet) (isSet● (isPreorder→isSet preX)) _))

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
