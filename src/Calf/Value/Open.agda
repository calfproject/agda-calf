open import Calf.Value
open import Calf.Value.Product
open import Calf.Value.Sigma

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path using (compPathlEquiv; compPathrEquiv)
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Univalence
open import Cubical.Functions.FunExtEquiv

open import Cubical.Modalities.Modality

module Calf.Value.Open (φ : hProp _) where

◯ : 𝒱 → 𝒱
◯ X = (p : ⟨ φ ⟩) → X

◯Π : (⟨ φ ⟩ → 𝒱) → 𝒱
◯Π X = (p : ⟨ φ ⟩) → X p

η◦ : X → ◯ X
η◦ x _ = x

isModal : 𝒱 → 𝒱
isModal X = isEquiv (η◦ {X = X})

isModal◯Π : {X : ⟨ φ ⟩ → 𝒱} → isModal (◯Π X)
isModal◯Π {X = X} = isoToIsEquiv (iso η◦ join′ sec ret)
  where
    join′ : ◯ (◯Π X) → ◯Π X
    join′ x p = x p p

    sec : (x : ◯ (◯Π X)) → η◦ (join′ x) ≡ x
    sec x = funExt λ p → funExt λ p' → cong (λ a → x a p') (str φ p' p)

    ret : (x : ◯Π X) → join′ (η◦ x) ≡ x
    ret x = refl

opaque
  isModal◯ : isModal (◯ X)
  isModal◯ = isModal◯Π

◯Modality : Modality _
◯Modality .Modality.◯ = ◯
◯Modality .Modality.η = η◦
◯Modality .Modality.isModal = isModal
◯Modality .Modality.isPropIsModal = isPropIsEquiv η◦
◯Modality .Modality.◯-isModal = isModal◯
◯Modality .Modality.◯-elim {X} {Y} isModalY f x◦ =
  invIsEq (isModalY x◦) λ p →
  subst Y (funExt λ p' → cong x◦ (str φ p p')) (f (x◦ p))
◯Modality .Modality.◯-elim-β {X} {Y} isModalY f x =
  retIsEq (isModalY (η◦ x)) (subst Y refl (f x)) ∙ substRefl {B = Y} (f x)
◯Modality .Modality.◯-=-isModal x◦ x◦' =
  subst isModal (ua funExtEquiv) (isModal◯Π {X = λ p → x◦ p ≡ x◦' p})

open Modality ◯Modality public
  renaming
    ( ◯-elim to elim
    ; ◯-elim-β to elim-β
    ; ◯-=-isModal to ◯-≡-isModal
    ; Π-isModal to isModalΠ
    ; →-isModal to isModal→
    )
  using (isModal≡; ◯-equiv)

open import Cubical.Modalities.Extras ◯Modality public
  hiding (η-=-isModal)
  renaming
    ( map to map′
    ; map-∘ to map′-∘
    ; join to join′
    ; η-isNatural to η◦-isNatural
    )

open import Cubical.Modalities.Extras ◯Modality
  using (η-=-isModal)

map : (X → Y) → ◯ X → ◯ Y
map f x◦ p = f (x◦ p)

map′≡map : map′ {X} {Y} ≡ map
map′≡map = funExt λ f → sym (◯-rec-unique isModal◯ refl)

map-∘ : (f : X → Y) (g : Y → Z) (x◦ : ◯ X) →
  map g (map f x◦) ≡ map (g ∘ f) x◦
map-∘ f g x◦ = refl

join : ◯ (◯ X) → ◯ X
join x◦◦ p = x◦◦ p p

join′≡join : join′ {X} ≡ join
join′≡join = sym (◯-rec-unique isModal◯ refl)

isConnected→◯isContr : isConnected X → ◯ (isContr X)
isConnected→◯isContr c p .fst = c .fst p
isConnected→◯isContr c p .snd x = funExt⁻ (c .snd (λ _ → x)) p

◯isContr→isConnected : ◯ (isContr X) → isConnected X
◯isContr→isConnected h .fst p = h p .fst
◯isContr→isConnected h .snd x◦ = funExt λ p → h p .snd (x◦ p)

◯isModal : ⟨ φ ⟩ → isModal X
◯isModal p =
  isoToIsEquiv (iso η◦ (λ f → f p)
    (λ f → funExt λ q → cong f (str φ p q))
    (λ x → refl))

opaque
  isLex◯ : IsLex◯
  isLex◯ = reflection-isEquiv η-=-isModal (isConnectedMap-∘ₑ funExtEquiv isConnectedMapη)

opaque
  isSet◯ : isSet X → isSet (◯ X)
  isSet◯ = isSet◯-lex isLex◯

isPreorder◯ : isPreorder X → isPreorder (◯ X)
isPreorder◯ isPreorderX = isLocalΠ λ _ → isPreorderX

◯-pullback : {X Y Z : 𝒱} {f : X → Z} {g : Y → Z} →
  ◯ (Σ[ (x , y) ∈ X × Y ] (f x ≡ g y))
  ≃ (Σ[ (x◦ , y◦) ∈ ◯ X × ◯ Y ] (map f x◦ ≡ map g y◦))
◯-pullback {X} {Y} {Z} {f} {g} =
  ◯-pullback-lex isLex◯
  ∙ₑ Σ-cong-equiv-snd λ (x◦ , y◦) →
      compPathrEquiv (funExt⁻ (funExt⁻ map′≡map g) y◦)
    ∙ₑ compPathlEquiv (sym (funExt⁻ (funExt⁻ map′≡map f) x◦))


𝒱◦ : 𝒱₁
𝒱◦ = TypeWithStr _ isModal

𝒱◦-path : (X◦ X◦' : 𝒱◦) → ⟨ X◦ ⟩ ≡ ⟨ X◦' ⟩ → X◦ ≡ X◦'
𝒱◦-path X◦ X◦' = Σ≡Prop λ _ → isPropIsEquiv _

◯◦ : 𝒱 _ → 𝒱◦
◯◦ X = ◯ X , isModal◯
