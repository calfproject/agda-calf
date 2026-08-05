open import Calf.Core.Abstract
open import Calf.Value
open import Calf.Value.Sigma

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path using (compPathlEquiv; compPathrEquiv)
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Univalence
open import Cubical.Functions.FunExtEquiv

open import Cubical.Modalities.Modality

module Calf.Value.Open where

◯ : 𝒱 → 𝒱
◯ X = (abs : ⟨ ABS ⟩) → X

◯' : (⟨ ABS ⟩ → 𝒱) → 𝒱
◯' X = (abs : ⟨ ABS ⟩) → X abs

η◦ : X → ◯ X
η◦ x _ = x

isModal : 𝒱 → 𝒱
isModal X = isEquiv (η◦ {X = X})

◯'-isModal : {X : ⟨ ABS ⟩ → 𝒱} → isModal (◯' X)
◯'-isModal {X = X} = isoToIsEquiv (iso η◦ join' sec ret)
  where
    join' : ◯ (◯' X) → ◯' X
    join' x abs = x abs abs

    sec : (x : ◯ (◯' X)) → η◦ (join' x) ≡ x
    sec x = funExt λ abs → funExt λ abs' → cong (λ a → x a abs') (str ABS abs' abs)

    ret : (x : ◯' X) → join' (η◦ x) ≡ x
    ret x = refl

isModal◯ : isModal (◯ X)
isModal◯ = ◯'-isModal

◯Modality : Modality _
◯Modality .Modality.◯ = ◯
◯Modality .Modality.η = η◦
◯Modality .Modality.isModal = isModal
◯Modality .Modality.isPropIsModal = isPropIsEquiv η◦
◯Modality .Modality.◯-isModal = isModal◯
◯Modality .Modality.◯-elim {X} {Y} isModalY f x◦ =
  invIsEq (isModalY x◦) λ abs →
  subst Y (funExt λ abs' → cong x◦ (str ABS abs abs')) (f (x◦ abs))
◯Modality .Modality.◯-elim-β {X} {Y} isModalY f x =
  retIsEq (isModalY (η◦ x)) (subst Y refl (f x)) ∙ substRefl {B = Y} (f x)
◯Modality .Modality.◯-=-isModal x◦ x◦' =
  subst isModal (ua funExtEquiv) (◯'-isModal {X = λ abs → x◦ abs ≡ x◦' abs})

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
map f x◦ abs = f (x◦ abs)

map′≡map : map′ {X} {Y} ≡ map
map′≡map = funExt λ f → sym (◯-rec-unique isModal◯ refl)

map-∘ : (f : X → Y) (g : Y → Z) (x◦ : ◯ X) →
  map g (map f x◦) ≡ map (g ∘ f) x◦
map-∘ f g x◦ = refl

join : ◯ (◯ X) → ◯ X
join x◦◦ abs = x◦◦ abs abs

join′≡join : join′ {X} ≡ join
join′≡join = sym (◯-rec-unique isModal◯ refl)

isConnected→◯isContr : isConnected X → ◯ (isContr X)
isConnected→◯isContr c abs .fst = c .fst abs
isConnected→◯isContr c abs .snd x = funExt⁻ (c .snd (λ _ → x)) abs

◯isContr→isConnected : ◯ (isContr X) → isConnected X
◯isContr→isConnected h .fst abs = h abs .fst
◯isContr→isConnected h .snd x◦ = funExt λ abs → h abs .snd (x◦ abs)

◯isModal : ⟨ ABS ⟩ → isModal X
◯isModal abs =
  isoToIsEquiv (iso η◦ (λ f → f abs)
    (λ f → funExt λ q → cong f (str ABS abs q))
    (λ x → refl))

opaque
  isLex◯ : IsLex◯
  isLex◯ =
    subst isEquiv
      (funExt $
        Modality.◯-elim ◯Modality
          (λ _ → Modality.isModal≡ ◯Modality η-=-isModal)
          (sym ∘ Modality.◯-rec-β ◯Modality η-=-isModal (cong η◦)))
      (equivIsEquiv funExtEquiv)

opaque
  isSet◯ : isSet X → isSet (◯ X)
  isSet◯ = isSet◯-lex isLex◯

◯-pullback : {X Y Z : 𝒱} {f : X → Z} {g : Y → Z} →
  ◯ (Σ[ x ∈ X ] Σ[ y ∈ Y ] (f x ≡ g y))
  ≃ (Σ[ x◦ ∈ ◯ X ] Σ[ y◦ ∈ ◯ Y ] (map f x◦ ≡ map g y◦))
◯-pullback {X} {Y} {Z} {f} {g} =
  ◯-pullback-lex isLex◯
  ∙ₑ Σ-cong-equiv-snd λ x◦ → Σ-cong-equiv-snd λ y◦ →
      compPathrEquiv (funExt⁻ (funExt⁻ map′≡map g) y◦)
    ∙ₑ compPathlEquiv (sym (funExt⁻ (funExt⁻ map′≡map f) x◦))


𝒱◦ : 𝒱₁
𝒱◦ = TypeWithStr _ isModal

𝒱◦-path : (X◦ X◦' : 𝒱◦) → ⟨ X◦ ⟩ ≡ ⟨ X◦' ⟩ → X◦ ≡ X◦'
𝒱◦-path X◦ X◦' = Σ≡Prop λ _ → isPropIsEquiv _

◯◦ : 𝒱 _ → 𝒱◦
◯◦ X = ◯ X , isModal◯
