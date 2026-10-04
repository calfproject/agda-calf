module Calf.Value.Open where

open import Cubical.Foundations.Univalence
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Unit.Properties
open import Cubical.Modalities.Modality

open import Calf.Core.Abstract
open import Calf.Value
open import Calf.Value.Product
open import Calf.Value.Sigma

◯ : 𝒱 → 𝒱
◯ X = (abs : ⟨ ABS ⟩) → X

◯Π : (⟨ ABS ⟩ → 𝒱) → 𝒱
◯Π X = (abs : ⟨ ABS ⟩) → X abs

η◦ : X → ◯ X
η◦ x _ = x

isModal : 𝒱 → 𝒱
isModal X = isEquiv (η◦ {X})

◯isModal : ⟨ ABS ⟩ → isModal X
◯isModal abs = isoToIsEquiv (invIso (isContr→Iso2 (inhProp→isContr abs (str ABS))))

isModal◯Π : {X : ⟨ ABS ⟩ → 𝒱} → isModal (◯Π X)
isModal◯Π {X} =
  equivIsEquiv $
    ◯Π X
  ≃⟨ equivΠCod (λ abs → η◦ , ◯isModal abs) ⟩
    ◯Π (◯ ∘ X)
  ≃⟨ isoToEquiv (iso flip flip (λ _ → refl) (λ _ → refl)) ⟩
    ◯ (◯Π X)
  ■

isModal◯ : isModal (◯ X)
isModal◯ = isModal◯Π

rec : isModal Y → (X → Y) → ◯ X → Y
rec isModalY f x◦ = invIsEq isModalY λ abs → f (x◦ abs)

rec-β : (isModalY : isModal Y) (f : X → Y) (x : X) → rec isModalY f (η◦ x) ≡ f x
rec-β isModalY f x = retIsEq isModalY (f x)

◯Modality : Modality _
◯Modality = record
  { ◯ = ◯
  ; isModal = isModal
  ; isPropIsModal = isPropIsEquiv η◦
  ; ◯-isModal = isModal◯
  ; η = η◦
  ; ◯-elim =
      λ {X} {Y} isModalY f x◦ →
      invIsEq (isModalY x◦) λ abs →
      subst Y (funExt λ abs' → cong x◦ (str ABS abs abs')) (f (x◦ abs))
  ; ◯-elim-β = λ {X} {Y} isModalY f x →
      retIsEq (isModalY (η◦ x)) (transport refl (f x)) ∙ transportRefl (f x)
  ; ◯-=-isModal = λ x◦ x◦' →
      subst isModal (ua funExtEquiv) isModal◯Π
  }

open import Cubical.Modalities.Extras ◯Modality rec rec-β public
  hiding (isModal◯)

isConnected≃◯isContr : isConnected X ≃ ◯ (isContr X)
isConnected≃◯isContr {X} =
    isConnected X
  ≃⟨ idEquiv _ ⟩
    (Σ[ x◦ ∈ ◯ X ] ((x◦' : ⟨ ABS ⟩ → X) → x◦ ≡ x◦'))
  ≃⟨ Σ-cong-equiv-snd (λ x◦ → precomp-η-≃Π (◯-≡-isModal x◦)) ⟩
    (Σ[ x◦ ∈ ◯ X ] ((x : X) → x◦ ≡ η◦ x))
  ≃⟨ Σ-cong-equiv-snd (λ _ → equivΠCod λ _ → invEquiv funExtEquiv) ⟩
    (Σ[ x◦ ∈ ◯ X ] ((x : X) (abs : ⟨ ABS ⟩) → x◦ abs ≡ x))
  ≃⟨ Σ-cong-equiv-snd (λ _ → isoToEquiv (iso flip flip (λ _ → refl) (λ _ → refl))) ⟩
    (Σ[ x◦ ∈ ◯ X ] ((abs : ⟨ ABS ⟩) (x : X) → x◦ abs ≡ x))
  ≃⟨ invEquiv Σ-Π-≃ ⟩
    ◯ (isContr X)
  ■

isLex◯ : IsLex◯
isLex◯ = reflection-isEquiv η-≡-isModal (isConnectedMap-∘ₑ funExtEquiv isConnectedMapη)

open Lex isLex◯

isPreorder◯ : isPreorder X → isPreorder (◯ X)
isPreorder◯ = isLocal→

𝒱◦ : 𝒱₁
𝒱◦ = TypeWithStr _ isModal

𝒱◦-path : {X◦ X◦' : 𝒱◦} → ⟨ X◦ ⟩ ≡ ⟨ X◦' ⟩ → X◦ ≡ X◦'
𝒱◦-path = Σ≡Prop λ _ → isPropIsEquiv _

◯◦ : 𝒱 _ → 𝒱◦
◯◦ X = ◯ X , isModal◯
