module Calf.Value.Open where

open import Cubical.Foundations.Equiv.Properties
open import Cubical.Data.Unit.Properties
open import Cubical.Functions.FunExtEquiv
open import Cubical.Modalities.Modality

open import Calf.Core.Abstract
open import Calf.Value
open import Calf.Value.Product
open import Calf.Value.Sigma

◯ : 𝒱 → 𝒱
◯ X = (abs : ⟨ ABS ⟩) → X

η◦ : X → ◯ X
η◦ x _ = x

elim◯ : {Y : ◯ X → 𝒱}
  → ((x : X) → ◯ (Y (η◦ x))) → (x : ◯ X) → ◯ (Y x)
elim◯ {X} {Y} y x◦ abs =
  subst Y (funExt (cong x◦ ∘ str ABS abs)) (y (x◦ abs) abs)

isModal◯≡ : {x◦ x◦' : ◯ X} → isEquiv (η◦ {X = x◦ ≡ x◦'})
isModal◯≡ = equivIsEquiv (congEquiv lemma ∙ₑ invEquiv funExtEquiv)
  where
    lemma : ◯ X ≃ ◯ (◯ X)
    lemma = preCompEquiv (invEquiv (_ , isProp→isEquiv[diag] (str ABS))) ∙ₑ curryEquiv

rec◯ : (X → ◯ Y) → ◯ X → ◯ Y
rec◯ f x◦ abs = f (x◦ abs) abs

open import Cubical.Modalities.Extras
  elim◯
  (λ _ → funExt λ abs → transportRefl _)
  isModal◯≡
  rec◯
  (λ _ → refl)
  public

◯isModal : ⟨ ABS ⟩ → isModal X
◯isModal abs = isoToIsEquiv (invIso (isContr→Iso2 (inhProp→isContr abs (str ABS))))

isConnected≃◯isContr : isConnected X ≃ ◯ (isContr X)
isConnected≃◯isContr {X} =
    isConnected X
  ≃⟨ idEquiv _ ⟩
    (Σ[ x◦ ∈ ◯ X ] ((x◦' : ⟨ ABS ⟩ → X) → x◦ ≡ x◦'))
  ≃⟨ Σ-cong-equiv-snd (λ x◦ → ∘η-≃ λ _ → isModal◯≡) ⟩
    (Σ[ x◦ ∈ ◯ X ] ((x : X) → x◦ ≡ η◦ x))
  ≃⟨ Σ-cong-equiv-snd (λ _ → equivΠCod λ _ → invEquiv funExtEquiv) ⟩
    (Σ[ x◦ ∈ ◯ X ] ((x : X) (abs : ⟨ ABS ⟩) → x◦ abs ≡ x))
  ≃⟨ Σ-cong-equiv-snd (λ _ → isoToEquiv (iso flip flip (λ _ → refl) (λ _ → refl))) ⟩
    (Σ[ x◦ ∈ ◯ X ] ((abs : ⟨ ABS ⟩) (x : X) → x◦ abs ≡ x))
  ≃⟨ invEquiv Σ-Π-≃ ⟩
    ◯ (isContr X)
  ■

isLex◯ : IsLex
isLex◯ = funExtEquiv

open Lex isLex◯ public

isPreorder◯ : isPreorder X → isPreorder (◯ X)
isPreorder◯ = isLocal→

𝒱◦ : 𝒱₁
𝒱◦ = TypeWithStr _ isModal

𝒱◦-path : {X◦ X◦' : 𝒱◦} → ⟨ X◦ ⟩ ≡ ⟨ X◦' ⟩ → X◦ ≡ X◦'
𝒱◦-path = Σ≡Prop λ _ → isPropIsEquiv _

◯◦ : 𝒱 _ → 𝒱◦
◯◦ X = ◯ X , isModal◯
