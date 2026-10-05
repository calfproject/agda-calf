module Calf.Value.Closed where

open import Cubical.Foundations.Equiv.Fiberwise using (fiberEquiv)
open import Cubical.Foundations.Equiv.Properties using (isEquivFromIsContr)
open import Cubical.Foundations.Path using (compPath→Square)
open import Cubical.Modalities.Modality

open import Calf.Core.Abstract
open import Calf.Value
open import Calf.Value.Open as ◯ using (◯)
open import Calf.Value.Product
open import Calf.Value.Sigma
open import Calf.Value.Unit

data ● (X : 𝒱) : 𝒱 where
  η• : (x : X) → ● X
  ∗ : (abs : ⟨ ABS ⟩) → ● X
  push : (x : X) (abs : ⟨ ABS ⟩) → η• x ≡ ∗ abs

ind : (Y : ● X → 𝒱)
  → (η•-case : (x : X) → Y (η• x))
  → (∗-case : (abs : ⟨ ABS ⟩) → Y (∗ abs))
  → (push-case :
      (x : X) (abs : ⟨ ABS ⟩)
      → PathP (λ i → Y (push x abs i)) (η•-case x) (∗-case abs))
  → (x• : ● X) → Y x•
ind Y η•-case ∗-case push-case (η• x) = η•-case x
ind Y η•-case ∗-case push-case (∗ abs) = ∗-case abs
ind Y η•-case ∗-case push-case (push x abs i) = push-case x abs i

∗-open : (abs : ⟨ ABS ⟩) → (x• : ● X) → x• ≡ ∗ abs
∗-open abs =
  ind (_≡ ∗ abs)
    (λ x → push x abs)
    (λ abs' → cong ∗ (str ABS abs' abs))
    (λ x abs' →
      J (λ a p → Square (push x a) (cong ∗ p) (push x abs') refl)
        (compPath→Square refl)
        (str ABS abs' abs))

◯-isConnected : ◯ (isContr (● X))
◯-isConnected abs = ∗ abs , sym ∘ ∗-open abs

◯-isProp● : ◯ (isProp (● X))
◯-isProp● = isContr→isProp ∘ ◯-isConnected

elim● : {Y : ● X → 𝒱}
  → ((x : X) → ● (Y (η• x))) → (x : ● X) → ● (Y x)
elim● {X} {Y} y =
  ind (● ∘ Y)
    y
    (λ abs → ∗ abs)
    (λ _ abs → isProp→PathP (λ _ → ◯-isProp● abs) _ _)

isModal●≡ : {x• x•' : ● X} → isEquiv (η• {X = x• ≡ x•'})
isModal●≡ =
  isoToIsEquiv
    (iso _
      (ind _ id (λ abs → ◯-isProp● abs _ _) λ _ abs →
        isProp→isSet (◯-isProp● abs) _ _ _ _)
      (ind _ (λ _ → refl) (λ abs → ◯-isProp● abs _ _) λ _ abs →
        isSet→isSet' (isProp→isSet (◯-isProp● abs)) _ _ _ _)
      (λ _ → refl))

open import Cubical.Modalities.Extras
  elim●
  (λ _ → refl)
  isModal●≡
  elim●
  (λ _ → refl)
  public
  renaming
    ( isModal◯ to isModal●
    ; ◯-≃ to ●-≃
    ; ◯-ua-gluePath to ●-ua-gluePath
    )

-- Based identity-system argument (https://1lab.dev/1Lab.Path.IdentitySystem.html#based-identity-systems)
-- This lex proof is adapted from: https://github.com/ncfavier/agda-stuff/blob/main/src-1lab/ErasureOpen.lagda.md
isLex● : IsLex
isLex● {X} {x} {x'} =
  _ ,
  fiberEquiv code (η• x ≡_) decode
    (isEquivFromIsContr _ code-contr (isContrSingl (η• x)))
    (η• x')
  where
    code : ● X → 𝒱
    code (η• x') = ● (x ≡ x')
    code (∗ abs) = 1ᵛ
    code (push x' abs i) = isContr→≡1ᵛ (◯-isConnected {X = x ≡ x'} abs) i

    decode : (x•' : ● X) → code x•' → η• x ≡ x•'
    decode =
      elim (λ _ → isModalΠ λ _ → isModal●≡) λ x' →
      elim (λ _ → isModal●≡) (cong η•)

    decode-over : ∀ x•' c → PathP (λ i → code (decode x•' c i)) (η• refl) c
    decode-over =
      elim (λ _ → isModalΠ λ _ → isModalPathP isModal●) λ y →
      elim (λ _ → isModalPathP isModal●) λ _ → congP (λ _ → η•) (compPath→Square refl)

    code-contr : isContr (Σ (● X) code)
    code-contr .fst = η• x , η• refl
    code-contr .snd (x•' , c) i = decode x•' c i , decode-over x•' c i

open Lex isLex● public
  renaming
    ( isSet◯ to isSet●
    ; ◯-pullback to ●-pullback
    ; ◯-pullback-β to ●-pullback-β
    ; ◯-pullback-β₁ to ●-pullback-β₁
    ; ◯-pullback-β₂ to ●-pullback-β₂
    )

isModal●→isConnected◯ : isModal X → ◯.isConnected X
isModal●→isConnected◯ X-modal =
  isContrΠ λ abs → isOfHLevelRespectEquiv 0 (invEquiv (η• , X-modal)) (◯-isConnected abs)

isConnected◯→isModal● : ◯.isConnected X → isModal X
isConnected◯→isModal● isConnectedX =
  isRetract◯→isModal
    (ind _
      id
      (λ abs → equivFun ◯.isConnected≃◯isContr isConnectedX abs .fst)
      (λ _ abs → sym (equivFun ◯.isConnected≃◯isContr isConnectedX abs .snd _)))
    (λ _ → refl)

opaque
  unfolding 𝟚

  isPreorder● : isPreorder X → isPreorder (● X)
  isPreorder● isPreorderX =
    isSet∧isDiscrete→isPreorder
      (isSet● (isPreorder→isSet isPreorderX))
      (BEH⇒isDiscrete refl)

isModal⊑ : isModal X → {x x' : X} → isModal (x ⊑ x')
isModal⊑ isModalX =
  isModalΣ (isModal→ isModalX) λ _ →
  isModal× (isModal≡ isModalX) (isModal≡ isModalX)

𝒱• : 𝒱₁
𝒱• = TypeWithStr _ isModal

𝒱•-path : {X• X•' : 𝒱•} → ⟨ X• ⟩ ≡ ⟨ X•' ⟩ → X• ≡ X•'
𝒱•-path = Σ≡Prop λ _ → isPropIsEquiv _

●• : 𝒱 → 𝒱•
●• X = ● X , isModal●
