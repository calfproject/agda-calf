module Calf.Value where

open import Cubical.Foundations.Prelude public
  renaming (Type to 𝒱)
open import Cubical.Foundations.Equiv public
open import Cubical.Foundations.Function public
  hiding (idfun)
open import Cubical.Foundations.HLevels public
open import Cubical.Foundations.Isomorphism public
open import Cubical.Foundations.Structure public

open import Calf.Core.Directed public

variable
  X Y Z : 𝒱

id : X → X
id x = x

_⨾_ : (X → Y) → (Y → Z) → X → Z
f ⨾ g = g ∘ f

infixr 30 _∙ᴾ_
_∙ᴾ_ :
  ∀ {X Y Z : I → 𝒱} {f₀ f₁ g₀ g₁}
  → PathP (λ i → X i → Y i) f₀ f₁
  → PathP (λ i → Y i → Z i) g₀ g₁
  → PathP (λ i → X i → Z i) (f₀ ⨾ g₀) (f₁ ⨾ g₁)
_∙ᴾ_ = congP₂ λ _ → _⨾_

isProp→isEquiv[diag] : isProp X → isEquiv (λ (x : X) → x , x)
isProp→isEquiv[diag] isPropX =
  isoToIsEquiv (iso _ snd (λ (x , x') → cong (_, x') (isPropX x' x)) (λ _ → refl))

𝒱₌ : 𝒱₁
𝒱₌ = TypeWithStr _ λ X → isSet X × isDiscrete X
  where open import Cubical.Data.Sigma

variable
  X₌ Y₌ Z₌ : 𝒱₌

𝒱ₚ : 𝒱₁
𝒱ₚ = TypeWithStr _ isPreorder

variable
  Xₚ Yₚ Zₚ : 𝒱ₚ

⟨_⟩ₚ : 𝒱₌ → 𝒱ₚ
⟨ X ⟩ₚ = ⟨ X ⟩ , isSet∧isDiscrete→isPreorder (str X .fst) (str X .snd)
