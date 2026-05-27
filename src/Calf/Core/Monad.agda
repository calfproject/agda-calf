open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Calf.Core.Monad (ABS : hProp ℓ-zero) where

φ = ABS .fst
φ-isProp = ABS .snd

open import Calf.Core.Directed
open import Calf.Value
open import Calf.Core.Cost public
open import Calf.Value.Open φ φ-isProp as ◯ᵛ
open import Calf.Value.Closed φ φ-isProp as ●ᵛ
open import Calf.Value.Product
open import Calf.Value.Pi

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.Monad.Base

open Category
open Functor public
open NatTrans public
open IsMonad public

𝒱-Cat : Category _ _
𝒱-Cat .ob = 𝒱
𝒱-Cat .Hom[_,_] X Y = val X → val Y
𝒱-Cat .id x = x
𝒱-Cat ._⋆_ f g x = g (f x)
𝒱-Cat .⋆IdL _ = refl
𝒱-Cat .⋆IdR _ = refl
𝒱-Cat .⋆Assoc _ _ _ = refl
𝒱-Cat .isSetHom {X} {Y} = isSet→ (Y .is-set)

record Glue≤ (X• : 𝒱•) (X∘ : 𝒱∘) (χ : val (X• .fst) → val (●ᵛ (X∘ .fst))) : Type where
  field
    • : val (X• .fst)
    ∘ : val (X∘ .fst)
    •→∘ : χ • ⊑[ ●ᵛ (X∘ .fst) ] η• ∘
open Glue≤

Seal : Monad 𝒱-Cat
Seal .fst .F-ob X .val = Glue≤ (●ᵛ X , ●ᵛ-ηᵛ-isEquiv) (◯ᵛ X , ◯ᵛ-ηᵛ-isEquiv) (●ᵛ.map (η∘ᵛ {X}))
Seal .fst .F-ob X .is-set = {!   !}
Seal .fst .F-ob X .is-preorder = subst isPreorder {!   !} (RS-8∙11 (●ᵛ X .is-preorder) is-covariant)
  where
    is-covariant : IsCovariant (λ x• → Σ[ x∘ ∈ val (◯ᵛ X) ] ●ᵛ.map (η∘ᵛ {X}) x• ⊑[ ●ᵛ (◯ᵛ X) ] η• x∘)
    is-covariant = {!   !}
Seal .fst .F-hom f g≤ .• = ●ᵛ.map f (g≤ .•)
Seal .fst .F-hom f g≤ .∘ = ◯ᵛ.map f (g≤ .∘)
Seal .fst .F-hom f g≤ .•→∘ = {!   !}
Seal .fst .F-id = {!   !}
Seal .fst .F-seq = {!   !}
Seal .snd .η .N-ob X x .• = η•ᵛ {X} x
Seal .snd .η .N-ob X x .∘ = η∘ᵛ {X} x
Seal .snd .η .N-ob X x .•→∘ = ⊑ᵛ-refl {●ᵛ (◯ᵛ X)}
Seal .snd .η .N-hom = {!   !}
Seal .snd .μ .N-ob X g≤ .• = ●-join (●ᵛ.map • (g≤ .•))
Seal .snd .μ .N-ob X g≤ .∘ abs = g≤ .∘ abs .∘ abs
Seal .snd .μ .N-ob X g≤ .•→∘ = {!   !}
Seal .snd .μ .N-hom = {!   !}
Seal .snd .idl-μ = {!   !}
Seal .snd .idr-μ = {!   !}
Seal .snd .assoc-μ = {!   !}

CostT : Monad 𝒱-Cat → Monad 𝒱-Cat
CostT M .fst .F-ob X = M .fst .F-ob (ℂ ×ᵛ X)
CostT M .fst .F-hom f = M .fst .F-hom (λ (c , x) → c , f x)
CostT M .fst .F-id = M .fst .F-id
CostT M .fst .F-seq f g = M .fst .F-seq _ _
CostT M .snd .η .N-ob X x = M .snd .η .N-ob (ℂ ×ᵛ X) (0ℂ , x)
CostT M .snd .η .N-hom = {!   !}
CostT M .snd .μ .N-ob X m =
  M .snd .μ .N-ob (ℂ ×ᵛ X) $
  M .fst .F-hom (λ (c , m') →
  M .fst .F-hom (λ (c' , x) →
  c +ℂ c' , x) m') m
CostT M .snd .μ .N-hom = {!   !}
CostT M .snd .idl-μ = {!   !}
CostT M .snd .idr-μ = {!   !}
CostT M .snd .assoc-μ = {!   !}

opaque
  M : Monad 𝒱-Cat
  M = CostT Seal

  private variable m : val (M .fst .F-ob X)

  chargeᴹ : val ℂ → val (M .fst .F-ob X) → val (M .fst .F-ob X)
  chargeᴹ {X} c m = M .snd .μ .N-ob X (Seal .snd .η .N-ob _ (c , m))

  chargeᴹ/0 : chargeᴹ 0ℂ m ≡ m
  chargeᴹ/0 = {!   !}

  chargeᴹ/+ : chargeᴹ (c₁ +ℂ c₂) m ≡ chargeᴹ c₁ (chargeᴹ c₂ m)
  chargeᴹ/+ = {!   !}

  sealᴹ :
    (a : val (M .fst .F-ob X)) (a∘ : ⟨ ABS ⟩ → val (M .fst .F-ob X))
    → ((abs : ⟨ ABS ⟩) → a ⊑[ M .fst .F-ob X ] a∘ abs)
    → val (M .fst .F-ob X)
  sealᴹ {X} m m∘ m⊑m∘ =
    M .snd .μ .N-ob X $
      record
        { • = η•ᵛ {ℂ ×ᵛ M .fst .F-ob X} (0ℂ , m)
        ; ∘ = λ abs → (0ℂ , m∘ abs)
        ; •→∘ =
            ⊑ᵛ-mono {◯ᵛ (ℂ ×ᵛ M .fst .F-ob X)} {●ᵛ (◯ᵛ (ℂ ×ᵛ M .fst .F-ob X))}
              (η•ᵛ {◯ᵛ (ℂ ×ᵛ M .fst .F-ob X)})
              (⊑ᵛ-funext {fromProp φ-isProp} {λ _ → ℂ ×ᵛ M .fst .F-ob X}
                λ abs → ⊑ᵛ-mono {M .fst .F-ob X} {ℂ ×ᵛ M .fst .F-ob X}
                (0ℂ ,_) (m⊑m∘ abs))
        }
