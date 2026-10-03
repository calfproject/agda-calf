module Calf.Directed.Transitive where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.PathSplit
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.HITs.Localization
open import Relation.Binary.Definitions using (Transitive)

open import Calf.Core.Interval
open import Calf.Directed.Path

open import Cubical.HITs.Pushout public

private variable X Y : Type

isTransitive : Type → Type
isTransitive X = Transitive (_⊑_ {X})

Λ² : Type
Λ² = Pushout {A = Unit} (const 1𝟚) (const 0𝟚)

Δ² : Type
Δ² = Σ[ i ∈ 𝟚 ] Σ[ j ∈ 𝟚 ] (j ≤𝟚 i)

Δ²-ext : {s t : Δ²} → s .fst ≡ t .fst → s .snd .fst ≡ t .snd .fst → s ≡ t
Δ²-ext p q = ΣPathP (p , ΣPathP (q , isProp→PathP (λ _ → ≤𝟚-isProp) _ _))

bottom₂ right₂ diagonal₂ : 𝟚 → Δ²
bottom₂ i = i , 0𝟚 , 0𝟚-minimum i
right₂ j = 1𝟚 , j , 1𝟚-maximum j
diagonal₂ i = i , i , ≤𝟚-refl

Δ²-elim : (t : Δ² → X) → t (bottom₂ 0𝟚) ⊑ t (right₂ 1𝟚)
Δ²-elim t =
    t ∘ diagonal₂
  , cong t (Δ²-ext refl refl)
  , cong t (Δ²-ext refl refl)

ι-horn : Λ² → Δ²
ι-horn (inl i) = bottom₂ i
ι-horn (inr j) = right₂ j
ι-horn (push tt k) = Δ²-ext {s = bottom₂ 1𝟚} {t = right₂ 0𝟚} refl refl k

Λ²-elim≃ : (Λ² → X) ≃ (Σ[ p ∈ (𝟚 → X) ] Σ[ q ∈ (𝟚 → X) ] (p 1𝟚 ≡ q 0𝟚))
Λ²-elim≃ {X} = isoToEquiv elimIso
  where
  elimIso : Iso (Λ² → X) (Σ[ p ∈ (𝟚 → X) ] Σ[ q ∈ (𝟚 → X) ] (p 1𝟚 ≡ q 0𝟚))
  elimIso .Iso.fun k = (k ∘ inl) , (k ∘ inr) , cong k (push tt)
  elimIso .Iso.inv (p , q , r) (inl 𝕚) = p 𝕚
  elimIso .Iso.inv (p , q , r) (inr 𝕚) = q 𝕚
  elimIso .Iso.inv (p , q , r) (push tt j) = r j
  elimIso .Iso.rightInv _ = refl
  elimIso .Iso.leftInv k i (inl 𝕚) = k (inl 𝕚)
  elimIso .Iso.leftInv k i (inr 𝕚) = k (inr 𝕚)
  elimIso .Iso.leftInv k i (push tt j) = k (push tt j)

isPathTransitive : Type → Type
isPathTransitive = isLocal {A = Unit} (const ι-horn)

isPathTransitive→isTransitive : isPathTransitive X → isTransitive X
isPathTransitive→isTransitive {X} pt {x} {y} {z} f g =
    path diagonal
  , (path diagonal 0𝟚      ≡⟨ path₀ diagonal ⟩
     triangle (bottom₂ 0𝟚) ≡⟨ funExt⁻ boundary (inl 0𝟚) ⟩
     path f 0𝟚             ≡⟨ path₀ f ⟩
     x                     ∎)
  , (path diagonal 1𝟚      ≡⟨ path₁ diagonal ⟩
     triangle (right₂ 1𝟚)  ≡⟨ funExt⁻ boundary (inr 1𝟚) ⟩
     path g 1𝟚             ≡⟨ path₁ g ⟩
     z                     ∎)
  where
  open isPathSplitEquiv

  horn : Λ² → X
  horn = invEq Λ²-elim≃ (path f , path g , path₁ f ∙ sym (path₀ g))

  triangle : Δ² → X
  triangle = equivFun (invEquiv (_ , toIsEquiv _ (pt tt))) horn

  boundary : triangle ∘ ι-horn ≡ horn
  boundary = secEq (_ , toIsEquiv _ (pt tt)) horn

  diagonal : triangle (bottom₂ 0𝟚) ⊑ triangle (right₂ 1𝟚)
  diagonal = Δ²-elim triangle
