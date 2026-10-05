module Calf.Directed.Thin where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Fiberwise using (fiberEquiv)
open import Cubical.Foundations.Equiv.PathSplit
open import Cubical.Foundations.Equiv.Properties
  using (isEquiv[equivFunA≃B∘f]→isEquiv[f])
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Data.Bool hiding (elim)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.HITs.Localization

open import Calf.Core.Interval
open import Calf.Directed.Path

open import Cubical.HITs.Pushout public

private variable X Y : Type

𝕊 : Type → Type
𝕊 X = Pushout {A = X × Bool} (λ (x , b) → (x , (if b then 1𝟚 else 0𝟚))) snd

map : (X → Y) → 𝕊 X → 𝕊 Y
map f (inl (x , 𝕚)) = inl (f x , 𝕚)
map f (inr b) = inr b
map f (push (x , b) i) = push (f x , b) i

cocone : Type → Type → Type
cocone X Y = Σ[ (x , x') ∈ X × X ] (Y → x ⊑ x')

elim≃ : (Y : Type) → (𝕊 Y → X) ≃ cocone X Y
elim≃ {X} Y = isoToEquiv elim
  where
  elim : Iso (𝕊 Y → X) (cocone X Y)
  elim .Iso.fun k =
    (k (inr false) , k (inr true)) , λ y →
        (λ 𝕚 → k (inl (y , 𝕚)))
      , cong k (push (y , false))
      , cong k (push (y , true))
  elim .Iso.inv (_ , q) (inl (y , 𝕚)) = path (q y) 𝕚
  elim .Iso.inv ((x , _) , _) (inr false) = x
  elim .Iso.inv ((_ , x') , _) (inr true) = x'
  elim .Iso.inv (_ , q) (push (y , false) j) = path₀ (q y) j
  elim .Iso.inv (_ , q) (push (y , true) j) = path₁ (q y) j
  elim .Iso.rightInv (_ , q) = refl
  elim .Iso.leftInv k i (inl (y , 𝕚)) = k (inl (y , 𝕚))
  elim .Iso.leftInv k i (inr false) = k (inr false)
  elim .Iso.leftInv k i (inr true) = k (inr true)
  elim .Iso.leftInv k i (push (y , false) j) = k (push (y , false) j)
  elim .Iso.leftInv k i (push (y , true) j) = k (push (y , true) j)

isBoundarySeparated : Type → Type
isBoundarySeparated = isLocal {A = Unit} (const (map (terminal Bool)))

isThin : Type → Type
isThin X = (x x' : X) → isProp (x ⊑ x')

isThin→𝟚-injective : isThin X → {P Q : 𝟚 → X} → P 0𝟚 ≡ Q 0𝟚 → P 1𝟚 ≡ Q 1𝟚 → P ≡ Q
isThin→𝟚-injective isThinX {P} {Q} p q =
  cong path (isThinX _ _ (P , refl , refl) (Q , sym p , sym q))

isBoundarySeparated≃isThin : isBoundarySeparated X ≃ isThin X
isBoundarySeparated≃isThin {X} =
  propBiimpl→Equiv
    (isPropΠ λ _ → isPropIsPathSplitEquiv _)
    (isPropΠ2 λ _ _ → isPropIsProp)
    separated→thin
    thin→separated
  where
  separated→thin : isBoundarySeparated X → isThin X
  separated→thin separated x x' p q =
    p           ≡⟨ sym (common-path≡pair false) ⟩
    common-path ≡⟨ common-path≡pair true ⟩
    q ∎
    where
    cocones≃ : cocone X Unit ≃ cocone X Bool
    cocones≃ =
        cocone X Unit
      ≃⟨ invEquiv (elim≃ Unit) ⟩
        (𝕊 Unit → X)
      ≃⟨ _ , toIsEquiv _ (separated tt) ⟩
        (𝕊 Bool → X)
      ≃⟨ elim≃ Bool ⟩
        cocone X Bool
      ■

    paths≃ : (Unit → x ⊑ x') ≃ (Bool → x ⊑ x')
    paths≃ = _ , fiberEquiv _ _ _ (equivIsEquiv cocones≃) (x , x')

    pair : Bool → x ⊑ x'
    pair false = p
    pair true = q

    common-path : x ⊑ x'
    common-path = invEq paths≃ pair tt

    common-path≡pair : (b : Bool) → common-path ≡ pair b
    common-path≡pair = funExt⁻ (secEq paths≃ pair)

  thin→separated : isThin X → isBoundarySeparated X
  thin→separated thin _ = fromIsEquiv _ $
    isEquiv[equivFunA≃B∘f]→isEquiv[f] _ (elim≃ Bool) $ equivIsEquiv $
        (𝕊 Unit → X)
      ≃⟨ elim≃ Unit ⟩
        cocone X Unit
      ≃⟨
        Σ-cong-equiv-snd (λ (x , x') →
          propBiimpl→Equiv
            (isProp→ (thin x x'))
            (isProp→ (thin x x'))
            (λ f _ → f _)
            (λ f _ → f true))
      ⟩
        cocone X Bool
      ■
