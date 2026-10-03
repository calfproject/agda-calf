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
open import Cubical.Data.Bool
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.HITs.Localization

open import Calf.Core.Interval
open import Calf.Directed.Path

open import Cubical.HITs.Pushout public

private variable X Y : Type

𝕊 : Type → Type
𝕊 X = Pushout {A = X × Bool} (λ (x , b) → (x , (if b then 1𝟚 else 0𝟚))) snd

𝕊-map : (X → Y) → 𝕊 X → 𝕊 Y
𝕊-map f (inl (x , 𝕚)) = inl (f x , 𝕚)
𝕊-map f (inr b) = inr b
𝕊-map f (push (x , b) i) = push (f x , b) i

𝕊-cocone : Type → Type → Type
𝕊-cocone X Y = Σ[ x ∈ X ] Σ[ x' ∈ X ] (Y → x ⊑ x')

𝕊-elim≃ : (Y : Type) → (𝕊 Y → X) ≃ 𝕊-cocone X Y
𝕊-elim≃ {X} Y = isoToEquiv 𝕊-elim
  where
  𝕊-elim : Iso (𝕊 Y → X) (𝕊-cocone X Y)
  𝕊-elim .Iso.fun k =
    k (inr false) , k (inr true) , λ y →
        (λ 𝕚 → k (inl (y , 𝕚)))
      , cong k (push (y , false))
      , cong k (push (y , true))
  𝕊-elim .Iso.inv (_ , _ , q) (inl (y , 𝕚)) = path (q y) 𝕚
  𝕊-elim .Iso.inv (x , x' , q) (inr false) = x
  𝕊-elim .Iso.inv (x , x' , q) (inr true) = x'
  𝕊-elim .Iso.inv (_ , _ , q) (push (y , false) j) = path₀ (q y) j
  𝕊-elim .Iso.inv (_ , _ , q) (push (y , true) j) = path₁ (q y) j
  𝕊-elim .Iso.rightInv (_ , _ , q) = refl
  𝕊-elim .Iso.leftInv k i (inl (y , 𝕚)) = k (inl (y , 𝕚))
  𝕊-elim .Iso.leftInv k i (inr false) = k (inr false)
  𝕊-elim .Iso.leftInv k i (inr true) = k (inr true)
  𝕊-elim .Iso.leftInv k i (push (y , false) j) = k (push (y , false) j)
  𝕊-elim .Iso.leftInv k i (push (y , true) j) = k (push (y , true) j)

isBoundarySeparated : Type → Type
isBoundarySeparated = isLocal {A = Unit} (const (𝕊-map (terminal Bool)))

isThin : Type → Type
isThin X = (x x' : X) → isProp (x ⊑ x')

isThin→𝟚-injective : isThin X → {P Q : 𝟚 → X} → P 0𝟚 ≡ Q 0𝟚 → P 1𝟚 ≡ Q 1𝟚 → P ≡ Q
isThin→𝟚-injective isThinX {P} {Q} p q = cong path (isThinX _ _ (P , refl , refl) (Q , sym p , sym q))

isBoundarySeparated≡isThin : isBoundarySeparated X ≡ isThin X
isBoundarySeparated≡isThin {X} =
  hPropExt 
    (isPropΠ λ _ → isPropIsPathSplitEquiv _) 
    (isPropΠ2 λ _ _ → isPropIsProp)
    separated→thin 
    thin→separated
  where
  separated→thin : isBoundarySeparated X → isThin X
  separated→thin separated x y p q =
    p           ≡⟨ sym (common-path≡pair false) ⟩
    common-path ≡⟨ common-path≡pair true ⟩
    q ∎
    where
    cocones≃ : 𝕊-cocone X Unit ≃ 𝕊-cocone X Bool
    cocones≃ =
        𝕊-cocone X Unit
      ≃⟨ invEquiv (𝕊-elim≃ Unit) ⟩
        (𝕊 Unit → X)
      ≃⟨ _ , toIsEquiv _ (separated tt) ⟩
        (𝕊 Bool → X)
      ≃⟨ 𝕊-elim≃ Bool ⟩
        𝕊-cocone X Bool
      ■

    paths≃ : (Unit → x ⊑ y) ≃ (Bool → x ⊑ y)
    paths≃ = _ , fiberEquiv _ _ _
      (fiberEquiv _ _ _ (equivIsEquiv cocones≃) x) y

    pair : Bool → x ⊑ y
    pair false = p
    pair true = q

    common-path : x ⊑ y
    common-path = invEq paths≃ pair tt

    common-path≡pair : (b : Bool) → common-path ≡ pair b
    common-path≡pair = funExt⁻ (secEq paths≃ pair)

  thin→separated : isThin X → isBoundarySeparated X
  thin→separated thin _ = fromIsEquiv _ $
    isEquiv[equivFunA≃B∘f]→isEquiv[f] _ (𝕊-elim≃ Bool) $ equivIsEquiv $
        (𝕊 Unit → X)
      ≃⟨ 𝕊-elim≃ Unit ⟩
        𝕊-cocone X Unit
      ≃⟨ Σ-cong-equiv-snd (λ x → Σ-cong-equiv-snd (λ y →
           propBiimpl→Equiv (isPropΠ λ _ → thin x y) (isPropΠ λ _ → thin x y)
             (λ f _ → f tt) (λ f _ → f true))) ⟩
        𝕊-cocone X Bool
      ■
