module Calf.Directed.Transitive where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.PathSplit
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Data.Bool
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.HITs.Localization
open import Cubical.HITs.Pushout public
open import Relation.Binary.Definitions

open import Calf.Core.Interval
open import Calf.Directed.Path
open import Calf.Directed.Thin

private variable X Y : Type

Λ² : Type
Λ² = Pushout {A = Unit} (const 1𝟚) (const 0𝟚)

Δ² : Type
Δ² =
  Pushout {A = Bool} {B = Λ²} {C = 𝟚}
    (λ { false → inl 0𝟚 ; true → inr 1𝟚 })
    (λ { false → 0𝟚 ; true → 1𝟚 })

ι : Λ² → Δ²
ι = inl

open Iso

Δ²-elim : Iso (Δ² → X) (Σ[ h ∈ (Λ² → X) ] (h (inl 0𝟚) ⊑ h (inr 1𝟚)))
Δ²-elim .fun k =
  (k ∘ inl) , record
    { path = k ∘ inr
    ; path₀ = cong k (sym (push false))
    ; path₁ = cong k (sym (push true))
    }
Δ²-elim .inv (h , e) (inl b) = h b
Δ²-elim .inv (h , e) (inr 𝕚) = e .path 𝕚
Δ²-elim .inv (h , e) (push false i) = sym (e .path₀) i
Δ²-elim .inv (h , e) (push true i) = sym (e .path₁) i
Δ²-elim .rightInv (h , e) = refl
Δ²-elim .leftInv k i (inl b) = k (inl b)
Δ²-elim .leftInv k i (inr 𝕚) = k (inr 𝕚)
Δ²-elim .leftInv k i (push false j) = k (push false j)
Δ²-elim .leftInv k i (push true j) = k (push true j)

Λ²-elim : Iso (Λ² → X) (Σ[ p ∈ (𝟚 → X) ] Σ[ q ∈ (𝟚 → X) ] (p 1𝟚 ≡ q 0𝟚))
Λ²-elim .fun k = (k ∘ inl) , (k ∘ inr) , cong k (push tt)
Λ²-elim .inv (p , q , r) (inl 𝕚) = p 𝕚
Λ²-elim .inv (p , q , r) (inr 𝕚) = q 𝕚
Λ²-elim .inv (p , q , r) (push tt j) = r j
Λ²-elim .rightInv _ = refl
Λ²-elim .leftInv k i (inl 𝕚) = k (inl 𝕚)
Λ²-elim .leftInv k i (inr 𝕚) = k (inr 𝕚)
Λ²-elim .leftInv k i (push tt j) = k (push tt j)

isPathTransitive : Type → Type
isPathTransitive = isLocal {A = Unit} (const ι)

isPathTransitive→Transitive[⊑] : isPathTransitive X → Transitive _⊑_
isPathTransitive→Transitive[⊑] {X} isPathTransitiveX {x} {x'} {x''} x⊑x' x'⊑x'' =
  record
    { path = triangle ∘ inr
    ; path₀ = cong triangle (sym (push false)) ∙ cong (_$ inl 0𝟚) secι ∙ x⊑x' .path₀
    ; path₁ = cong triangle (sym (push true)) ∙ cong (_$ inr 1𝟚) secι ∙ x'⊑x'' .path₁
    }
  where
    open isPathSplitEquiv

    horn : Λ² → X
    horn (inl 𝕚) = x⊑x' .path 𝕚
    horn (inr 𝕚) = x'⊑x'' .path 𝕚
    horn (push tt i) = (x⊑x' .path₁ ∙ sym (x'⊑x'' .path₀)) i

    triangle : Δ² → X
    triangle = isPathTransitiveX tt .sec .fst horn

    secι : triangle ∘ ι ≡ horn
    secι = isPathTransitiveX tt .sec .snd horn

isThin∧Transitive[⊑]→isPathTransitive :
  isThin X → Transitive _⊑_ → isPathTransitive X
isThin∧Transitive[⊑]→isPathTransitive {X} ⊑prop ⊑trans _ =
  fromIsEquiv _
    (subst isEquiv (funExt (λ _ → refl))
      (compEquiv (isoToEquiv Δ²-elim) (Σ-contractSnd edge) .snd))
  where
    composite : (h : Λ² → X) → h (inl 0𝟚) ⊑ h (inr 1𝟚)
    composite h =
      ⊑trans (record { path = h ∘ inl ; path₀ = refl ; path₁ = refl })
        (⊑trans (≡⇒⊑ (cong h (push tt)))
          (record { path = h ∘ inr ; path₀ = refl ; path₁ = refl }))

    edge : (h : Λ² → X) → isContr (h (inl 0𝟚) ⊑ h (inr 1𝟚))
    edge h = composite h , ⊑prop _ _ (composite h)

isThin→isPathTransitive≡Transitive[⊑] :
  isThin X → isPathTransitive X ≡ Transitive _⊑_
isThin→isPathTransitive≡Transitive[⊑] {X} isThinX =
  hPropExt
    (isPropΠ λ _ → isPropIsPathSplitEquiv _)
    isPropTransitive
    isPathTransitive→Transitive[⊑]
    (isThin∧Transitive[⊑]→isPathTransitive isThinX)
  where
    isPropTransitive : isProp (Transitive _⊑_)
    isPropTransitive t t' i a b = isThinX _ _ (t a b) (t' a b) i
