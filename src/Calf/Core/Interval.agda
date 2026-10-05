module Calf.Core.Interval where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (isProp×; isPropΠ3)
open import Cubical.Data.Sigma using (_×_; Σ≡Prop)
open import Cubical.Data.Unit
open import Cubical.Functions.Logic
open import Relation.Binary.Definitions
  using (Antisymmetric; Maximum; Minimum; Reflexive; Transitive)

infixr 7 _∧𝟚_
infixr 6 _∨𝟚_

opaque
  𝟚 : Type
  𝟚 = Unit

  isSet𝟚 : isSet 𝟚
  isSet𝟚 = isSetUnit

  _≤𝟚_ : 𝟚 → 𝟚 → Type
  tt ≤𝟚 tt = Unit

  ≤𝟚-isProp : ∀ {i j} → isProp (i ≤𝟚 j)
  ≤𝟚-isProp = isContr→isProp isContrUnit

  ≤𝟚-refl : Reflexive _≤𝟚_
  ≤𝟚-refl = tt

  ≤𝟚-trans : Transitive _≤𝟚_
  ≤𝟚-trans _ _ = tt

  ≤𝟚-antisym : Antisymmetric _≡_ _≤𝟚_
  ≤𝟚-antisym = isContr→isProp isContrUnit

  ≤𝟚-total : (i j : 𝟚) → (i ≤𝟚 j) ⊔′ (j ≤𝟚 i)
  ≤𝟚-total _ _ = inl tt

  0𝟚 1𝟚 : 𝟚
  0𝟚 = tt
  1𝟚 = tt

  0𝟚-minimum : Minimum _≤𝟚_ 0𝟚
  0𝟚-minimum _ = tt

  1𝟚-maximum : Maximum _≤𝟚_ 1𝟚
  1𝟚-maximum tt = tt

private
  Meet : 𝟚 → 𝟚 → Type
  Meet i j = Σ[ m ∈ 𝟚 ] ((m ≤𝟚 i) × (m ≤𝟚 j)
    × ((k : 𝟚) → k ≤𝟚 i → k ≤𝟚 j → k ≤𝟚 m))

  isPropMeet : (i j : 𝟚) → isProp (Meet i j)
  isPropMeet i j (m , ml , mr , mg) (n , nl , nr , ng) =
    Σ≡Prop (λ _ → isProp× ≤𝟚-isProp
      (isProp× ≤𝟚-isProp (isPropΠ3 λ _ _ _ → ≤𝟚-isProp)))
      (≤𝟚-antisym (ng m ml mr) (mg n nl nr))

  meet : (i j : 𝟚) → Meet i j
  meet i j =
    ⊔-elim (i ≤𝟚 j , ≤𝟚-isProp) (j ≤𝟚 i , ≤𝟚-isProp) (λ _ → Meet i j , isPropMeet i j)
      (λ p → i , ≤𝟚-refl , p , (λ k ki kj → ki))
      (λ p → j , p , ≤𝟚-refl , (λ k ki kj → kj))
      (≤𝟚-total i j)

  Join : 𝟚 → 𝟚 → Type
  Join i j = Σ[ m ∈ 𝟚 ] ((i ≤𝟚 m) × (j ≤𝟚 m)
    × ((k : 𝟚) → i ≤𝟚 k → j ≤𝟚 k → m ≤𝟚 k))

  isPropJoin : (i j : 𝟚) → isProp (Join i j)
  isPropJoin i j (m , ml , mr , mlst) (n , nl , nr , nlst) =
    Σ≡Prop (λ _ → isProp× ≤𝟚-isProp
      (isProp× ≤𝟚-isProp (isPropΠ3 λ _ _ _ → ≤𝟚-isProp)))
      (≤𝟚-antisym (mlst n nl nr) (nlst m ml mr))

  join : (i j : 𝟚) → Join i j
  join i j =
    ⊔-elim (i ≤𝟚 j , ≤𝟚-isProp) (j ≤𝟚 i , ≤𝟚-isProp) (λ _ → Join i j , isPropJoin i j)
      (λ p → j , p , ≤𝟚-refl , (λ k ik jk → jk))
      (λ p → i , ≤𝟚-refl , p , (λ k ik jk → ik))
      (≤𝟚-total i j)

_∧𝟚_ : 𝟚 → 𝟚 → 𝟚
i ∧𝟚 j = meet i j .fst

∧𝟚-left : (i j : 𝟚) → (i ∧𝟚 j) ≤𝟚 i
∧𝟚-left i j = meet i j .snd .fst

∧𝟚-right : (i j : 𝟚) → (i ∧𝟚 j) ≤𝟚 j
∧𝟚-right i j = meet i j .snd .snd .fst

∧𝟚-greatest : {i j k : 𝟚} → k ≤𝟚 i → k ≤𝟚 j → k ≤𝟚 (i ∧𝟚 j)
∧𝟚-greatest {i} {j} {k} = meet i j .snd .snd .snd k

_∨𝟚_ : 𝟚 → 𝟚 → 𝟚
i ∨𝟚 j = join i j .fst

∨𝟚-left : (i j : 𝟚) → i ≤𝟚 (i ∨𝟚 j)
∨𝟚-left i j = join i j .snd .fst

∨𝟚-right : (i j : 𝟚) → j ≤𝟚 (i ∨𝟚 j)
∨𝟚-right i j = join i j .snd .snd .fst

∨𝟚-least : {i j k : 𝟚} → i ≤𝟚 k → j ≤𝟚 k → (i ∨𝟚 j) ≤𝟚 k
∨𝟚-least {i} {j} {k} = join i j .snd .snd .snd k

∧𝟚-mono : {i i' j j' : 𝟚} → i ≤𝟚 i' → j ≤𝟚 j' → (i ∧𝟚 j) ≤𝟚 (i' ∧𝟚 j')
∧𝟚-mono {i} {j = j} p q =
  ∧𝟚-greatest (≤𝟚-trans (∧𝟚-left i j) p) (≤𝟚-trans (∧𝟚-right i j) q)

∧𝟚-zero : (i : 𝟚) → (i ∧𝟚 0𝟚) ≡ 0𝟚
∧𝟚-zero i = ≤𝟚-antisym (∧𝟚-right i 0𝟚) (0𝟚-minimum _)

∧𝟚-one : (i : 𝟚) → (i ∧𝟚 1𝟚) ≡ i
∧𝟚-one i = ≤𝟚-antisym (∧𝟚-left i 1𝟚) (∧𝟚-greatest ≤𝟚-refl (1𝟚-maximum i))

∨𝟚-mono : {i i' j j' : 𝟚} → i ≤𝟚 i' → j ≤𝟚 j' → (i ∨𝟚 j) ≤𝟚 (i' ∨𝟚 j')
∨𝟚-mono {i' = i'} {j' = j'} p q =
  ∨𝟚-least (≤𝟚-trans p (∨𝟚-left i' j')) (≤𝟚-trans q (∨𝟚-right i' j'))

∨𝟚-zero : (i : 𝟚) → (i ∨𝟚 0𝟚) ≡ i
∨𝟚-zero i = ≤𝟚-antisym (∨𝟚-least ≤𝟚-refl (0𝟚-minimum i)) (∨𝟚-left i 0𝟚)

∨𝟚-one : (i : 𝟚) → (i ∨𝟚 1𝟚) ≡ 1𝟚
∨𝟚-one i = ≤𝟚-antisym (1𝟚-maximum _) (∨𝟚-right i 1𝟚)

∧𝟚-of-≤ : {i j : 𝟚} → i ≤𝟚 j → (i ∧𝟚 j) ≡ i
∧𝟚-of-≤ {i} {j} p = ≤𝟚-antisym (∧𝟚-left i j) (∧𝟚-greatest ≤𝟚-refl p)

∧𝟚-of-≥ : {i j : 𝟚} → j ≤𝟚 i → (i ∧𝟚 j) ≡ j
∧𝟚-of-≥ {i} {j} p = ≤𝟚-antisym (∧𝟚-right i j) (∧𝟚-greatest p ≤𝟚-refl)

∨𝟚-of-≤ : {i j : 𝟚} → i ≤𝟚 j → (i ∨𝟚 j) ≡ j
∨𝟚-of-≤ {i} {j} p = ≤𝟚-antisym (∨𝟚-least p ≤𝟚-refl) (∨𝟚-right i j)

∨𝟚-of-≥ : {i j : 𝟚} → j ≤𝟚 i → (i ∨𝟚 j) ≡ i
∨𝟚-of-≥ {i} {j} p = ≤𝟚-antisym (∨𝟚-least ≤𝟚-refl p) (∨𝟚-left i j)
