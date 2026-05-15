{-# OPTIONS --cubical #-}

-- The basic CBPV metalanguage.

open import Cubical.Foundations.Prelude
-- open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Data.List
-- open import Cubical.Foundations.HLevels
-- open import Cubical.Foundations.Isomorphism
-- open import Cubical.Foundations.Path
-- open import Cubical.Foundations.Univalence

module Calf.CBPV where

-- record 𝒞

open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Sigma

variable
  X : Type

opaque
  M : Type → Type
  M X = ℕ × X

  M-ret : X → M X
  M-ret x = (0 , x)

  -- M-charge : ℕ → M X → M X
  -- M-charge c (c' , x) = (c + c' , x)

record 𝒞 : Type₁ where
  field
    U : Type
    charge : ℕ → U → U
open 𝒞

variable
  A B C : 𝒞

record _⊸_ (A B : 𝒞) : Type where
  field
    U : U A → U B
    charge : (c : ℕ) (a : 𝒞.U A) → U (A .charge c a) ≡ B .charge c (U a)
open _⊸_

UnitA : 𝒞
UnitA .U = Unit

_⇀_ : Type → 𝒞 → 𝒞
(X ⇀ A) .U = X → A .U

opaque
  unfolding M

  F : Type → 𝒞
  F X .U = M X
  F X .charge c (c' , x) = c + c' , x

  ret : X → U (F X)
  ret = M-ret

fwd : (F X ⊸ A) → (X → U A)
fwd f x = f .U (ret x)

BIND : (X → U A) → (F X ⊸ A)
BIND g .U = {!   !}
BIND g .charge = {!   !}

postulate
  ABS : Type

data ● (X : Type) : Type where
  η∙ : X → ● X
  ∗ : ABS → ● X
  law : (x : X) (abs : ABS) → η∙ x ≡ ∗ abs
-- ● = {!   !}

●' : 𝒞 → 𝒞
●' A .U = ● (A .U)
●' A .charge c (η∙ x) = η∙ (A .charge c x)
●' A .charge c (∗ abs) = ∗ abs
●' A .charge c (law x abs i) = law (A .charge c x) abs i

-- opaque
--   unfolding M


--   Fℕ : 𝒞
--   Fℕ .U = Unit

-- opaque
--   unfolding _⇀_ Fℕ

bar : U (ℕ ⇀ F ℕ)
bar zero = ret {!   !}
bar (suc n) = {!   !}

-- opaque
--   unfolding UnitA

--   foo : UnitA .U
--   foo = tt

-- record CBPV : Type₁ where
--   𝒱 = Type

--   field
--     𝒞 : Type
--     _⊢_ : List 𝒞 → 𝒞 → 𝒱
--     id : ∀ {A} → [ A ] ⊢ A

--     _⊸_ : 𝒞 → 𝒞 → 𝒱

--     F : 𝒱 → 𝒞
--     U : 𝒞 → 𝒱

--     -- ⊤ : 𝒞
--     -- unit : ⊤ ⊸ ⊤
--     -- check : ∀ {Δ A} → (Δ ⊸ ⊤) → U A → (Δ ⊸ A)

--     susp : ∀ {A} → ([] ⊢ A) → U A
--     force : ∀ {Δ A} → U A → (Δ ⊸ A)
--     -- U/β : ∀ {A} {a : ⊤ ⊸ A} → force (susp a) ≡ a

--     ret : ∀ {Δ X} → X → (Δ ⊸ F X)
--     bind : ∀ {Δ X A} → (Δ ⊸ F X) → (X → U A) → (Δ ⊸ A)
--     bind/β : ∀ {Δ X A} {x} {k : X → U A} → bind (ret x) k ≡ force (k x)
--     -- bind/η : ∀ {X} {e : U (F X)} → bind e ret ≡ e

--     _⇀_ : 𝒱 → 𝒞 → 𝒞
--     ⇀/decode : ∀ {X A} → U (X ⇀ A) ≡ (X → U A)
--     ⇀/decode' : ∀ {Δ X A} → (Δ ⊸ (X ⇀ A)) ≡ (X → (Δ ⊸ A))

--     -- vec : ℕ → 𝒞 → 𝒞
--     _⋊_ : (X : 𝒱) (A : X → 𝒞) → 𝒞
--     pair : ∀ {Δ X A} → (x : X) → (Δ ⊸ A x) → (Δ ⊸ (X ⋊ A))
--     split : ∀ {Δ X A B} → (Δ ⊸ (X ⋊ A)) → ((x : X) → (A x ⊸ B)) → (Δ ⊸ B)


--   variable
--     X Y Z : 𝒱
--     A B C : 𝒞

-- -- Computation types

-- postulate
--   ret : val A → cmp (F A)
--   bind : (X : tp⁻) → cmp (F A) → (val A → cmp X) → cmp X

--   bind/β : {a : val A} {f : val A → cmp X} → bind X (ret {A} a) f ≡ f a
--   bind/η : {e : cmp (F A)} → bind (F A) e ret ≡ e
--   bind/assoc : {e : cmp (F A)} {f : val A → cmp (F B)} {g : val B → cmp X} →
--     bind X (bind (F B) e f) g ≡ bind X e (λ a → bind X (f a) g)
--   {-# REWRITE bind/β bind/η bind/assoc #-}

--   Π : (A : tp⁺) (X : val A → tp⁻) → tp⁻
--   Π/decode : {X : val A → tp⁻} → val (U (Π A X)) ≡ ((a : val A) → cmp (X a))
--   {-# REWRITE Π/decode #-}

--   prod⁻ : tp⁻ → tp⁻ → tp⁻
--   prod⁻/decode : val (U (prod⁻ X Y)) ≡ (cmp X × cmp Y)
--   {-# REWRITE prod⁻/decode #-}

--   unit⁻ : tp⁻
--   unit⁻/decode : val (U unit⁻) ≡ Unit
--   {-# REWRITE unit⁻/decode #-}

--   Σ⁻ : (A : tp⁺) (X : val A → tp⁻) → tp⁻
--   Σ⁻/decode : {X : val A → tp⁻} → val (U (Σ⁻ A X)) ≡ Σ (val A) λ a → cmp (X a)
--   {-# REWRITE Σ⁻/decode #-}

-- _⋉_ : tp⁺ → tp⁻ → tp⁻
-- A ⋉ X = Σ⁻ A λ _ → X
