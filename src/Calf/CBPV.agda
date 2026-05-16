{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
-- open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Data.List
open import Cubical.Data.Sum
open import Cubical.Data.Unit
open import Cubical.Data.Empty
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Properties
open import Cubical.Data.Sigma
-- open import Cubical.Foundations.HLevels
-- open import Cubical.Foundations.Isomorphism
-- open import Cubical.Foundations.Path
-- open import Cubical.Foundations.Univalence

open import Calf.Directed

module Calf.CBPV where

opaque
  ℂ : 𝒱
  ℂ = ω

  0ℂ : val ℂ
  0ℂ = 0

  _+ℂ_ : val ℂ → val ℂ → val ℂ
  _+ℂ_ = _+_

  +ℂ-identityˡ : ∀ c → 0ℂ +ℂ c ≡ c
  +ℂ-identityˡ = {!   !}

  +ℂ-assoc : ∀ c₁ c₂ c₃ → (c₁ +ℂ c₂) +ℂ c₃ ≡ c₁ +ℂ (c₂ +ℂ c₃)
  +ℂ-assoc = {!   !}

variable
  c c₁ c₂ : val ℂ

opaque
  M : 𝒱 → 𝒱
  M X = ℂ ×ᵛ X

  M-ret : val X → val (M X)
  M-ret x = (0ℂ , x)

record 𝒞 : Type₁ where
  field
    U : 𝒱
  cmp = val U

  field
    charge : val ℂ → cmp → cmp
    charge/0 : ∀ {a} → charge 0ℂ a ≡ a
    charge/+ : ∀ {a c₁ c₂} → charge (c₁ +ℂ c₂) a ≡ charge c₁ (charge c₂ a)
open 𝒞

variable
  A B C : 𝒞

record _⊸_ (A B : 𝒞) : Type where
  field
    U : cmp A → cmp B
    charge : (c : val ℂ) (a : cmp A) → U (A .charge c a) ≡ B .charge c (U a)
open _⊸_

id⊸ : A ⊸ A
id⊸ .U a = a
id⊸ .charge c a = refl

1ᶜ : 𝒞
1ᶜ .U = 1ᵛ
1ᶜ .charge c tt = tt
1ᶜ .charge/0 = refl
1ᶜ .charge/+ = refl

_×ᶜ_ : 𝒞 → 𝒞 → 𝒞
(A ×ᶜ B) .U = A .U ×ᵛ B .U
(A ×ᶜ B) .charge c e .fst = A .charge c (e .fst)
(A ×ᶜ B) .charge c e .snd = B .charge c (e .snd)
(A ×ᶜ B) .charge/0 {e} i .fst = A .charge/0 {e .fst} i
(A ×ᶜ B) .charge/0 {e} i .snd = B .charge/0 {e .snd} i
(A ×ᶜ B) .charge/+ {e} {c₁} {c₂} i .fst = A .charge/+ {e .fst} {c₁} {c₂} i
(A ×ᶜ B) .charge/+ {e} {c₁} {c₂} i .snd = B .charge/+ {e .snd} {c₁} {c₂} i

Πᶜ : (X : 𝒱) → (val X → 𝒞) → 𝒞
Πᶜ X A .U = Πᵛ X (U ∘ A)
Πᶜ X A .charge c e x = A x .charge c (e x)
Πᶜ X A .charge/0 {e} i x = A x .charge/0 {e x} i
Πᶜ X A .charge/+ {e} {c₁} {c₂} i x = A x .charge/+ {e x} {c₁} {c₂} i
syntax Πᶜ X (λ x → A) = [ x ∈ X ] ⇀ A

_⇀_ : 𝒱 → 𝒞 → 𝒞
X ⇀ A = Πᶜ X (const A)

0ᶜ : 𝒞
0ᶜ .U = ⊥ᵛ
0ᶜ .charge c ()

_+ᶜ_ : 𝒞 → 𝒞 → 𝒞
(A +ᶜ B) .U = A .U +ᵛ B .U
(A +ᶜ B) .charge c (inl a) = inl (A .charge c a)
(A +ᶜ B) .charge c (inr b) = inr (B .charge c b)
(A +ᶜ B) .charge/0 {inl a} = cong inl (A .charge/0)
(A +ᶜ B) .charge/0 {inr b} = cong inr (B .charge/0)
(A +ᶜ B) .charge/+ {inl a} = cong inl (A .charge/+)
(A +ᶜ B) .charge/+ {inr b} = cong inr (B .charge/+)

Σᶜ : (X : 𝒱) ⦃ _ : IsDiscrete X ⦄ → (val X → 𝒞) → 𝒞
Σᶜ X A .U = Σᵛ X (U ∘ A)
Σᶜ X A .charge c (x , a) = x , A x .charge c a
Σᶜ X A .charge/0 {x , a} = cong (x ,_) (A x .charge/0)
Σᶜ X A .charge/+ {x , a} = cong (x ,_) (A x .charge/+)
syntax Σᶜ X (λ x → A) = [ x ∈ X ] ⋊ A

_⋊_ : (X : 𝒱) ⦃ _ : IsDiscrete X ⦄ → 𝒞 → 𝒞
X ⋊ A = Σᶜ X (const A)

opaque
  unfolding M

  F : 𝒱 → 𝒞
  F X .U = M X
  F X .charge c (c' , x) = c +ℂ c' , x
  F X .charge/0 {c , x} = cong (_, x) (+ℂ-identityˡ c)
  F X .charge/+ {c , x} {c₁} {c₂} = cong (_, x) (+ℂ-assoc c₁ c₂ c)

  ret : val X → cmp (F X)
  ret {X} = M-ret {X}

  bind : cmp (F X) → (val X → cmp A) → cmp A
  bind {A = A} (c , x) k = A .charge c (k x)

  variable
    Δ : 𝒞

  bind' : (Δ ⊸ F X) → (val X → cmp A) → (Δ ⊸ A)
  bind' {A = A} e k .U δ = let (c , x) = e .U δ in A .charge c (k x)
  bind' {Δ} {A = A} e k .charge c δ =
      A .charge (e .U (Δ .charge c δ) .fst) (k (e .U (Δ .charge c δ) .snd))
    ≡⟨ cong (λ hole → A .charge (hole .fst) (k (hole .snd))) (e .charge c δ) ⟩
      A .charge (c +ℂ e .U δ .fst) (k (e .U δ .snd))
    ≡⟨ A .charge/+ ⟩
      A .charge c (A .charge (e .U δ .fst) (k (e .U δ .snd)))
    ∎

module Demo where
  double : cmp (ℕᵛ ⇀ F ℕᵛ)
  double zero = ret 0
  double (suc n) =
    bind {A = F ℕᵛ} (double n) λ n' →
    ret (suc (suc n'))

  BQ : 𝒞
  BQ = F (Listᵛ ℕᵛ ×ᵛ Listᵛ ℕᵛ)

  LQ : 𝒞
  LQ = F (Listᵛ ℕᵛ)

  opaque
    unfolding ℂ

    dequeue : LQ ⊸ (ℕᵛ ⋊ LQ)
    dequeue = bind' id⊸ λ
      { []      → 0 , ret []
      ; (x ∷ l) → x , LQ .charge 1 (ret l) }
