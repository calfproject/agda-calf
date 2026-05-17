{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Data.Equality.Conversion
open import Cubical.Data.Empty
open import Data.List
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Function

open import Calf.Directed

module Calf.CBPV where

open import Agda.Builtin.FromNat renaming (Number to HasFromNat)
import Data.Nat.Literals

instance
  fromNatℕ : HasFromNat ℕ
  fromNatℕ = Data.Nat.Literals.number


module _ {A : Type} where
  open import Algebra.Definitions {A = A} _≡_ public

opaque
  ℂ : 𝒱
  ℂ = ω

  0ℂ : val ℂ
  0ℂ = 0

  _+ℂ_ : val ℂ → val ℂ → val ℂ
  _+ℂ_ = _+_

  +ℂ-identityˡ : LeftIdentity 0ℂ _+ℂ_
  +ℂ-identityˡ c = eqToPath (+-identityˡ c)

  +ℂ-assoc : Associative _+ℂ_
  +ℂ-assoc c₁ c₂ c₃ = eqToPath (+-assoc c₁ c₂ c₃)

  +ℂ-comm : Commutative _+ℂ_
  +ℂ-comm c₁ c₂ = eqToPath (+-comm c₁ c₂)

  ℕ→ℂ : ℕ → val ℂ
  ℕ→ℂ n = n

instance
  fromNatℂ : HasFromNat (val ℂ)
  fromNatℂ = record { Constraint = λ _ → ⊤ ; fromNat = λ n → ℕ→ℂ n }

`_ = fromNat

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
(A +ᶜ B) .charge c (inj₁ a) = inj₁ (A .charge c a)
(A +ᶜ B) .charge c (inj₂ b) = inj₂ (B .charge c b)
(A +ᶜ B) .charge/0 {inj₁ a} = cong inj₁ (A .charge/0)
(A +ᶜ B) .charge/0 {inj₂ b} = cong inj₂ (B .charge/0)
(A +ᶜ B) .charge/+ {inj₁ a} = cong inj₁ (A .charge/+)
(A +ᶜ B) .charge/+ {inj₂ b} = cong inj₂ (B .charge/+)

Σᶜ : (X : 𝒱) ⦃ _ : IsDiscrete X ⦄ → (val X → 𝒞) → 𝒞
Σᶜ X A .U = Σᵛ X (U ∘ A)
Σᶜ X A .charge c (x , a) = x , A x .charge c a
Σᶜ X A .charge/0 {x , a} = cong (x ,_) (A x .charge/0)
Σᶜ X A .charge/+ {x , a} = cong (x ,_) (A x .charge/+)
syntax Σᶜ X (λ x → A) = [ x ∈ X ] ⋊ A

_⋊_ : (X : 𝒱) ⦃ _ : IsDiscrete X ⦄ → 𝒞 → 𝒞
X ⋊ A = Σᶜ X (const A)

data _U⊗_ (A B : 𝒞) : Type where
  inj : (a : cmp A) (b : cmp B) (c : val ℂ) → A U⊗ B
  law₁ : ∀ c c' a b → inj (A .charge c' a) b c ≡ inj a b (c +ℂ c')
  law₂ : ∀ c c' a b → inj a (B .charge c' b) c ≡ inj a b (c +ℂ c')
  squash : isSet (A U⊗ B)

_⊗_ : 𝒞 → 𝒞 → 𝒞
(A ⊗ B) .U .val = A U⊗ B
(A ⊗ B) .U .isPreorder = {!   !}
(A ⊗ B) .charge c (inj a b c') = inj a b (c +ℂ c')
(A ⊗ B) .charge c (law₁ c₁ c' a b i) = lemma i
  where
    lemma : inj (A .charge c' a) b (c +ℂ c₁) ≡ inj a b (c +ℂ (c₁ +ℂ c'))
    lemma =
        inj (A .charge c' a) b (c +ℂ c₁)
      ≡⟨ law₁ (c +ℂ c₁) c' a b ⟩
        inj a b ((c +ℂ c₁) +ℂ c')
      ≡⟨ cong (inj a b) (+ℂ-assoc c c₁ c') ⟩
        inj a b (c +ℂ (c₁ +ℂ c'))
      ∎
(A ⊗ B) .charge c (law₂ c₁ c' a b i) = lemma i
  where
    lemma : inj a (B .charge c' b) (c +ℂ c₁) ≡ inj a b (c +ℂ (c₁ +ℂ c'))
    lemma =
        inj a (B .charge c' b) (c +ℂ c₁)
      ≡⟨ law₂ (c +ℂ c₁) c' a b ⟩
        inj a b ((c +ℂ c₁) +ℂ c')
      ≡⟨ cong (inj a b) (+ℂ-assoc c c₁ c') ⟩
        inj a b (c +ℂ (c₁ +ℂ c'))
      ∎
(A ⊗ B) .charge c (squash _ _ _ _ _ _) = {!   !}
(A ⊗ B) .charge/0 {inj a b c} = cong (inj a b) (+ℂ-identityˡ c)
(A ⊗ B) .charge/0 {law₁ c c' a b i} j = squash (inj a b c') (inj a b c') refl refl {!   !} {!   !}
(A ⊗ B) .charge/0 {law₂ c c' a b i} = {! squash  !}
(A ⊗ B) .charge/0 {squash _ _ _ _ _ _} = {!   !}
(A ⊗ B) .charge/+ {inj a b c} = cong (inj a b) (+ℂ-assoc _ _ c)
(A ⊗ B) .charge/+ {law₁ c c' a b i} = {! squash  !}
(A ⊗ B) .charge/+ {law₂ c c' a b i} = {! squash  !}
(A ⊗ B) .charge/+ {squash _ _ _ _ _ _} = {!   !}

_∥_ : cmp A → cmp B → cmp (A ⊗ B)
a ∥ b = inj a b 0ℂ

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

  bind/charge : ∀ {c e k} → bind {A = A} (F X .charge c e) k ≡ A .charge c (bind {A = A} e k)
  bind/charge = {!   !}

  F/η : ∀ {x k} → bind {A = A} (ret {X} x) k ≡ k x
  F/η = {!   !}

  syntax bind {A = A} e (λ x → k) = bind[ A ] x ← e ⨾ k

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
  syntax bind' e (λ x → k) = bind x ← e ⨾ k

  F⊗-fwd : (F X ⊗ F Y) ⊸ F (X ×ᵛ Y)
  F⊗-fwd .U (inj (cx , x) (cy , y) c) = c +ℂ (cx +ℂ cy) , x , y
  F⊗-fwd .U (law₁ c c' a b i) = {!   !}
  F⊗-fwd .U (law₂ c c' a b i) = {!   !}
  F⊗-fwd .U (squash e e₁ x y i i₁) = {!   !}
  F⊗-fwd .charge = {!   !}

  F⊗-bwd : F (X ×ᵛ Y) ⊸ (F X ⊗ F Y)
  F⊗-bwd .U (c , x , y) = inj (0ℂ , x) (0ℂ , y) c
  F⊗-bwd .charge = {!   !}

par : cmp (F X) → cmp (F Y) → cmp (F (X ×ᵛ Y))
par ex ey = F⊗-fwd .U (ex ∥ ey)

module Demo where
  double : cmp (ℕᵛ ⇀ F ℕᵛ)
  double zero = ret 0
  double (suc n) =
    F ℕᵛ .charge 1 $
    bind[ F ℕᵛ ] n' ← double n ⨾
    ret (suc (suc n'))

  opaque
    unfolding ℂ

    DOUBLE : ℕ → ℕ
    DOUBLE zero = 0
    DOUBLE (suc n) = suc (suc (DOUBLE n))

    foo : double ⊑[ U (ℕᵛ ⇀ F ℕᵛ) ] (λ n → F ℕᵛ .charge (` n) (ret (DOUBLE n)))
    foo = ⊑-funext lemma
      where
        lemma : ∀ n → double n ⊑[ U (F ℕᵛ) ] F ℕᵛ .charge (` n) (ret (DOUBLE n))
        lemma zero = ≡⇒⊑ (sym (F ℕᵛ .charge/0))
        lemma (suc n) =
          ⊑-trans (⊑-mono (λ e → F ℕᵛ .charge 1 (bind e _)) (lemma n)) $
          ⊑-trans (⊑-mono {X = U (F ℕᵛ)} (F ℕᵛ .charge 1) (⊑-trans (≡⇒⊑ bind/charge) (⊑-mono {X = U (F ℕᵛ)} (F ℕᵛ .charge n) (≡⇒⊑ F/η)))) $
          ≡⇒⊑ (sym (F ℕᵛ .charge/+ {c₁ = 1}))

  BQ : 𝒞
  BQ = F (Listᵛ ℕᵛ ×ᵛ Listᵛ ℕᵛ)

  LQ : 𝒞
  LQ = F (Listᵛ ℕᵛ)

  φ : BQ ⊸ LQ
  φ =
    bind (l₁ , l₂) ← id⊸ ⨾
    LQ .charge (` length l₁) (ret (l₂ ++ reverse l₁))

  dequeue : LQ ⊸ (ℕᵛ ⋊ LQ)
  dequeue = bind' id⊸ λ
    { []      → 0 , ret []
    ; (x ∷ l) → x , LQ .charge 1 (ret l) }
