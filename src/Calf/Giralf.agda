open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma

module Calf.Giralf where

open import Calf.Value
open import Calf.Value.Nat
open import Calf.Core.Cost
open import Calf.Computation
open import Calf.Computation.Product
open import Calf.Computation.Tensor
open import Calf.Computation.Lolli
open import Calf.Computation.Potential
open import Calf.Computation.Cost
open import Calf.Computation.PList1
open import Calf.Computation.PList2
open import Calf.Computation.Free

Context : Type₁
Context = 𝒞 × val ℂ  -- List 𝒞 × val ℙ

variable
  p p' p₁ p₂ q q' q₁ q₂ r r' : val ℂ


infix 1 _⊢_

_⊢_ : Context → 𝒞 → Type
Δ , q ⊢ A = ▷'[ q ] Δ ⊸ A

idᴳ : A , 0ℂ ⊢ A
idᴳ {A} = transport (cong (_⊸ A) (sym ▷'/0)) idᶜ

module _ where  -- promonoid
  _⋎₀ : val ℂ → Type
  q ⋎₀ = 0ℂ ≡ q

  _⋎₂_ : val ℂ → (val ℂ × val ℂ) → Type  -- promonoid
  q ⋎₂ (q₁ , q₂) = q₁ +ℂ q₂ ≡ q

  -- _⋎_ : val ℂ → List (val ℂ) → Type  -- promonoid
  -- p ⋎ ps = foldr _+ℂ_ 0ℂ ps ≡ p

letᴳ :
  q ⋎₂ (q₁ , q₂)
  → A , q₁ ⊢ B
  → B , q₂ ⊢ C
  → A , q ⊢ C
letᴳ = {!   !}

cmpᴳ : 𝒞 → Type
cmpᴳ = ⊤ , 0ℂ ⊢_
-- cmpᴳ A = ∀ {q} → q ⋎₀ → (⊤ , q ⊢ A)

cmpᴳ→cmp : cmpᴳ A → cmp A
cmpᴳ→cmp e = e .U (transport (cong cmp (sym ▷'/0)) (ret _))

cmp→cmpᴳ : cmp A → cmpᴳ A
cmp→cmpᴳ {A} e = transport (cong (_⊸ A) (sym ▷'/0)) (bind' λ _ → e)


module _ where
  storeᴳ : ∀ p
    → q ⋎₂ (p , q')
    → Δ , q' ⊢ A
    → Δ , q ⊢ ▷'[ p ] A
  storeᴳ p split e =
    transport (cong (_⊸ _) (sym ▷'/+ ∙ cong (▷'[_] _) split)) (▷'-map e)

  releaseᴳ :
    Δ , q ⊢ ▷'[ p ] B
    → B , p ⊢ A
    → Δ , q ⊢ A
  releaseᴳ e k = e ⨾ᶜ k

chargeᴳ : ∀ p
  → q ⋎₂ (p , q')
  → Δ , q' ⊢ A
  → Δ , q ⊢ A
chargeᴳ p split e =
  releaseᴳ (storeᴳ p split e) release'

module _ where
  getᴳ : ∀ p
    → q' ⋎₂ (p , q)
    → Δ , q' ⊢ A
    → Δ , q ⊢ ◁'[ p ] A
  getᴳ p split = transport (sym (pot-cost ∙ cong (_⊸ _) (sym ▷'/+ ∙ cong (▷'[_] _) split)))

  payᴳ :
    q ⋎₂ (p , q')
    → Δ , q' ⊢ ◁'[ p ] A
    → Δ , q ⊢ A
  payᴳ split = transport (pot-cost ∙ cong (_⊸ _) (sym ▷'/+ ∙ cong (▷'[_] _) split))

module _ where
  nil₁ᴳ : cmpᴳ (PList₁ p X)
  nil₁ᴳ = cmp→cmpᴳ pnil₁

  cons₁ᴳ :
    q ⋎₂ (p , q')
    → val X
    → Δ , q' ⊢ PList₁ p X
    → Δ , q ⊢ PList₁ p X
  cons₁ᴳ split x e = storeᴳ _ split e ⨾ᶜ pcons₁ x

  foldr₁ᴳ :
    cmpᴳ A
    → (val X → A , p ⊢ A)
    → Δ , q ⊢ PList₁ p X
    → Δ , q ⊢ A
  foldr₁ᴳ e-nil e-cons e = e ⨾ᶜ pfoldr₁ (cmpᴳ→cmp e-nil) e-cons

module _ where
  nil₂ᴳ : cmpᴳ (PList₂ p₁ p₂ X)
  nil₂ᴳ = cmp→cmpᴳ pnil₂

  cons₂ᴳ :
    q ⋎₂ (p₁ , q')
    → val X
    → Δ , q' ⊢ PList₂ (p₂ +ℂ p₁) p₂ X
    → Δ , q ⊢ PList₂ p₁ p₂ X
  cons₂ᴳ split x e = storeᴳ _ split e ⨾ᶜ pcons₂ x

  foldr₂ᴳ :
    (A : val ℂ → 𝒞)
    → (∀ r → cmpᴳ (A r))
    → (∀ r → val X → A (p₂ +ℂ r) , r ⊢ A r)
    → Δ , q ⊢ PList₂ p₁ p₂ X
    → Δ , q ⊢ A p₁
  foldr₂ᴳ A e-nil e-cons e = e ⨾ᶜ pfoldr₂ A (cmpᴳ→cmp ∘ e-nil) e-cons

module _ where
  pairᴳ :
      Δ , q ⊢ A
    → Δ , q ⊢ B
    → Δ , q ⊢ A ×ᶜ B
  pairᴳ = pairᶜ

  proj₁ᴳ :
      Δ , q ⊢ A ×ᶜ B
    → Δ , q ⊢ A
  proj₁ᴳ {B = B} = _⨾ᶜ proj₁ᶜ {B = B}

  proj₂ᴳ :
      Δ , q ⊢ A ×ᶜ B
    → Δ , q ⊢ B
  proj₂ᴳ {A = A} = _⨾ᶜ proj₂ᶜ {A = A}


module Examples where
  id₁ : PList₁ (1 +ℂ p) X , 0ℂ ⊢ PList₁ p X
  id₁ =
    foldr₁ᴳ
      nil₁ᴳ
      (λ x →
        chargeᴳ 1 refl $
        cons₁ᴳ (+ℂ-identityʳ _) x $
        idᴳ
      )
      idᴳ

  snoc : ∀ p → val X → PList₁ (1 +ℂ p) X , p ⊢ PList₁ p X
  snoc p x =
    payᴳ (+ℂ-identityʳ _) $
    foldr₁ᴳ
      ( getᴳ p (+ℂ-identityʳ p) $
        cons₁ᴳ (+ℂ-identityʳ p) x $
        nil₁ᴳ
      )
      (λ y →
        chargeᴳ 1 refl $
        getᴳ p refl $
        cons₁ᴳ refl y $
        payᴳ (+ℂ-identityʳ p)
        idᴳ
      )
      idᴳ

  id₂ : ∀ p → PList₂ p 1 X , 0ℂ ⊢ PList₁ p X
  id₂ {X} p =
    foldr₂ᴳ
      (λ r → PList₁ r X)
      (λ r → nil₁ᴳ)
      (λ r x → cons₁ᴳ (+ℂ-identityʳ r) x id₁)
      idᴳ

  qreverse : PList₂ 0 1 X , 0ℂ ⊢ PList₁ 0 X
  qreverse {X} =
    foldr₂ᴳ
      (λ r → PList₁ r X)
      (λ r → nil₁ᴳ)
      snoc
      idᴳ

  open import Cubical.Data.Bool
  import Cubical.Data.Nat.Properties as Nat
  open import Cubical.Data.Nat.Order
  open import Cubical.Relation.Nullary

  _≤ᵇ_ : ℕ → ℕ → Bool
  m ≤ᵇ n with ≤Dec m n
  ... | yes p = true
  ... | no ¬p = false

  insert : ∀ p → val ℕᵛ → PList₁ (1 +ℂ p) ℕᵛ , p ⊢ PList₁ p ℕᵛ
  insert p x =
    payᴳ (+ℂ-identityʳ p) $
    proj₁ᴳ {B = PList₁ p ℕᵛ} $
    foldr₁ᴳ
      {A = (◁'[ p ] PList₁ p ℕᵛ) ×ᶜ PList₁ p ℕᵛ}
      (pairᴳ
        (getᴳ p (+ℂ-identityʳ p) (cons₁ᴳ (+ℂ-identityʳ p) x nil₁ᴳ))
        nil₁ᴳ
      )
      (λ y →
        chargeᴳ 1 refl $
        pairᴳ
          ( getᴳ p refl $
            if x ≤ᵇ y
              then cons₁ᴳ refl x (cons₁ᴳ (+ℂ-identityʳ p) y (proj₂ᴳ idᴳ))
              else cons₁ᴳ refl y (payᴳ (+ℂ-identityʳ p) (proj₁ᴳ {B = PList₁ p ℕᵛ} idᴳ))
          )
          (cons₁ᴳ (+ℂ-identityʳ p) y (proj₂ᴳ {A = ◁'[ p ] PList₁ p ℕᵛ} idᴳ))
      )
      idᴳ

  isort : PList₂ 0 1 ℕᵛ , 0ℂ ⊢ PList₁ 0 ℕᵛ
  isort =
    foldr₂ᴳ
      (λ r → PList₁ r ℕᵛ)
      (λ r → nil₁ᴳ)
      insert
      idᴳ

  variable
    k : ℕ

  split : PList₁ c ℕᵛ , 0ℂ ⊢ PList₁ c ℕᵛ ⊗ PList₁ c ℕᵛ
  split = {!   !}

  merge : PList₁ (` suc k) ℕᵛ ⊗ PList₁ (` suc k) ℕᵛ , 0ℂ ⊢ PList₁ (` k) ℕᵛ
  merge = {!   !}

  msort/clocked : (k k' : ℕ) → PList₁ (` (k + k')) ℕᵛ , 0ℂ ⊢ PList₁ (` k') ℕᵛ
  msort/clocked zero k' = idᴳ
  msort/clocked (suc k) k' =
    letᴳ (+ℂ-identityˡ _) split $
    letᴳ (+ℂ-identityˡ _)
      (transport
        (cong (_⊸ _) lemma)
        (map₂ (msort/clocked k (suc k')) (msort/clocked k (suc k')))) $
    merge
      where
        lemma :
          (▷'[ 0ℂ ] PList₁ (` (k + suc k')) ℕᵛ) ⊗ (▷'[ 0ℂ ] PList₁ (` (k + suc k')) ℕᵛ)
          ≡ ▷'[ 0ℂ ] (PList₁ (` suc (k + k')) ℕᵛ ⊗ PList₁ (` suc (k + k')) ℕᵛ)
        lemma =
            (▷'[ 0ℂ ] PList₁ (` (k + suc k')) ℕᵛ) ⊗ (▷'[ 0ℂ ] PList₁ (` (k + suc k')) ℕᵛ)
          ≡⟨ cong₂ _⊗_ ▷'/0 ▷'/0 ⟩
            PList₁ (` (k + suc k')) ℕᵛ ⊗ PList₁ (` (k + suc k')) ℕᵛ
          ≡⟨ cong (λ n → PList₁ (` n) ℕᵛ ⊗ PList₁ (` n) ℕᵛ) (Nat.+-suc k k') ⟩
            PList₁ (` suc (k + k')) ℕᵛ ⊗ PList₁ (` suc (k + k')) ℕᵛ
          ≡⟨ sym ▷'/0 ⟩
            ▷'[ 0ℂ ] (PList₁ (` suc (k + k')) ℕᵛ ⊗ PList₁ (` suc (k + k')) ℕᵛ)
          ∎
