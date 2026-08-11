module Calf.Core.Cost where

open import Calf.Value
open import Calf.Value.Nat
open import Calf.Value.Unit
open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat.Literals public
import Cubical.Data.Nat.Properties as Nat

module _ {A : Type} where
  LeftIdentity : A → (A → A → A) → Type
  LeftIdentity e _∙_ = ∀ x → e ∙ x ≡ x

  RightIdentity : A → (A → A → A) → Type
  RightIdentity e _∙_ = ∀ x → x ∙ e ≡ x

  Associative : (A → A → A) → Type
  Associative _∙_ = ∀ x y z → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z)

  Commutative : (A → A → A) → Type
  Commutative _∙_ = ∀ x y → x ∙ y ≡ y ∙ x

`_ = fromNat

opaque
  ℂ : 𝒱
  ℂ = ℕ

  isSetℂ : isSet ℂ
  isSetℂ = isSetℕ

  0ℂ : ℂ
  0ℂ = 0

  _+ℂ_ : ℂ → ℂ → ℂ
  _+ℂ_ = _+_

  +ℂ-identityˡ : LeftIdentity 0ℂ _+ℂ_
  +ℂ-identityˡ _ = refl

  +ℂ-identityʳ : RightIdentity 0ℂ _+ℂ_
  +ℂ-identityʳ = Nat.+-zero

  +ℂ-assoc : Associative _+ℂ_
  +ℂ-assoc c₁ c₂ c₃ = sym (Nat.+-assoc c₁ c₂ c₃)

  +ℂ-comm : Commutative _+ℂ_
  +ℂ-comm c₁ c₂ = Nat.+-comm c₁ c₂

  ℕ→ℂ : ℕ → ℂ
  ℕ→ℂ n = ` n

instance
  fromNatℂ : HasFromNat ℂ
  fromNatℂ = record { Constraint = λ _ → ⊤ ; fromNat = λ n → ℕ→ℂ n }

variable
  c c' c₁ c₂ : ℂ

_⊙_ : ℕ → ℂ → ℂ
zero ⊙ c = 0ℂ
suc n ⊙ c = c +ℂ (n ⊙ c)

⊙-+ : ∀ n c₁ c₂ → n ⊙ (c₁ +ℂ c₂) ≡ (n ⊙ c₁) +ℂ (n ⊙ c₂)
⊙-+ zero c₁ c₂ = sym (+ℂ-identityˡ 0ℂ)
⊙-+ (suc n) c₁ c₂ =
    suc n ⊙ (c₁ +ℂ c₂)
  ≡⟨ cong ((c₁ +ℂ c₂) +ℂ_) (⊙-+ n c₁ c₂) ⟩
    (c₁ +ℂ c₂) +ℂ ((n ⊙ c₁) +ℂ (n ⊙ c₂))
  ≡⟨ +ℂ-assoc c₁ c₂ ((n ⊙ c₁) +ℂ (n ⊙ c₂)) ⟩
    c₁ +ℂ (c₂ +ℂ ((n ⊙ c₁) +ℂ (n ⊙ c₂)))
  ≡⟨ cong (c₁ +ℂ_) (sym (+ℂ-assoc c₂ (n ⊙ c₁) (n ⊙ c₂))) ⟩
    c₁ +ℂ ((c₂ +ℂ (n ⊙ c₁)) +ℂ (n ⊙ c₂))
  ≡⟨ cong (λ c → c₁ +ℂ (c +ℂ (n ⊙ c₂))) (+ℂ-comm c₂ (n ⊙ c₁)) ⟩
    c₁ +ℂ (((n ⊙ c₁) +ℂ c₂) +ℂ (n ⊙ c₂))
  ≡⟨ cong (c₁ +ℂ_) (+ℂ-assoc (n ⊙ c₁) c₂ (n ⊙ c₂)) ⟩
    c₁ +ℂ ((n ⊙ c₁) +ℂ (c₂ +ℂ (n ⊙ c₂)))
  ≡⟨ sym (+ℂ-assoc c₁ (n ⊙ c₁) (c₂ +ℂ (n ⊙ c₂))) ⟩
    (suc n ⊙ c₁) +ℂ (suc n ⊙ c₂)
  ∎

⊙-+-left : ∀ n m c → (n + m) ⊙ c ≡ (n ⊙ c) +ℂ (m ⊙ c)
⊙-+-left zero m c = sym (+ℂ-identityˡ (m ⊙ c))
⊙-+-left (suc n) m c =
    (suc n + m) ⊙ c
  ≡⟨ cong (c +ℂ_) (⊙-+-left n m c) ⟩
    c +ℂ ((n ⊙ c) +ℂ (m ⊙ c))
  ≡⟨ sym (+ℂ-assoc c (n ⊙ c) (m ⊙ c)) ⟩
    (suc n ⊙ c) +ℂ (m ⊙ c)
  ∎
