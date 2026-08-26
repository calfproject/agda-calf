module Calf.Value.Omega where

open import Calf.Core.Directed
open import Calf.Value
open import Cubical.Data.Nat using (ℕ; zero; suc; HasFromNat) renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Order
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Data.Unit

data ω₀ : 𝒱 where
  zero : ω₀
  suc : (n : ω₀) → ω₀
  rel : (𝕚 : 𝟚) (n : ω₀) → ω₀
  rel-0𝟚 : ∀ n → rel 0𝟚 n ≡ n
  rel-1𝟚 : ∀ n → rel 1𝟚 n ≡ suc n

infixl 6 _+₀_

_+₀_ : ω₀ → ω₀ → ω₀
zero +₀ n = n
suc m +₀ n = suc (m +₀ n)
rel 𝕚 m +₀ n = rel 𝕚 (m +₀ n)
rel-0𝟚 m i +₀ n = rel-0𝟚 (m +₀ n) i
rel-1𝟚 m i +₀ n = rel-1𝟚 (m +₀ n) i

+₀-identityʳ : ∀ n → n +₀ zero ≡ n
+₀-identityʳ zero = refl
+₀-identityʳ (suc n) = cong suc (+₀-identityʳ n)
+₀-identityʳ (rel 𝕚 n) = cong (rel 𝕚) (+₀-identityʳ n)
+₀-identityʳ (rel-0𝟚 n i) = cong (λ x → rel-0𝟚 x i) (+₀-identityʳ n)
+₀-identityʳ (rel-1𝟚 n i) = cong (λ x → rel-1𝟚 x i) (+₀-identityʳ n)

+₀-assoc : ∀ m n o → (m +₀ n) +₀ o ≡ m +₀ (n +₀ o)
+₀-assoc zero         _ _ = refl
+₀-assoc (suc m)      n o = cong suc (+₀-assoc m n o)
+₀-assoc (rel 𝕚 m)    n o = cong (rel 𝕚) (+₀-assoc m n o)
+₀-assoc (rel-0𝟚 m i) n o = cong (λ x → rel-0𝟚 x i) (+₀-assoc m n o)
+₀-assoc (rel-1𝟚 m i) n o = cong (λ x → rel-1𝟚 x i) (+₀-assoc m n o)

ℕ→ω₀ : ℕ → ω₀
ℕ→ω₀ zero = zero
ℕ→ω₀ (suc n) = suc (ℕ→ω₀ n)

ℕ→ω₀-+ : ∀ m n → ℕ→ω₀ (m +ℕ n) ≡ ℕ→ω₀ m +₀ ℕ→ω₀ n
ℕ→ω₀-+ zero n = refl
ℕ→ω₀-+ (suc m) n = cong suc (ℕ→ω₀-+ m n)


ω : 𝒱
ω = ∥ ω₀ ∥ᴾ

isPreorderω : isPreorder ω
isPreorderω = isPreorderP

ℕ→ω : ℕ → ω
ℕ→ω = ηᴾ ∘ ℕ→ω₀

instance
  fromNatω : HasFromNat ω
  fromNatω = record { Constraint = λ _ → ⊤ ; fromNat = λ n → ℕ→ω n }

infixl 6 _+_

0ω : ω
0ω = ℕ→ω 0

_+_ : ω → ω → ω
_+_ = map2ᴾ _+₀_

open import Algebra.Definitions {A = ω} _≡_

+-identityˡ : LeftIdentity 0ω _+_
+-identityˡ = rec-unique isPreorderP (0ω +_) (λ n → n) λ _ → refl

+-identityʳ : RightIdentity 0ω _+_
+-identityʳ = rec-unique isPreorderP (_+ 0ω) (λ n → n) λ n → cong ηᴾ (+₀-identityʳ n)

+-assoc : Associative _+_
+-assoc m n o =
  funExt⁻
    (rec-unique2 (isLocalΠ λ _ → isPreorderP)
      (λ m n o → (m + n) + o)
      (λ m n o → m + (n + o))
      (λ x y → funExt (rec-unique isPreorderP _ _ λ z → cong ηᴾ (+₀-assoc x y z)))
      m n)
    o

ℕ→ω-+ : ∀ m n → ℕ→ω (m +ℕ n) ≡ ℕ→ω m + ℕ→ω n
ℕ→ω-+ m n = cong ηᴾ (ℕ→ω₀-+ m n)

⊑-suc : ∀ n → ηᴾ n ⊑ ηᴾ (suc n)
⊑-suc n = (λ 𝕚 → ηᴾ (rel 𝕚 n)) , cong ηᴾ (rel-0𝟚 n) , cong ηᴾ (rel-1𝟚 n)

⊑-+ : ∀ p m → ℕ→ω m ⊑ ℕ→ω (p +ℕ m)
⊑-+ zero m = ⊑-refl
⊑-+ (suc p) m = ⊑-trans isPreorderω (⊑-+ p m) (⊑-suc (ℕ→ω₀ (p +ℕ m)))

≤⇒⊑ : ∀ {m n} → m ≤ n → ℕ→ω m ⊑ ℕ→ω n
≤⇒⊑ (p , p+m≡n) = ⊑∙≡ (⊑-+ p _) (cong ℕ→ω p+m≡n)


private
  isSetω : isSet ω
  isSetω = isPreorder→isSet isPreorderω

  thin-path : (P Q : 𝟚 → ω) → P 0𝟚 ≡ Q 0𝟚 → P 1𝟚 ≡ Q 1𝟚 → ∀ 𝕚 → P 𝕚 ≡ Q 𝕚
  thin-path P Q p q 𝕚 =
    cong (λ e → path e 𝕚)
      (isPreorder→isThin isPreorderω _ _ (P , refl , refl) (Q , sym p , sym q))

  sucω : ω → ω
  sucω = mapᴾ suc

  relω : 𝟚 → ω → ω
  relω 𝕚 = mapᴾ (rel 𝕚)

  rel-suc : ∀ 𝕚 n → ηᴾ (rel 𝕚 (suc n)) ≡ ηᴾ (suc (rel 𝕚 n))
  rel-suc 𝕚 n =
    thin-path (λ 𝕚 → ηᴾ (rel 𝕚 (suc n))) (λ 𝕚 → ηᴾ (suc (rel 𝕚 n)))
      (cong ηᴾ (rel-0𝟚 (suc n)) ∙ sym (cong (sucω ∘ ηᴾ) (rel-0𝟚 n)))
      (cong ηᴾ (rel-1𝟚 (suc n)) ∙ sym (cong (sucω ∘ ηᴾ) (rel-1𝟚 n)))
      𝕚

  rel-rel : ∀ 𝕚 𝕛 n → ηᴾ (rel 𝕚 (rel 𝕛 n)) ≡ ηᴾ (rel 𝕛 (rel 𝕚 n))
  rel-rel 𝕚 𝕛 n =
    thin-path (λ 𝕚 → ηᴾ (rel 𝕚 (rel 𝕛 n))) (λ 𝕚 → ηᴾ (rel 𝕛 (rel 𝕚 n)))
      (cong ηᴾ (rel-0𝟚 (rel 𝕛 n)) ∙ sym (cong (relω 𝕛 ∘ ηᴾ) (rel-0𝟚 n)))
      (cong ηᴾ (rel-1𝟚 (rel 𝕛 n)) ∙ sym (rel-suc 𝕛 n) ∙ sym (cong (relω 𝕛 ∘ ηᴾ) (rel-1𝟚 n)))
      𝕚

  +-suc : ∀ m n → ηᴾ (m +₀ suc n) ≡ ηᴾ (suc (m +₀ n))
  +-suc zero n = refl
  +-suc (suc m) n = cong sucω (+-suc m n)
  +-suc (rel 𝕚 m) n = cong (relω 𝕚) (+-suc m n) ∙ rel-suc 𝕚 (m +₀ n)
  +-suc (rel-0𝟚 m i) n =
    isProp→PathP
      (λ i → isSetω (ηᴾ (rel-0𝟚 m i +₀ suc n)) (ηᴾ (suc (rel-0𝟚 m i +₀ n))))
      (cong (relω 0𝟚) (+-suc m n) ∙ rel-suc 0𝟚 (m +₀ n))
      (+-suc m n) i
  +-suc (rel-1𝟚 m i) n =
    isProp→PathP
      (λ i → isSetω (ηᴾ (rel-1𝟚 m i +₀ suc n)) (ηᴾ (suc (rel-1𝟚 m i +₀ n))))
      (cong (relω 1𝟚) (+-suc m n) ∙ rel-suc 1𝟚 (m +₀ n))
      (cong sucω (+-suc m n)) i

  +-rel : ∀ m 𝕚 n → ηᴾ (m +₀ rel 𝕚 n) ≡ ηᴾ (rel 𝕚 (m +₀ n))
  +-rel zero 𝕚 n = refl
  +-rel (suc m) 𝕚 n = cong sucω (+-rel m 𝕚 n) ∙ sym (rel-suc 𝕚 (m +₀ n))
  +-rel (rel 𝕛 m) 𝕚 n = cong (relω 𝕛) (+-rel m 𝕚 n) ∙ rel-rel 𝕛 𝕚 (m +₀ n)
  +-rel (rel-0𝟚 m i) 𝕚 n =
    isProp→PathP
      (λ i → isSetω (ηᴾ (rel-0𝟚 m i +₀ rel 𝕚 n)) (ηᴾ (rel 𝕚 (rel-0𝟚 m i +₀ n))))
      (cong (relω 0𝟚) (+-rel m 𝕚 n) ∙ rel-rel 0𝟚 𝕚 (m +₀ n))
      (+-rel m 𝕚 n) i
  +-rel (rel-1𝟚 m i) 𝕚 n =
    isProp→PathP
      (λ i → isSetω (ηᴾ (rel-1𝟚 m i +₀ rel 𝕚 n)) (ηᴾ (rel 𝕚 (rel-1𝟚 m i +₀ n))))
      (cong (relω 1𝟚) (+-rel m 𝕚 n) ∙ rel-rel 1𝟚 𝕚 (m +₀ n))
      (cong sucω (+-rel m 𝕚 n) ∙ sym (rel-suc 𝕚 (m +₀ n))) i

  +-comm₀ : ∀ m n → ηᴾ (m +₀ n) ≡ ηᴾ (n +₀ m)
  +-comm₀ m zero = cong ηᴾ (+₀-identityʳ m)
  +-comm₀ m (suc n) = +-suc m n ∙ cong sucω (+-comm₀ m n)
  +-comm₀ m (rel 𝕚 n) = +-rel m 𝕚 n ∙ cong (relω 𝕚) (+-comm₀ m n)
  +-comm₀ m (rel-0𝟚 n i) =
    isProp→PathP
      (λ i → isSetω (ηᴾ (m +₀ rel-0𝟚 n i)) (ηᴾ (rel-0𝟚 n i +₀ m)))
      (+-rel m 0𝟚 n ∙ cong (relω 0𝟚) (+-comm₀ m n))
      (+-comm₀ m n) i
  +-comm₀ m (rel-1𝟚 n i) =
    isProp→PathP
      (λ i → isSetω (ηᴾ (m +₀ rel-1𝟚 n i)) (ηᴾ (rel-1𝟚 n i +₀ m)))
      (+-rel m 1𝟚 n ∙ cong (relω 1𝟚) (+-comm₀ m n))
      (+-suc m n ∙ cong sucω (+-comm₀ m n)) i

+-comm : Commutative _+_
+-comm = rec-unique2 isPreorderP _+_ (λ m n → n + m) +-comm₀
