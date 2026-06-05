open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Calf.Giralf where

open import Calf.Value
open import Calf.Core.Cost
open import Calf.Computation
open import Calf.Computation.Tensor
open import Calf.Computation.Lolli
open import Calf.Computation.Potential
open import Calf.Computation.Cost
open import Calf.Computation.PList1
open import Cubical.Data.Sigma

Context : Type₁
Context = 𝒞 × val ℂ  -- List 𝒞 × val ℙ

variable
  p p' q q' r r' : val ℂ


infix 3 _⊢_

_⊢_ : Context → 𝒞 → Type
Δ , p ⊢ A = ▷'[ p ] Δ ⊸ A

idᴳ : A , 0ℂ ⊢ A
idᴳ {A} = transport (cong (_⊸ A) (sym ▷'/0)) idᶜ

module _ where  -- promonoid
  _⋎₀ : val ℂ → Type
  q ⋎₀ = 0ℂ ≡ q

  _⋎₂_ : val ℂ → (val ℂ × val ℂ) → Type  -- promonoid
  q ⋎₂ (q₁ , q₂) = q₁ +ℂ q₂ ≡ q

  -- _⋎_ : val ℂ → List (val ℂ) → Type  -- promonoid
  -- p ⋎ ps = foldr _+ℂ_ 0ℂ ps ≡ p

cmpᴳ : 𝒞 → Type
cmpᴳ = ⊤ , 0ℂ ⊢_
-- cmpᴳ A = ∀ {q} → q ⋎₀ → (⊤ , q ⊢ A)

cmpᴳ→cmp : cmpᴳ A → cmp A
cmpᴳ→cmp e = e .U (transport (cong cmp (sym ▷'/0)) (ret _))


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

nil₁ᴳ : cmpᴳ (PList₁ p X)
nil₁ᴳ {p} {X} = transport (cong (_⊸ PList₁ p X) (sym ▷'/0)) (bind' λ _ → pnil₁)

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


--     ⊥ᵍ : 𝒞
--     absurdᵍ : ∀ {Δ Δ' q q' C}
--       → (Δ , q) ≡⋎ᵐ Vec.[ (Δ' , q') ]
--       → Δ' ⨾ q' ⊢ ⊥ᵍ
--       → Δ ⨾ q ⊢ C

--     _⊎ᵍ_ : 𝒞 → 𝒞 → 𝒞
--     inj₁ᵍ : ∀ {Δ Δ' q q' A B}
--       → (Δ , q) ≡⋎ᵐ Vec.[ (Δ' , q') ]
--       → Δ' ⨾ q' ⊢ A
--       → Δ ⨾ q ⊢ (A ⊎ᵍ B)
--     inj₂ᵍ : ∀ {Δ Δ' q q' A B}
--       → (Δ , q) ≡⋎ᵐ Vec.[ (Δ' , q') ]
--       → Δ' ⨾ q' ⊢ B
--       → Δ ⨾ q ⊢ (A ⊎ᵍ B)
--     caseᵍ : ∀ {Δ Δ₁ Δ₂ q q₁ q₂ A B C}
--       → (Δ , q) ≡⋎ᵐ ((Δ₁ , q₁) Vec.∷ Vec.[ (Δ₂ , q₂) ])
--       → Δ₁ ⨾ q₁ ⊢ (A ⊎ᵍ B)
--       → (A ∷ Δ₂) ⨾ q₂ ⊢ C
--       → (B ∷ Δ₂) ⨾ q₂ ⊢ C
--       → Δ ⨾ q ⊢ C

--     ⊤ᵍ : 𝒞
--     trivᵍ : ∀ {Δ q}
--       → (Δ , q) ≡⋎ᵐ Vec.[]
--       → Δ ⨾ q ⊢ ⊤ᵍ
--     checkᵍ : ∀ {Δ Δ₁ Δ₂ q q₁ q₂ C}
--       → (Δ , q) ≡⋎ᵐ ((Δ₁ , q₁) Vec.∷ Vec.[ (Δ₂ , q₂) ])
--       → Δ₁ ⨾ q₁ ⊢ ⊤ᵍ
--       → Δ₂ ⨾ q₂ ⊢ C
--       → Δ ⨾ q ⊢ C

--     _⊗ᵍ_ : 𝒞 → 𝒞 → 𝒞
--     tensorᵍ : ∀ {Δ Δ₁ Δ₂ q q₁ q₂ A B}
--       → (Δ , q) ≡⋎ᵐ ((Δ₁ , q₁) Vec.∷ Vec.[ (Δ₂ , q₂) ])
--       → Δ₁ ⨾ q₁ ⊢ A
--       → Δ₂ ⨾ q₂ ⊢ B
--       → Δ ⨾ q ⊢ (A ⊗ᵍ B)
--     splitᵍ : ∀ {Δ Δ₁ Δ₂ q q₁ q₂ A B C}
--       → (Δ , q) ≡⋎ᵐ ((Δ₁ , q₁) Vec.∷ Vec.[ (Δ₂ , q₂) ])
--       → Δ₁ ⨾ q₁ ⊢ (A ⊗ᵍ B)
--       → (A ∷ B ∷ Δ₂) ⨾ q₂ ⊢ C
--       → Δ ⨾ q ⊢ C

--     listᵍ : (ℂ × ℂ) → 𝒞 → 𝒞
--     nilᵍ : ∀ {Δ q A ps}
--       → (Δ , q) ≡⋎ᵐ Vec.[]
--       → Δ ⨾ q ⊢ (listᵍ ps A)
--     consᵍ : ∀ {Δ Δ₁ Δ₂ q q₁ q₂ A ps}
--       → (Δ , q) ≡⋎ᵐ ((Δ₁ , q₁ + ps .proj₁) Vec.∷ Vec.[ (Δ₂ , q₂) ])
--       → Δ₁ ⨾ q₁ ⊢ A
--       → Δ₂ ⨾ q₂ ⊢ listᵍ (shift ps) A
--       → Δ ⨾ q ⊢ listᵍ ps A
--     foldrᵍ : ∀ {Δ Δ' q q' A ps} {B : ℕ → 𝒞}
--       → (Δ , q) ≡⋎ᵐ Vec.[ (Δ' , q') ]
--       → Δ' ⨾ q' ⊢ listᵍ ps A
--       → (∀ {n} → cmpᵍ (B n))
--       → (∀ {n} → ((B (ℕ.suc n)) ∷ A ∷ []) ⨾ ((GA.fold ps shift n) .proj₁) ⊢ B n)
--       → Δ ⨾ q ⊢ B 0

--   variable
--     p q r : ℂ
