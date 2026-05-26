open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Calf.Giralf (ABS : Type) (ABS-isProp : isProp ABS) where

open import Calf.Value
open import Calf.Value.Closed ABS ABS-isProp
open import Calf.Core.Cost
open import Calf.Computation
open import Calf.Computation.Tensor
open import Calf.Computation.Open ABS ABS-isProp as ◯ᶜ
open import Calf.Computation.Closed ABS ABS-isProp as ●ᶜ
open import Calf.Computation.Glue ABS ABS-isProp
open import Calf.Computation.Potential ABS ABS-isProp
open import Cubical.Data.List
open import Cubical.Data.Sigma

Context : Type₁
Context = List 𝒞 × val ℙ


infix 3 _⊢_

_⊢_ : Context → 𝒞 → Type
Δ , p ⊢ A = ▷[ p ] (foldr _⊗_ {!   !} Δ) ⊸ A

_≡ᶜ⋎_ : Context → List Context → Type  -- promonoid
_≡ᶜ⋎_ = {!   !}

--     _≡ᶜ⋎_ : 𝒞 → List 𝒞 → Set
--     id-split : ∀ A → A ≡ᶜ⋎ [ A ]

--   _≡⋎ᵐ_ : ∀ {n} → (List 𝒞 × ℂ) → Vec (List 𝒞 × ℂ) n → Set
--   _≡⋎ᵐ_ = Perm-Split._≡⊔ᵐ_ _≡ᶜ⋎_

--   id-splits : ∀ {Δq} → Δq ≡⋎ᵐ (Δq Vec.∷ Vec.[])
--   id-splits = id-perm-split {𝒞} _≡ᶜ⋎_ id-split

--   cmpᵍ : 𝒞 → Set
--   cmpᵍ A = [] ⨾ zero ⊢ A

--   _⊸_ : 𝒞 → 𝒞 → 𝓥
--   A ⊸ B = meta⁺ ([ A ] ⨾ zero ⊢ B)

--   Uᵍ : 𝒞 → 𝓥
--   Uᵍ A = meta⁺ (cmpᵍ A)

--   field
--     idᵍ : ∀ {Δ q A}
--       → (Δ , q) ≡⋎ᵐ Vec.[ ([ A ] , zero) ]
--       → Δ ⨾ q ⊢ A

--     charge : ∀ {Δ Δ' q q' A} (p : ℂ)
--       → (Δ , q) ≡⋎ᵐ Vec.[ (Δ' , q' + p) ]
--       → Δ' ⨾ q' ⊢ A
--       → Δ ⨾ q ⊢ A

--     Fᵍ : 𝓥 → 𝒞
--     retᵍ : ∀ {Δ q X}
--       → (Δ , q) ≡⋎ᵐ Vec.[]
--       → valᵍ X
--       → Δ ⨾ q ⊢ (Fᵍ X)
--     bindᵍ : ∀ {Δ Δ₁ Δ₂ q q₁ q₂ X A}
--       → (Δ , q) ≡⋎ᵐ ((Δ₁ , q₁) Vec.∷ Vec.[ (Δ₂ , q₂) ])
--       → Δ₁ ⨾ q₁ ⊢ (Fᵍ X)
--       → (valᵍ X → Δ₂ ⨾ q₂ ⊢ A)
--       → Δ ⨾ q ⊢ A

--     _⋊ᵍ_ : ℂ → 𝒞 → 𝒞
--     store : ∀ {Δ Δ' q q' A} (p : ℂ)
--       → (Δ , q) ≡⋎ᵐ Vec.[ (Δ' , q' + p) ]
--       → Δ' ⨾ q' ⊢ A
--       → Δ ⨾ q ⊢ (p ⋊ᵍ A)
--     release : ∀ {Δ Δ₁ Δ₂ p q q₁ q₂ A B}
--       → (Δ , q) ≡⋎ᵐ ((Δ₁ , q₁) Vec.∷ Vec.[ (Δ₂ , q₂) ])
--       → Δ₁ ⨾ q₁ ⊢ (p ⋊ᵍ A)
--       → (A ∷ Δ₂) ⨾ p + q₂ ⊢ B
--       → Δ ⨾ q ⊢ B

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
