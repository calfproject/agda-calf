open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma

module Calf.GiralfMulti where

open import Calf.Value
open import Calf.Core.Cost
open import Calf.Computation
open import Calf.Computation.Product
open import Calf.Computation.Tensor
open import Calf.Computation.Lolli
open import Calf.Computation.Credit
open import Calf.Computation.Debit
open import Calf.Computation.CList1
open import Calf.Computation.CList2
open import Calf.Computation.Free
open import Calf.Computation.Power
open import Calf.Computation.Sum
open import Calf.Giralf using (_⊢_; _⋎₀; _⋎₂_)

open import Calf.Value.List
Context : Type₁
Context = List 𝒞 × ℂ

variable
  p p' p₁ p₂ q q' q₁ q₂ r r' : ℂ

import Cubical.Data.List as List
open import Calf.Computation.Tensor
Tensorfy : List 𝒞 → 𝒞
Tensorfy Δ = List.foldr _⊗_ ⊤ Δ


infix 1 _⊢ᵐ_
_⊢ᵐ_ : Context → 𝒞 → Type
Δ , q ⊢ᵐ A = ▷[ q ] (Tensorfy Δ) ⊸ A

idᴳ :
  q ⋎₀
  → [ A ] , q ⊢ᵐ A
idᴳ {q} {A} split = subst (_⊸ A) (sym ▷/0 ∙ cong₂ (▷[_]_) split (sym ⊗-identityʳ)) idᶜ


letᴳ :
  q ⋎₂ (q₁ , q₂)
  → A , q₁ ⊢ B
  → B , q₂ ⊢ C
  → A , q ⊢ C
letᴳ split e1 e2 =
  subst (_⊸ _) (sym ▷/+ ∙ cong (▷[_] _) (+ℂ-comm _ _ ∙ split)) ((▷-map e1) ⨾ᶜ e2)



module Perm-Split {E : Type₁} where
  data _≡_⊔_ : List E → List E → List E → Type₂ where
    base : [] ≡ [] ⊔ []
    left : {Δ Δ₁ Δ₂ : List E} {A : E} → Δ ≡ Δ₁ ⊔ Δ₂ → (A ∷ Δ) ≡ (A ∷ Δ₁) ⊔ Δ₂
    right : {Δ Δ₁ Δ₂ : List E} {A : E} → Δ ≡ Δ₁ ⊔ Δ₂ → (A ∷ Δ) ≡ Δ₁ ⊔ (A ∷ Δ₂)

  all-left : {Δ : List E} → Δ ≡ Δ ⊔ []
  all-left {[]} = base
  all-left {A ∷ Δ} = left (all-left {Δ})

  all-right : {Δ : List E} → Δ ≡ [] ⊔ Δ
  all-right {[]} = base
  all-right {A ∷ Δ} = right (all-right {Δ})

  switch : {Δ Δ₁ Δ₂ : List E} → Δ ≡ Δ₁ ⊔ Δ₂ → Δ ≡ Δ₂ ⊔ Δ₁
  switch base = base
  switch (left S) = right (switch S)
  switch (right S) = left (switch S)

open Perm-Split


variable
  Δ Δ₁ Δ₂ : List 𝒞

permute : Δ ≡ Δ₁ ⊔ Δ₂ → (Tensorfy Δ ⊸ (Tensorfy Δ₁ ⊗ Tensorfy Δ₂))
permute base = subst (⊤ ⊸_) (sym ⊗-identityʳ) idᶜ
permute (left {Δ'} {Δ₁'} {Δ₂'} {A} s) = subst (A ⊗ Tensorfy Δ' ⊸_) ⊗-assoc (map₂ idᶜ (permute s))
permute {Δ₁ = Δ₁} {Δ₂} (right {Δ'} {Δ₁'} {Δ₂'} {A} s) = subst (A ⊗ Tensorfy Δ' ⊸_) rearrange (map₂ idᶜ (permute s))
  where
    rearrange : (A ⊗ (Tensorfy Δ₁ ⊗ Tensorfy Δ₂')) ≡ (Tensorfy Δ₁ ⊗ Tensorfy (A ∷ Δ₂'))
    rearrange = ⊗-assoc ∙ cong (_⊗ (Tensorfy Δ₂')) ⊗-comm ∙ sym ⊗-assoc


cutᴳ :
  Δ ≡ Δ₁ ⊔ Δ₂
  → q ⋎₂ (q₁ , q₂)
  → Δ₁ , q₁ ⊢ᵐ A
  → A ∷ Δ₂ , q₂ ⊢ᵐ B
  → Δ , q ⊢ᵐ B
cutᴳ {Δ} {Δ₁} {Δ₂} {q} {q₁} {q₂} {A} {B} S s e₁ e₂ = (▷-map (permute S)) ⨾ᶜ (letᴳ s e₁' e₂)
  where
    e₁' : (Tensorfy Δ₁ ⊗ Tensorfy Δ₂) , q₁ ⊢ (A ⊗ Tensorfy Δ₂)
    e₁' = subst (_⊸ _) (▷A⊗B≡▷[A⊗B] q₁) (map₂ e₁ idᶜ)

cmpᴳ : 𝒞 → Type
cmpᴳ = ⊤ , 0ℂ ⊢_

cmpᴳ→cmp : cmpᴳ A → U A
cmpᴳ→cmp e = e .U (subst U (sym ▷/0) 0ℂ)

cmp→cmpᴳ : U A → cmpᴳ A
cmp→cmpᴳ {A} e =
  subst (_⊸ A) (sym ▷/0) $
  record { U = flip (A .charge) e ; charge = λ _ _ → A .charge/+ }

module _ where
  substᵐᴳ :
    q ≡ q'
    → Δ , q ⊢ᵐ A
    → Δ , q' ⊢ᵐ A
  substᵐᴳ qq = subst (_⊸ _) (cong (▷[_] _) qq)

  substᴳ :
    (A : ℂ → 𝒞)
    → p ≡ p'
    → Δ , q ⊢ᵐ A p
    → Δ , q ⊢ᵐ A p'
  substᴳ {Δ = Δ} {q = q} A = subst (λ p → Δ , q ⊢ᵐ A p)

  subst2ᴳ : ∀ {p1 p1' p2 p2'} →
    (A : ℂ → ℂ → 𝒞)
    → p1 ≡ p1' → p2 ≡ p2'
    → Δ , q ⊢ᵐ A p1 p2
    → Δ , q ⊢ᵐ A p1' p2'
  subst2ᴳ {Δ = Δ} {q = q} A = subst2 λ p1 p2 → Δ , q ⊢ᵐ A p1 p2

  subst3ᴳ : ∀ {p1 p1' p2 p2' p3 p3'} →
    (A : ℂ → ℂ → ℂ → 𝒞)
    → p1 ≡ p1' → p2 ≡ p2' → p3 ≡ p3'
    → Δ , q ⊢ᵐ A p1 p2 p3
    → Δ , q ⊢ᵐ A p1' p2' p3'
  subst3ᴳ {Δ = Δ} {q = q} {p1 = p1} {p2' = p2'} {p3' = p3'} A ≡1 ≡2 ≡3 e = substᴳ {Δ = Δ} {q = q} (λ v → A v p2' p3') ≡1 (subst2ᴳ {Δ = Δ} {q = q} (A p1) ≡2 ≡3 e)

module _ where
  storeᴳ : ∀ p
    → q ⋎₂ (p , q')
    → Δ , q' ⊢ᵐ A
    → Δ , q ⊢ᵐ ▷[ p ] A
  storeᴳ p split e = subst (_⊸ _) (sym ▷/+ ∙ cong (▷[_] _) split) (▷-map e)

  releaseᴳ :
    Δ ≡ Δ₁ ⊔ Δ₂
    → q ⋎₂ (q₁ , q₂)
    → Δ₁ , q₁ ⊢ᵐ ▷[ p ] B
    → B ∷ Δ₂ , (q₂ +ℂ p) ⊢ᵐ A
    → Δ , q ⊢ᵐ A
  releaseᴳ {Δ₂ = Δ₂} {q₂ = q₂} {p = p} {B = B} {A = A} S s e k = cutᴳ S s e k'
    where
      k' : (▷[ p ] B) ∷ Δ₂ , q₂ ⊢ᵐ A
      k' = subst (_⊸ _) (▷/+ ∙ cong (▷[ q₂ ]_) (sym (▷A⊗B≡▷[A⊗B] p))) k

spendᴳ : ∀ p
  → q ⋎₂ (p , q')
  → Δ , q' ⊢ᵐ A
  → Δ , q ⊢ᵐ A
spendᴳ {q = q} {A = A} p split e = letᴳ split (spend p) e


module _ where
  getᴳ : ∀ p
    → q' ⋎₂ (p , q)
    → Δ , q' ⊢ᵐ A
    → Δ , q ⊢ᵐ ◁[ p ] A
  getᴳ p split = transport (sym (▷⊣◁ ∙ cong (_⊸ _) (sym ▷/+ ∙ cong (▷[_] _) split)))

  payᴳ :
    q ⋎₂ (p , q')
    → Δ , q' ⊢ᵐ ◁[ p ] A
    → Δ , q ⊢ᵐ A
  payᴳ split = transport (▷⊣◁ ∙ cong (_⊸ _) (sym ▷/+ ∙ cong (▷[_] _) split))

module _ where
  nil₁ᴳ : cmpᴳ (CList₁ p X)
  nil₁ᴳ = cmp→cmpᴳ cnil₁

  cons₁ᴳ :
    q ⋎₂ (p , q')
    → X
    → Δ , q' ⊢ᵐ CList₁ p X
    → Δ , q ⊢ᵐ CList₁ p X
  cons₁ᴳ split x e = storeᴳ _ split e ⨾ᶜ ccons₁ x

  foldr₁ᴳ :
    cmpᴳ A
    → (X → [ A ] , p ⊢ᵐ A)
    → Δ , q ⊢ᵐ CList₁ p X
    → Δ , q ⊢ᵐ A
  foldr₁ᴳ e-nil e-cons e = {!   !}
  --  e ⨾ᶜ cfoldr₁ (cmpᴳ→cmp e-nil) e-cons

-- module _ where
--   nil₂ᴳ : q ⋎₀ → ⊤ , q ⊢ᵐ (CList₂ p₁ p₂ X)
--   nil₂ᴳ split = subst (λ x → ▷[ x ] _ ⊸ _) split (cmp→cmpᴳ cnil₂)

--   cons₂ᴳ :
--     q ⋎₂ (p₁ , q')
--     → X
--     → Δ , q' ⊢ᵐ CList₂ (p₂ +ℂ p₁) p₂ X
--     → Δ , q ⊢ᵐ CList₂ p₁ p₂ X
--   cons₂ᴳ split-q x e =
--     storeᴳ _ split-q e ⨾ᶜ ccons₂ x

--   foldr₂ᴳ :
--     (A : ℂ → 𝒞)
--     → (∀ r → cmpᴳ (A r))
--     → (∀ r → X → A (p₂ +ℂ r) , r ⊢ᵐ A r)
--     → Δ , q ⊢ᵐ CList₂ p₁ p₂ X
--     → Δ , q ⊢ᵐ A p₁
--   foldr₂ᴳ A e-nil e-cons e = e ⨾ᶜ cfoldr₂ A (cmpᴳ→cmp ∘ e-nil) e-cons

module _ where
  pairᴳ :
      Δ , q ⊢ᵐ A
    → Δ , q ⊢ᵐ B
    → Δ , q ⊢ᵐ A ×ᶜ B
  pairᴳ = pairᶜ

  proj₁ᴳ :
      Δ , q ⊢ᵐ A ×ᶜ B
    → Δ , q ⊢ᵐ A
  proj₁ᴳ {B = B} = _⨾ᶜ proj₁ᶜ {B = B}

  proj₂ᴳ :
      Δ , q ⊢ᵐ A ×ᶜ B
    → Δ , q ⊢ᵐ B
  proj₂ᴳ {A = A} = _⨾ᶜ proj₂ᶜ {A = A}

module _ where
  powlamᴳ :
    (X → Δ , q ⊢ᵐ A)
    → Δ , q ⊢ᵐ X ⇀ A
  powlamᴳ {X = X} = powlam {X = X}

  powappᴳ :
    X → Δ , q ⊢ᵐ X ⇀ A
    → Δ , q ⊢ᵐ A
  powappᴳ {X = X} x e = powapp {X = X} e x

module _ where
  inj₁ᴳ :
      Δ , q ⊢ᵐ A
    → Δ , q ⊢ᵐ A +ᶜ B
  inj₁ᴳ {B = B} = _⨾ᶜ inj₁ᶜ {B = B}

  inj₂ᴳ :
      Δ , q ⊢ᵐ B
    → Δ , q ⊢ᵐ A +ᶜ B
  inj₂ᴳ {A = A} = _⨾ᶜ inj₂ᶜ {A = A}

  caseᴳ : Δ ≡ Δ₁ ⊔ Δ₂
    → q ⋎₂ (q₁ , q₂)
    → Δ₁ , q₁ ⊢ᵐ A +ᶜ B
    → A ∷ Δ₂ , q₂ ⊢ᵐ C
    → B ∷ Δ₂ , q₂ ⊢ᵐ C
    → Δ , q ⊢ᵐ C
  caseᴳ {Δ₂ = Δ₂} {q₂ = q₂} {A = A} {B} {C} S s e e₁ e₂ = cutᴳ S s e k'
    where
      k' : (A +ᶜ B) ∷ Δ₂ , q₂ ⊢ᵐ C
      k' = subst (_⊸ _) (▷A+▷B≡▷[A+B] q₂ ∙ cong (▷[ q₂ ]_) A⊗C+B⊗C≡[A+B]⊗C) (caseᶜ e₁ e₂)

module _ where
  tensorᴳ : Δ ≡ Δ₁ ⊔ Δ₂
    → q ⋎₂ (q₁ , q₂)
    → Δ₁ , q₁ ⊢ᵐ A
    → Δ₂ , q₂ ⊢ᵐ B
    → Δ , q ⊢ᵐ A ⊗ B
  tensorᴳ {q₂ = q₂} S s e₁ e₂ = cutᴳ S s e₁ (subst (_⊸ _) (A⊗▷B≡▷[A⊗B] q₂) (map₂ idᶜ e₂))

  splitᴳ : Δ ≡ Δ₁ ⊔ Δ₂
    → q ⋎₂ (q₁ , q₂)
    → Δ₁ , q₁ ⊢ᵐ A ⊗ B
    → A ∷ B ∷ Δ₂ , q₂ ⊢ᵐ C
    → Δ , q ⊢ᵐ C
  splitᴳ {q₂ = q₂} S s e k = cutᴳ S s e (subst (_⊸ _) (cong (▷[ q₂ ]_) ⊗-assoc) k)
