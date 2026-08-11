open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma

module Calf.Giralf where

open import Calf.Value
open import Calf.Core.Cost
open import Calf.Computation
open import Calf.Computation.Product
open import Calf.Computation.Tensor
open import Calf.Computation.Lolli
open import Calf.Computation.Credit
open import Calf.Computation.Debit
open import Calf.Computation.List as Listᶜ
open import Calf.Computation.CList1
open import Calf.Computation.CList2
open import Calf.Computation.Free
open import Calf.Computation.Power
open import Calf.Computation.Sum

open import Calf.Value.List
Context : Type₁
Context = List 𝒞 × ℂ

module _ where
  _⋎₀ : ℂ → Type
  q ⋎₀ = 0ℂ ≡ q

  _⋎₂_ : ℂ → (ℂ × ℂ) → Type
  q ⋎₂ (q₁ , q₂) = q₁ +ℂ q₂ ≡ q

variable
  p p' p₁ p₂ q q' q₁ q₂ r r' : ℂ

import Cubical.Data.List as List
open import Calf.Computation.Tensor
Tensorfy : List 𝒞 → 𝒞
Tensorfy Δ = List.foldr _⊗_ ⊤ Δ


infix 1 _⊢_
_⊢_ : Context → 𝒞 → Type
Δ , q ⊢ A = ▷[ q ] (Tensorfy Δ) ⊸ A

idᴳ :
  q ⋎₀
  → [ A ] , q ⊢ A
idᴳ {q} {A} split = subst (_⊸ A) (sym ▷/0 ∙ cong₂ (▷[_]_) split (sym ⊗-identityʳ)) idᶜ


letᴳ :
  q ⋎₂ (q₁ , q₂)
  → ▷[ q₁ ] A ⊸ B
  → ▷[ q₂ ] B ⊸ C
  → ▷[ q ] A ⊸ C
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
  → Δ₁ , q₁ ⊢ A
  → A ∷ Δ₂ , q₂ ⊢ B
  → Δ , q ⊢ B
cutᴳ {Δ} {Δ₁} {Δ₂} {q} {q₁} {q₂} {A} {B} S s e₁ e₂ = (▷-map (permute S)) ⨾ᶜ (letᴳ s e₁' e₂)
  where
    e₁' : ▷[ q₁ ] (Tensorfy Δ₁ ⊗ Tensorfy Δ₂) ⊸ (A ⊗ Tensorfy Δ₂)
    e₁' = subst (_⊸ _) (▷A⊗B≡▷[A⊗B] q₁) (map₂ e₁ idᶜ)

cmpᴳ : 𝒞 → Type
cmpᴳ = [] , 0ℂ ⊢_

cmpᴳ→U : cmpᴳ A → U A
cmpᴳ→U {A} e = cmp→U (subst (_⊸ A) ▷/0 e)

U→cmpᴳ : U A → cmpᴳ A
U→cmpᴳ {A} e = subst (_⊸ A) (sym ▷/0) (U→cmp e)

module _ where
  substᵐᴳ :
    q ≡ q'
    → Δ , q ⊢ A
    → Δ , q' ⊢ A
  substᵐᴳ {A = A} qq = subst (_⊸ A) (cong (▷[_] _) qq)

  substᴳ :
    (A : ℂ → 𝒞)
    → p ≡ p'
    → Δ , q ⊢ A p
    → Δ , q ⊢ A p'
  substᴳ {Δ = Δ} {q = q} A = subst (λ p → Δ , q ⊢ A p)

  subst2ᴳ : ∀ {p1 p1' p2 p2'} →
    (A : ℂ → ℂ → 𝒞)
    → p1 ≡ p1' → p2 ≡ p2'
    → Δ , q ⊢ A p1 p2
    → Δ , q ⊢ A p1' p2'
  subst2ᴳ {Δ = Δ} {q = q} A = subst2 λ p1 p2 → Δ , q ⊢ A p1 p2

  subst3ᴳ : ∀ {p1 p1' p2 p2' p3 p3'} →
    (A : ℂ → ℂ → ℂ → 𝒞)
    → p1 ≡ p1' → p2 ≡ p2' → p3 ≡ p3'
    → Δ , q ⊢ A p1 p2 p3
    → Δ , q ⊢ A p1' p2' p3'
  subst3ᴳ {Δ = Δ} {q = q} {p1 = p1} {p2' = p2'} {p3' = p3'} A ≡1 ≡2 ≡3 e = substᴳ {Δ = Δ} {q = q} (λ v → A v p2' p3') ≡1 (subst2ᴳ {Δ = Δ} {q = q} (A p1) ≡2 ≡3 e)

module _ where
  storeᴳ : ∀ p
    → q ⋎₂ (p , q')
    → Δ , q' ⊢ A
    → Δ , q ⊢ ▷[ p ] A
  storeᴳ {A = A} p split e = subst (_⊸ ▷[ p ] A) (sym ▷/+ ∙ cong (▷[_] _) split) (▷-map e)

  releaseᴳ :
    Δ ≡ Δ₁ ⊔ Δ₂
    → q ⋎₂ (q₁ , q₂)
    → Δ₁ , q₁ ⊢ ▷[ p ] B
    → B ∷ Δ₂ , (q₂ +ℂ p) ⊢ A
    → Δ , q ⊢ A
  releaseᴳ {Δ₂ = Δ₂} {q₂ = q₂} {p = p} {B = B} {A = A} S s e k = cutᴳ S s e k'
    where
      k' : (▷[ p ] B) ∷ Δ₂ , q₂ ⊢ A
      k' = subst (_⊸ _) (▷/+ ∙ cong (▷[ q₂ ]_) (sym (▷A⊗B≡▷[A⊗B] p))) k

spendᴳ : ∀ p
  → q ⋎₂ (p , q')
  → Δ , q' ⊢ A
  → Δ , q ⊢ A
spendᴳ {q = q} {Δ = Δ} {A = A} p split e = letᴳ split (spend (Tensorfy Δ) p) e


module _ where
  getᴳ : ∀ p
    → q' ⋎₂ (p , q)
    → Δ , q' ⊢ A
    → Δ , q ⊢ ◁[ p ] A
  getᴳ {A = A} p split = transport (sym (▷⊣◁ ∙ cong (_⊸ A) (sym ▷/+ ∙ cong (▷[_] _) split)))

  payᴳ :
    q ⋎₂ (p , q')
    → Δ , q' ⊢ ◁[ p ] A
    → Δ , q ⊢ A
  payᴳ {A = A} split = transport (▷⊣◁ ∙ cong (_⊸ A) (sym ▷/+ ∙ cong (▷[_] _) split))

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

module _ where
  powlamᴳ :
    (X → Δ , q ⊢ A)
    → Δ , q ⊢ X ⇀ A
  powlamᴳ {X = X} = powlam {X = X}

  powappᴳ :
    X → Δ , q ⊢ X ⇀ A
    → Δ , q ⊢ A
  powappᴳ {X = X} x e = powapp {X = X} e x

module _ where
  absurdᴳ :
      Δ , q ⊢ 0ᶜ
    → Δ , q ⊢ C
  absurdᴳ = _⨾ᶜ absurdᶜ

  inj₁ᴳ :
      Δ , q ⊢ A
    → Δ , q ⊢ A +ᶜ B
  inj₁ᴳ {B = B} = _⨾ᶜ inj₁ᶜ {B = B}

  inj₂ᴳ :
      Δ , q ⊢ B
    → Δ , q ⊢ A +ᶜ B
  inj₂ᴳ {A = A} = _⨾ᶜ inj₂ᶜ {A = A}

  caseᴳ : Δ ≡ Δ₁ ⊔ Δ₂
    → q ⋎₂ (q₁ , q₂)
    → Δ₁ , q₁ ⊢ A +ᶜ B
    → A ∷ Δ₂ , q₂ ⊢ C
    → B ∷ Δ₂ , q₂ ⊢ C
    → Δ , q ⊢ C
  caseᴳ {Δ₂ = Δ₂} {q₂ = q₂} {A = A} {B} {C} S s e e₁ e₂ = cutᴳ S s e k'
    where
      k' : (A +ᶜ B) ∷ Δ₂ , q₂ ⊢ C
      k' = subst (_⊸ _) (▷A+▷B≡▷[A+B] q₂ ∙ cong (▷[ q₂ ]_) A⊗C+B⊗C≡[A+B]⊗C) (caseᶜ e₁ e₂)

module _ where
  trivᴳ : cmpᴳ ⊤
  trivᴳ = U→cmpᴳ trivᶜ

  checkᴳ : Δ ≡ Δ₁ ⊔ Δ₂
    → q ⋎₂ (q₁ , q₂)
    → Δ₁ , q₁ ⊢ ⊤
    → Δ₂ , q₂ ⊢ C
    → Δ , q ⊢ C
  checkᴳ S s e k = cutᴳ S s e (subst (λ a → ▷[ _ ] a ⊸ _) (sym ⊗-identityˡ) k)

  tensorᴳ : Δ ≡ Δ₁ ⊔ Δ₂
    → q ⋎₂ (q₁ , q₂)
    → Δ₁ , q₁ ⊢ A
    → Δ₂ , q₂ ⊢ B
    → Δ , q ⊢ A ⊗ B
  tensorᴳ {q₂ = q₂} S s e₁ e₂ = cutᴳ S s e₁ (subst (_⊸ _) (A⊗▷B≡▷[A⊗B] q₂) (map₂ idᶜ e₂))

  splitᴳ : Δ ≡ Δ₁ ⊔ Δ₂
    → q ⋎₂ (q₁ , q₂)
    → Δ₁ , q₁ ⊢ A ⊗ B
    → A ∷ B ∷ Δ₂ , q₂ ⊢ C
    → Δ , q ⊢ C
  splitᴳ {q₂ = q₂} {C = C} S s e k = cutᴳ S s e (subst (λ a → ▷[ q₂ ] a ⊸ C) ⊗-assoc k)

module _ where
  nilᴳ : cmpᴳ (Listᶜ A)
  nilᴳ = U→cmpᴳ nil

  consᴳ :
    Δ ≡ Δ₁ ⊔ Δ₂
    → q ⋎₂ (q₁ , q₂)
    → Δ₁ , q₁ ⊢ A
    → Δ₂ , q₂ ⊢ Listᶜ A
    → Δ , q ⊢ Listᶜ A
  consᴳ S s eₕ eₜ = tensorᴳ S s eₕ eₜ ⨾ᶜ cons

  foldrᴳ :
    cmpᴳ B
    → (A ∷ [ B ] , 0ℂ ⊢ B)
    → Δ , q ⊢ Listᶜ A
    → Δ , q ⊢ B
  foldrᴳ e[] e∷ = _⨾ᶜ Listᶜ.foldr (cmpᴳ→U e[]) (subst (_⊸ _) (▷/0 ∙ cong (_ ⊗_) ⊗-identityʳ) e∷)

module _ where
  nil₁ᴳ : cmpᴳ (CList₁ p A)
  nil₁ᴳ = U→cmpᴳ cnil₁

  cons₁ᴳ :
    Δ ≡ Δ₁ ⊔ Δ₂
    → q ⋎₂ (p , (q₁ +ℂ q₂))
    → Δ₁ , q₁ ⊢ A
    → Δ₂ , q₂ ⊢ CList₁ p A
    → Δ , q ⊢ CList₁ p A
  cons₁ᴳ {Δ = Δ} {p = p} S s eₕ eₜ = storeᴳ {Δ = Δ} p s (tensorᴳ S refl eₕ eₜ) ⨾ᶜ ccons₁

  foldr₁ᴳ :
    cmpᴳ B
    → (A ∷ [ B ] , p ⊢ B)
    → Δ , q ⊢ CList₁ p A
    → Δ , q ⊢ B
  foldr₁ᴳ {B = B} {p = p} e[] e∷ =
    _⨾ᶜ cfoldr₁ (cmpᴳ→U e[]) (subst (λ C →  ▷[ p ] (_ ⊗ C) ⊸ B) ⊗-identityʳ e∷)

module _ where
  nil₂ᴳ : q ⋎₀ → [] , q ⊢ (CList₂ p₁ p₂ A)
  nil₂ᴳ split = subst (λ x → ▷[ x ] _ ⊸ _) split (U→cmpᴳ cnil₂)

  cons₂ᴳ :
    Δ ≡ Δ₁ ⊔ Δ₂
    → q ⋎₂ (p₁ , (q₁ +ℂ q₂))
    → Δ₁ , q₁ ⊢ A
    → Δ₂ , q₂ ⊢ CList₂ (p₂ +ℂ p₁) p₂ A
    → Δ , q ⊢ CList₂ p₁ p₂ A
  cons₂ᴳ {Δ = Δ} {p₁ = p₁} S s eₕ eₜ = storeᴳ {Δ = Δ} p₁ s (tensorᴳ S refl eₕ eₜ) ⨾ᶜ ccons₂

  foldr₂ᴳ :
    (B : ℂ → 𝒞)
    → (∀ r → cmpᴳ (B r))
    → (∀ r → A ∷ [ B (p₂ +ℂ r) ] , r ⊢ B r)
    → Δ , q ⊢ CList₂ p₁ p₂ A
    → Δ , q ⊢ B p₁
  foldr₂ᴳ B e[] e∷ =
    _⨾ᶜ cfoldr₂ B (cmpᴳ→U ∘ e[]) (λ c-lin' → subst (λ C →  ▷[ c-lin' ] (_ ⊗ C) ⊸ _) ⊗-identityʳ (e∷ c-lin'))
