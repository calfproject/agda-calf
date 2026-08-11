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
open import Calf.Computation.CList
open import Calf.Computation.CList1
open import Calf.Computation.CList2
open import Calf.Computation.Free
open import Calf.Computation.Power
open import Calf.Computation.Sum
open import Calf.Computation.Tensor

open import Calf.Value.List
Context : Type₁
Context = List 𝒞 × ℂ

module _ where
  _⋎₀ : ℂ → Type
  q ⋎₀ = 0ℂ ≡ q

  _⋎₂_ : ℂ → (ℂ × ℂ) → Type
  q ⋎₂ (q₁ , q₂) = q₁ +ℂ q₂ ≡ q

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
  p p' p₁ p₂ q q' q₁ q₂ r r' : ℂ

variable
  Δ Δ₁ Δ₂ : List 𝒞

record Giralf : Set₂ where
  infix 1 _⨾_⊢_
  field
    _⨾_⊢_ : List 𝒞 → ℂ → 𝒞 → Set

    spendᴳ : ∀ p
      → q ⋎₂ (p , q')
      → Δ ⨾ q' ⊢ A
      → Δ ⨾ q ⊢ A
    idᴳ : ∀ {q : ℂ} {A : 𝒞} → q ⋎₀ → [ A ] ⨾ q ⊢ A
    cutᴳ : Δ ≡ Δ₁ ⊔ Δ₂
      → q ⋎₂ (q₁ , q₂)
      → Δ₁ ⨾ q₁ ⊢ A
      → A ∷ Δ₂ ⨾ q₂ ⊢ B
      → Δ ⨾ q ⊢ B

    substᵐᴳ :
      q ≡ q'
      → Δ ⨾ q ⊢ A
      → Δ ⨾ q' ⊢ A
    substᴳ :
      (A : ℂ → 𝒞)
      → p ≡ p'
      → Δ ⨾ q ⊢ A p
      → Δ ⨾ q ⊢ A p'
    subst2ᴳ : ∀ {p1 p1' p2 p2'} →
      (A : ℂ → ℂ → 𝒞)
      → p1 ≡ p1' → p2 ≡ p2'
      → Δ ⨾ q ⊢ A p1 p2
      → Δ ⨾ q ⊢ A p1' p2'
    subst3ᴳ : ∀ {p1 p1' p2 p2' p3 p3'} →
      (A : ℂ → ℂ → ℂ → 𝒞)
      → p1 ≡ p1' → p2 ≡ p2' → p3 ≡ p3'
      → Δ ⨾ q ⊢ A p1 p2 p3
      → Δ ⨾ q ⊢ A p1' p2' p3'

    storeᴳ : ∀ p
      → q ⋎₂ (p , q')
      → Δ ⨾ q' ⊢ A
      → Δ ⨾ q ⊢ ▷[ p ] A
    releaseᴳ :
      Δ ≡ Δ₁ ⊔ Δ₂
      → q ⋎₂ (q₁ , q₂)
      → Δ₁ ⨾ q₁ ⊢ ▷[ p ] B
      → B ∷ Δ₂ ⨾ (q₂ +ℂ p) ⊢ A
      → Δ ⨾ q ⊢ A

    getᴳ : ∀ p
      → q' ⋎₂ (p , q)
      → Δ ⨾ q' ⊢ A
      → Δ ⨾ q ⊢ ◁[ p ] A
    payᴳ :
      q ⋎₂ (p , q')
      → Δ ⨾ q' ⊢ ◁[ p ] A
      → Δ ⨾ q ⊢ A

    pairᴳ :
        Δ ⨾ q ⊢ A
      → Δ ⨾ q ⊢ B
      → Δ ⨾ q ⊢ A ×ᶜ B
    proj₁ᴳ :
        Δ ⨾ q ⊢ A ×ᶜ B
      → Δ ⨾ q ⊢ A
    proj₂ᴳ :
        Δ ⨾ q ⊢ A ×ᶜ B
      → Δ ⨾ q ⊢ B

    powlamᴳ :
      (X → Δ ⨾ q ⊢ A)
      → Δ ⨾ q ⊢ X ⇀ A
    powappᴳ :
      X → Δ ⨾ q ⊢ X ⇀ A
      → Δ ⨾ q ⊢ A

    absurdᴳ :
        Δ ⨾ q ⊢ 0ᶜ
      → Δ ⨾ q ⊢ C

    inj₁ᴳ :
        Δ ⨾ q ⊢ A
      → Δ ⨾ q ⊢ A +ᶜ B
    inj₂ᴳ :
        Δ ⨾ q ⊢ B
      → Δ ⨾ q ⊢ A +ᶜ B
    caseᴳ : Δ ≡ Δ₁ ⊔ Δ₂
      → q ⋎₂ (q₁ , q₂)
      → Δ₁ ⨾ q₁ ⊢ A +ᶜ B
      → A ∷ Δ₂ ⨾ q₂ ⊢ C
      → B ∷ Δ₂ ⨾ q₂ ⊢ C
      → Δ ⨾ q ⊢ C

  cmpᴳ : 𝒞 → Type
  cmpᴳ = [] ⨾ 0ℂ ⊢_

  field
    trivᴳ : cmpᴳ ⊤
    checkᴳ : Δ ≡ Δ₁ ⊔ Δ₂
      → q ⋎₂ (q₁ , q₂)
      → Δ₁ ⨾ q₁ ⊢ ⊤
      → Δ₂ ⨾ q₂ ⊢ C
      → Δ ⨾ q ⊢ C

    tensorᴳ : Δ ≡ Δ₁ ⊔ Δ₂
      → q ⋎₂ (q₁ , q₂)
      → Δ₁ ⨾ q₁ ⊢ A
      → Δ₂ ⨾ q₂ ⊢ B
      → Δ ⨾ q ⊢ A ⊗ B
    splitᴳ : Δ ≡ Δ₁ ⊔ Δ₂
      → q ⋎₂ (q₁ , q₂)
      → Δ₁ ⨾ q₁ ⊢ A ⊗ B
      → A ∷ B ∷ Δ₂ ⨾ q₂ ⊢ C
      → Δ ⨾ q ⊢ C

    nilᴳ : cmpᴳ (CList A)
    consᴳ :
      Δ ≡ Δ₁ ⊔ Δ₂
      → q ⋎₂ (q₁ , q₂)
      → Δ₁ ⨾ q₁ ⊢ A
      → Δ₂ ⨾ q₂ ⊢ CList A
      → Δ ⨾ q ⊢ CList A
    foldrᴳ :
      cmpᴳ B
      → (A ∷ [ B ] ⨾ 0ℂ ⊢ B)
      → Δ ⨾ q ⊢ CList A
      → Δ ⨾ q ⊢ B

    nil₁ᴳ : cmpᴳ (CList₁ p A)
    cons₁ᴳ :
      Δ ≡ Δ₁ ⊔ Δ₂
      → q ⋎₂ (p , (q₁ +ℂ q₂))
      → Δ₁ ⨾ q₁ ⊢ A
      → Δ₂ ⨾ q₂ ⊢ CList₁ p A
      → Δ ⨾ q ⊢ CList₁ p A
    foldr₁ᴳ :
      cmpᴳ B
      → (A ∷ [ B ] ⨾ p ⊢ B)
      → Δ ⨾ q ⊢ CList₁ p A
      → Δ ⨾ q ⊢ B

    nil₂ᴳ : q ⋎₀ → [] ⨾ q ⊢ (CList₂ p₁ p₂ A)
    cons₂ᴳ :
      Δ ≡ Δ₁ ⊔ Δ₂
      → q ⋎₂ (p₁ , (q₁ +ℂ q₂))
      → Δ₁ ⨾ q₁ ⊢ A
      → Δ₂ ⨾ q₂ ⊢ CList₂ (p₂ +ℂ p₁) p₂ A
      → Δ ⨾ q ⊢ CList₂ p₁ p₂ A
    foldr₂ᴳ :
      (B : ℂ → 𝒞)
      → (∀ r → cmpᴳ (B r))
      → (∀ r → A ∷ [ B (p₂ +ℂ r) ] ⨾ r ⊢ B r)
      → Δ ⨾ q ⊢ CList₂ p₁ p₂ A
      → Δ ⨾ q ⊢ B p₁


import Cubical.Data.List as List
Tensorfy : List 𝒞 → 𝒞
Tensorfy Δ = List.foldr _⊗_ ⊤ Δ

-- standard interpretation of Giralf judgment into Calf
infix 1 _⨾_⊢ˢ_
_⨾_⊢ˢ_ : List 𝒞 → ℂ → 𝒞 → Set
Δ ⨾ q ⊢ˢ A = ▷[ q ] (Tensorfy Δ) ⊸ A

cmpᴳ→U : ([] ⨾ 0ℂ ⊢ˢ A) → U A
cmpᴳ→U {A} e = cmp→U (subst (_⊸ A) ▷/0 e)

U→cmpᴳ : U A → ([] ⨾ 0ℂ ⊢ˢ A)
U→cmpᴳ {A} e = subst (_⊸ A) (sym ▷/0) (U→cmp e)

-- composition with credit splitting
_⋎_⨾ᴳ_ :
  q ⋎₂ (q₁ , q₂)
  → ▷[ q₁ ] A ⊸ B
  → ▷[ q₂ ] B ⊸ C
  → ▷[ q ] A ⊸ C
s ⋎ e₁ ⨾ᴳ e₂ = subst (_⊸ _) (sym ▷/+ ∙ cong (▷[_] _) (+ℂ-comm _ _ ∙ s)) ((▷-map e₁) ⨾ᶜ e₂)

-- composition with credit AND context splitting (cut)
_∣_⋎_⨾ᴳ_ :
  Δ ≡ Δ₁ ⊔ Δ₂
  → q ⋎₂ (q₁ , q₂)
  → Δ₁ ⨾ q₁ ⊢ˢ A
  → A ∷ Δ₂ ⨾ q₂ ⊢ˢ B
  → Δ ⨾ q ⊢ˢ B
_∣_⋎_⨾ᴳ_ {Δ} {Δ₁} {Δ₂} {q} {q₁} {q₂} {A} {B} S s e₁ e₂ = (▷-map (permute S)) ⨾ᶜ (s ⋎ e₁' ⨾ᴳ e₂)
  where
    e₁' : ▷[ q₁ ] (Tensorfy Δ₁ ⊗ Tensorfy Δ₂) ⊸ (A ⊗ Tensorfy Δ₂)
    e₁' = subst (_⊸ _) (▷A⊗B≡▷[A⊗B] q₁) (map₂ e₁ idᶜ)

    permute : ∀ {Δ Δ₁ Δ₂} → Δ ≡ Δ₁ ⊔ Δ₂ → (Tensorfy Δ ⊸ (Tensorfy Δ₁ ⊗ Tensorfy Δ₂))
    permute base = subst (⊤ ⊸_) (sym ⊗-identityʳ) idᶜ
    permute (left {Δ'} {Δ₁'} {Δ₂'} {A} s) = subst (A ⊗ Tensorfy Δ' ⊸_) ⊗-assoc (map₂ idᶜ (permute s))
    permute {Δ₁ = Δ₁} {Δ₂} (right {Δ'} {Δ₁'} {Δ₂'} {A} s) = subst (A ⊗ Tensorfy Δ' ⊸_) rearrange (map₂ idᶜ (permute s))
      where
        rearrange : (A ⊗ (Tensorfy Δ₁ ⊗ Tensorfy Δ₂')) ≡ (Tensorfy Δ₁ ⊗ Tensorfy (A ∷ Δ₂'))
        rearrange = ⊗-assoc ∙ cong (_⊗ (Tensorfy Δ₂')) ⊗-comm ∙ sym ⊗-assoc


open Giralf

-- implementation of standard Giralf semantics
std : Giralf
std ._⨾_⊢_ = _⨾_⊢ˢ_
std .spendᴳ {q = q} {Δ = Δ} {A = A} p split e = split ⋎ spend (Tensorfy Δ) p ⨾ᴳ e

std .idᴳ {q} {A} split = subst (_⊸ A) (sym ▷/0 ∙ cong₂ (▷[_]_) split (sym ⊗-identityʳ)) idᶜ
std .cutᴳ = _∣_⋎_⨾ᴳ_

std .substᵐᴳ {A = A} qq = subst (_⊸ A) (cong (▷[_] _) qq)
std .substᴳ {Δ = Δ} {q = q} A = subst (λ p → Δ ⨾ q ⊢ˢ A p)
std .subst2ᴳ {Δ = Δ} {q = q} A =  subst2 (λ p1 p2 → Δ ⨾ q ⊢ˢ A p1 p2)
std .subst3ᴳ {Δ = Δ} {q = q} {p1 = p1} {p2' = p2'} {p3' = p3'} A ≡1 ≡2 ≡3 e =
  std .substᴳ {Δ = Δ} {q = q} (λ v → A v p2' p3') ≡1 $
  std .subst2ᴳ {Δ = Δ} {q = q} (A p1) ≡2 ≡3 e

std .storeᴳ {A = A} p split e = subst (_⊸ ▷[ p ] A) (sym ▷/+ ∙ cong (▷[_] _) split) (▷-map e)
std .releaseᴳ {Δ₂ = Δ₂} {q₂ = q₂} {p = p} {B = B} {A = A} S s e k = S ∣ s ⋎ e ⨾ᴳ k'
  where
    k' : (▷[ p ] B) ∷ Δ₂ ⨾ q₂ ⊢ˢ A
    k' = subst (_⊸ _) (▷/+ ∙ cong (▷[ q₂ ]_) (sym (▷A⊗B≡▷[A⊗B] p))) k

std .getᴳ {A = A} p split = transport (sym (▷⊣◁ ∙ cong (_⊸ A) (sym ▷/+ ∙ cong (▷[_] _) split)))
std .payᴳ {A = A} split = transport (▷⊣◁ ∙ cong (_⊸ A) (sym ▷/+ ∙ cong (▷[_] _) split))

std .pairᴳ = pairᶜ
std .proj₁ᴳ {B = B} = _⨾ᶜ proj₁ᶜ {B = B}
std .proj₂ᴳ {A = A} = _⨾ᶜ proj₂ᶜ {A = A}

std .powlamᴳ {X = X} = powlam {X = X}
std .powappᴳ {X = X} x e = powapp {X = X} e x

std .absurdᴳ = _⨾ᶜ absurdᶜ
std .inj₁ᴳ {B = B} = _⨾ᶜ inj₁ᶜ {B = B}
std .inj₂ᴳ {A = A} = _⨾ᶜ inj₂ᶜ {A = A}
std .caseᴳ {Δ₂ = Δ₂} {q₂ = q₂} {A = A} {B} {C} S s e e₁ e₂ = S ∣ s ⋎ e ⨾ᴳ k'
  where
    k' : (A +ᶜ B) ∷ Δ₂ ⨾ q₂ ⊢ˢ C
    k' = subst (_⊸ _) (▷A+▷B≡▷[A+B] q₂ ∙ cong (▷[ q₂ ]_) A⊗C+B⊗C≡[A+B]⊗C) (caseᶜ e₁ e₂)

std .trivᴳ = U→cmpᴳ trivᶜ
std .checkᴳ S s e k = S ∣ s ⋎ e ⨾ᴳ (subst (λ a → ▷[ _ ] a ⊸ _) (sym ⊗-identityˡ) k)
std .tensorᴳ {q₂ = q₂} S s e₁ e₂ = S ∣ s ⋎ e₁ ⨾ᴳ (subst (_⊸ _) (A⊗▷B≡▷[A⊗B] q₂) (map₂ idᶜ e₂))
std .splitᴳ {q₂ = q₂} {C = C} S s e k = S ∣ s ⋎ e ⨾ᴳ (subst (λ a → ▷[ q₂ ] a ⊸ C) ⊗-assoc k)

std .nilᴳ = U→cmpᴳ cnil
std .consᴳ S s eₕ eₜ = std .tensorᴳ S s eₕ eₜ ⨾ᶜ ccons
std .foldrᴳ e[] e∷ = _⨾ᶜ cfoldr (cmpᴳ→U e[]) (subst (_⊸ _) (▷/0 ∙ cong (_ ⊗_) ⊗-identityʳ) e∷)

std .nil₁ᴳ = U→cmpᴳ cnil₁
std .cons₁ᴳ {Δ = Δ} {p = p} S s eₕ eₜ =
  std .storeᴳ {Δ = Δ} p s (std .tensorᴳ S refl eₕ eₜ) ⨾ᶜ ccons₁
std .foldr₁ᴳ {B = B} {p = p} e[] e∷ =
  _⨾ᶜ cfoldr₁ (cmpᴳ→U e[]) (subst (λ C →  ▷[ p ] (_ ⊗ C) ⊸ B) ⊗-identityʳ e∷)

std .nil₂ᴳ split = subst (λ x → ▷[ x ] _ ⊸ _) split (U→cmpᴳ cnil₂)
std .cons₂ᴳ {Δ = Δ} {p₁ = p₁} S s eₕ eₜ =
  std .storeᴳ {Δ = Δ} p₁ s (std .tensorᴳ S refl eₕ eₜ) ⨾ᶜ ccons₂
std .foldr₂ᴳ B e[] e∷ =
  _⨾ᶜ cfoldr₂ B (cmpᴳ→U ∘ e[]) (λ c-lin' → subst (λ C →  ▷[ c-lin' ] (_ ⊗ C) ⊸ _) ⊗-identityʳ (e∷ c-lin'))


-- alternative interpretation of Giralf into Calf, dropping all potential
infix 1 _⨾_⊢ᶜ_
_⨾_⊢ᶜ_ : List 𝒞 → ℂ → 𝒞 → Set
Δ ⨾ q ⊢ᶜ A = Tensorfy Δ ⊸ A

-- TODO
-- alt : Giralf
-- alt ._⨾_⊢_ = _⨾_⊢ᶜ_
