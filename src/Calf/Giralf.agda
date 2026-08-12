open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma

module Calf.Giralf where

open import Calf.Value
open import Calf.Value.List
open import Calf.Core.Cost
open import Calf.Computation
open import Calf.Computation.Product
open import Calf.Computation.Lolli
open import Calf.Computation.Credit
open import Calf.Computation.Debit
open import Calf.Computation.List as Listᶜ
open import Calf.Computation.CList1
open import Calf.Computation.CList2
open import Calf.Computation.Free
open import Calf.Computation.Power
open import Calf.Computation.Sum
open import Calf.Computation.Tensor
open import Calf.Computation.CreditInterface

module _ where
  _⋎₀ : ℂ → 𝒱
  q ⋎₀ = 0ℂ ≡ q

  _⋎₂_ : ℂ → (ℂ × ℂ) → 𝒱
  q ⋎₂ (q₁ , q₂) = q₁ +ℂ q₂ ≡ q

module Perm-Split {E : 𝒱₁} where
  data _≡_⊔_ : List E → List E → List E → 𝒱₂ where
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

import Cubical.Data.List as List
Tensorfy : List 𝒞 → 𝒞
Tensorfy Δ = List.foldr _⊗_ ⊤ Δ

variable
  p p' p₁ p₂ q q' q₁ q₂ r r' : ℂ

variable
  Δ Δ₁ Δ₂ Δ' : List 𝒞

record Giralf : 𝒱₂ where
  infix 1 _⨾_⊢_
  field
    _⨾_⊢_ : List 𝒞 → ℂ → 𝒞 → Set
    ▷ᴳ[_]_ : ℂ → 𝒞 → 𝒞
    ◁ᴳ[_]_ : ℂ → 𝒞 → 𝒞
    CList₁ᴳ : ℂ → 𝒞 → 𝒞
    CList₂ᴳ : ℂ → ℂ → 𝒞 → 𝒞

  cmpᴳ : 𝒞 → Type
  cmpᴳ = [] ⨾ 0ℂ ⊢_

  field
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

    storeᴳ : ∀ p
      → q ⋎₂ (p , q')
      → Δ ⨾ q' ⊢ A
      → Δ ⨾ q ⊢ ▷ᴳ[ p ] A
    releaseᴳ :
      Δ ≡ Δ₁ ⊔ Δ₂
      → q ⋎₂ (q₁ , q₂)
      → Δ₁ ⨾ q₁ ⊢ ▷ᴳ[ p ] B
      → B ∷ Δ₂ ⨾ (q₂ +ℂ p) ⊢ A
      → Δ ⨾ q ⊢ A

    getᴳ : ∀ p
      → q' ⋎₂ (p , q)
      → Δ ⨾ q' ⊢ A
      → Δ ⨾ q ⊢ ◁ᴳ[ p ] A
    payᴳ :
      q ⋎₂ (p , q')
      → Δ ⨾ q' ⊢ ◁ᴳ[ p ] A
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

    nilᴳ : cmpᴳ (Listᶜ A)
    consᴳ :
      Δ ≡ Δ₁ ⊔ Δ₂
      → q ⋎₂ (q₁ , q₂)
      → Δ₁ ⨾ q₁ ⊢ A
      → Δ₂ ⨾ q₂ ⊢ Listᶜ A
      → Δ ⨾ q ⊢ Listᶜ A
    foldrᴳ :
      cmpᴳ B
      → (A ∷ [ B ] ⨾ 0ℂ ⊢ B)
      → Δ ⨾ q ⊢ Listᶜ A
      → Δ ⨾ q ⊢ B

    nil₁ᴳ : cmpᴳ (CList₁ᴳ p A)
    cons₁ᴳ :
      Δ ≡ Δ₁ ⊔ Δ₂
      → q ⋎₂ (p , (q₁ +ℂ q₂))
      → Δ₁ ⨾ q₁ ⊢ A
      → Δ₂ ⨾ q₂ ⊢ CList₁ᴳ p A
      → Δ ⨾ q ⊢ CList₁ᴳ p A
    foldr₁ᴳ :
      cmpᴳ B
      → (A ∷ [ B ] ⨾ p ⊢ B)
      → Δ ⨾ q ⊢ CList₁ᴳ p A
      → Δ ⨾ q ⊢ B

    nil₂ᴳ : q ⋎₀ → [] ⨾ q ⊢ (CList₂ᴳ p₁ p₂ A)
    cons₂ᴳ :
      Δ ≡ Δ₁ ⊔ Δ₂
      → q ⋎₂ (p₁ , (q₁ +ℂ q₂))
      → Δ₁ ⨾ q₁ ⊢ A
      → Δ₂ ⨾ q₂ ⊢ CList₂ᴳ (p₂ +ℂ p₁) p₂ A
      → Δ ⨾ q ⊢ CList₂ᴳ p₁ p₂ A
    foldr₂ᴳ :
      (B : ℂ → 𝒞)
      → (∀ r → cmpᴳ (B r))
      → (∀ r → A ∷ [ B (p₂ +ℂ r) ] ⨾ r ⊢ B r)
      → Δ ⨾ q ⊢ CList₂ᴳ p₁ p₂ A
      → Δ ⨾ q ⊢ B p₁

  substᵐᴳ :
    q ≡ q'
    → Δ ⨾ q ⊢ A
    → Δ ⨾ q' ⊢ A
  substᵐᴳ {A = A} qq = subst (_ ⨾_⊢ A) qq

  substᴳ :
    (A : ℂ → 𝒞)
    → p ≡ p'
    → Δ ⨾ q ⊢ A p
    → Δ ⨾ q ⊢ A p'
  substᴳ {Δ = Δ} {q = q} A = subst (λ p → Δ ⨾ q ⊢ A p)

  subst2ᴳ : ∀ {p1 p1' p2 p2'} →
    (A : ℂ → ℂ → 𝒞)
    → p1 ≡ p1' → p2 ≡ p2'
    → Δ ⨾ q ⊢ A p1 p2
    → Δ ⨾ q ⊢ A p1' p2'
  subst2ᴳ {Δ = Δ} {q = q} A =  subst2 (λ p1 p2 → Δ ⨾ q ⊢ A p1 p2)

  subst3ᴳ : ∀ {p1 p1' p2 p2' p3 p3'} →
    (A : ℂ → ℂ → ℂ → 𝒞)
    → p1 ≡ p1' → p2 ≡ p2' → p3 ≡ p3'
    → Δ ⨾ q ⊢ A p1 p2 p3
    → Δ ⨾ q ⊢ A p1' p2' p3'
  subst3ᴳ {Δ = Δ} {q = q} {p1 = p1} {p2' = p2'} {p3' = p3'} A ≡1 ≡2 ≡3 e =
    substᴳ {Δ = Δ} {q = q} (λ v → A v p2' p3') ≡1 $
    subst2ᴳ {Δ = Δ} {q = q} (A p1) ≡2 ≡3 e


open Giralf

-- implementation of standard Giralf semantics
module _ (▷-impl : ▷-Laws) where
  open ▷-Laws ▷-impl

  -- interpretation of Giralf judgment into Calf
  infix 1 _⨾_⊢ˢ_
  _⨾_⊢ˢ_ : List 𝒞 → ℂ → 𝒞 → Set
  Δ ⨾ q ⊢ˢ A = ▷ⁱ[ q ] (Tensorfy Δ) ⊸ A

  cmpᴳ→U : ([] ⨾ 0ℂ ⊢ˢ A) → U A
  cmpᴳ→U {A} e = cmp→U (subst (_⊸ A) ▷ⁱ/0 e)

  U→cmpᴳ : U A → ([] ⨾ 0ℂ ⊢ˢ A)
  U→cmpᴳ {A} e = subst (_⊸ A) (sym ▷ⁱ/0) (U→cmp e)

  -- composition with credit splitting
  _⋎_⨾ᴳ_ :
    q ⋎₂ (q₁ , q₂)
    → ▷ⁱ[ q₁ ] A ⊸ B
    → ▷ⁱ[ q₂ ] B ⊸ C
    → ▷ⁱ[ q ] A ⊸ C
  s ⋎ e₁ ⨾ᴳ e₂ = subst (_⊸ _) (sym ▷ⁱ/+ ∙ cong (▷ⁱ[_] _) (+ℂ-comm _ _ ∙ s)) ((▷ⁱ-map e₁) ⨾ᶜ e₂)

  -- composition with credit AND context splitting (cut)
  _∣_⋎_⨾ᴳ_ :
    Δ ≡ Δ₁ ⊔ Δ₂
    → q ⋎₂ (q₁ , q₂)
    → Δ₁ ⨾ q₁ ⊢ˢ A
    → (A ∷ Δ₂) ⨾ q₂ ⊢ˢ B
    → Δ ⨾ q ⊢ˢ B
  _∣_⋎_⨾ᴳ_ {Δ} {Δ₁} {Δ₂} {q} {q₁} {q₂} {A} {B} S s e₁ e₂ = (▷ⁱ-map (permute S)) ⨾ᶜ (s ⋎ e₁' ⨾ᴳ e₂)
    where
      e₁' : ▷ⁱ[ q₁ ] (Tensorfy Δ₁ ⊗ Tensorfy Δ₂) ⊸ (A ⊗ Tensorfy Δ₂)
      e₁' = subst (_⊸ _) (▷ⁱA⊗B≡▷ⁱ[A⊗B] q₁) (map₂ e₁ idᶜ)

      permute : ∀ {Δ Δ₁ Δ₂} → Δ ≡ Δ₁ ⊔ Δ₂ → (Tensorfy Δ ⊸ (Tensorfy Δ₁ ⊗ Tensorfy Δ₂))
      permute base = subst (⊤ ⊸_) (sym ⊗-identityʳ) idᶜ
      permute (left {Δ'} {Δ₁'} {Δ₂'} {A} s) = subst (A ⊗ Tensorfy Δ' ⊸_) ⊗-assoc (map₂ idᶜ (permute s))
      permute {Δ₁ = Δ₁} {Δ₂} (right {Δ'} {Δ₁'} {Δ₂'} {A} s) = subst (A ⊗ Tensorfy Δ' ⊸_) rearrange (map₂ idᶜ (permute s))
        where
          rearrange : (A ⊗ (Tensorfy Δ₁ ⊗ Tensorfy Δ₂')) ≡ (Tensorfy Δ₁ ⊗ Tensorfy (A ∷ Δ₂'))
          rearrange = ⊗-assoc ∙ cong (_⊗ (Tensorfy Δ₂')) ⊗-comm ∙ sym ⊗-assoc

  impl : Giralf
  impl ._⨾_⊢_ = _⨾_⊢ˢ_
  impl .▷ᴳ[_]_ = ▷ⁱ[_]_
  impl .◁ᴳ[_]_ = ◁ⁱ[_]_
  impl .CList₁ᴳ = CList₁ ▷-impl
  impl .CList₂ᴳ = CList₂ ▷-impl

  impl .spendᴳ {q = q} {Δ = Δ} {A = A} p split e = split ⋎ spendⁱ (Tensorfy Δ) p ⨾ᴳ e

  impl .idᴳ {q} {A} split = subst (_⊸ A) (sym ▷ⁱ/0 ∙ cong₂ (▷ⁱ[_]_) split (sym ⊗-identityʳ)) idᶜ
  impl .cutᴳ = _∣_⋎_⨾ᴳ_

  impl .storeᴳ {A = A} p split e = subst (_⊸ ▷ⁱ[ p ] A) (sym ▷ⁱ/+ ∙ cong (▷ⁱ[_] _) split) (▷ⁱ-map e)
  impl .releaseᴳ {Δ₂ = Δ₂} {q₂ = q₂} {p = p} {B = B} {A = A} S s e k = S ∣ s ⋎ e ⨾ᴳ k'
    where
      k' : (▷ⁱ[ p ] B) ∷ Δ₂ ⨾ q₂ ⊢ˢ A
      k' = subst (_⊸ _) (▷ⁱ/+ ∙ cong (▷ⁱ[ q₂ ]_) (sym (▷ⁱA⊗B≡▷ⁱ[A⊗B] p))) k

  impl .getᴳ {A = A} p split = transport (sym (▷ⁱ⊣◁ⁱ ∙ cong (_⊸ A) (sym ▷ⁱ/+ ∙ cong (▷ⁱ[_] _) split)))
  impl .payᴳ {p = p} {q' = q'} {A = A} split = transport (▷ⁱ⊣◁ⁱ ∙ cong (_⊸ A) (sym ▷ⁱ/+ ∙ cong (▷ⁱ[_] _) split))

  impl .pairᴳ = pairᶜ
  impl .proj₁ᴳ {B = B} = _⨾ᶜ proj₁ᶜ {B = B}
  impl .proj₂ᴳ {A = A} = _⨾ᶜ proj₂ᶜ {A = A}

  impl .powlamᴳ {X = X} = powlam {X = X}
  impl .powappᴳ {X = X} x e = powapp {X = X} e x

  impl .absurdᴳ = _⨾ᶜ absurdᶜ
  impl .inj₁ᴳ {B = B} = _⨾ᶜ inj₁ᶜ {B = B}
  impl .inj₂ᴳ {A = A} = _⨾ᶜ inj₂ᶜ {A = A}
  impl .caseᴳ {Δ₂ = Δ₂} {q₂ = q₂} {A = A} {B} {C} S s e e₁ e₂ = S ∣ s ⋎ e ⨾ᴳ k'
    where
      k' : (A +ᶜ B) ∷ Δ₂ ⨾ q₂ ⊢ˢ C
      k' = subst (_⊸ _) (▷ⁱA+▷ⁱB≡▷ⁱ[A+B] q₂ ∙ cong (▷ⁱ[ q₂ ]_) A⊗C+B⊗C≡[A+B]⊗C) (caseᶜ e₁ e₂)

  impl .trivᴳ = U→cmpᴳ trivᶜ
  impl .checkᴳ S s e k = S ∣ s ⋎ e ⨾ᴳ (subst (λ a → ▷ⁱ[ _ ] a ⊸ _) (sym ⊗-identityˡ) k)
  impl .tensorᴳ {q₂ = q₂} S s e₁ e₂ = S ∣ s ⋎ e₁ ⨾ᴳ (subst (_⊸ _) (A⊗▷ⁱB≡▷ⁱ[A⊗B] q₂) (map₂ idᶜ e₂))
  impl .splitᴳ {q₂ = q₂} {C = C} S s e k = S ∣ s ⋎ e ⨾ᴳ (subst (λ a → ▷ⁱ[ q₂ ] a ⊸ C) ⊗-assoc k)

  impl .nilᴳ = U→cmpᴳ nil
  impl .consᴳ S s eₕ eₜ = impl .tensorᴳ S s eₕ eₜ ⨾ᶜ cons
  impl .foldrᴳ e[] e∷ = _⨾ᶜ Listᶜ.foldr (cmpᴳ→U e[]) (subst (_⊸ _) (▷ⁱ/0 ∙ cong (_ ⊗_) ⊗-identityʳ) e∷)

  impl .nil₁ᴳ = U→cmpᴳ (cnil₁ ▷-impl)
  impl .cons₁ᴳ {Δ = Δ} {p = p} S s eₕ eₜ =
    impl .storeᴳ {Δ = Δ} p s (impl .tensorᴳ S refl eₕ eₜ) ⨾ᶜ (ccons₁ ▷-impl)
  impl .foldr₁ᴳ {B = B} {p = p} e[] e∷ =
    _⨾ᶜ cfoldr₁ ▷-impl (cmpᴳ→U e[]) (subst (λ C →  ▷ⁱ[ p ] (_ ⊗ C) ⊸ B) ⊗-identityʳ e∷)

  impl .nil₂ᴳ split = subst (λ x → ▷ⁱ[ x ] _ ⊸ _) split (U→cmpᴳ (cnil₂ ▷-impl))
  impl .cons₂ᴳ {Δ = Δ} {p₁ = p₁} S s eₕ eₜ =
    impl .storeᴳ {Δ = Δ} p₁ s (impl .tensorᴳ S refl eₕ eₜ) ⨾ᶜ ccons₂ ▷-impl -- ccons₂
  impl .foldr₂ᴳ B e[] e∷ =
    _⨾ᶜ cfoldr₂ ▷-impl B (cmpᴳ→U ∘ e[]) (λ c-lin' → subst (λ C →  ▷ⁱ[ c-lin' ] (_ ⊗ C) ⊸ _) ⊗-identityʳ (e∷ c-lin'))

module _ where
  open ▷-Laws
  std-▷ : ▷-Laws
  std-▷ .▷ⁱ[_]_ = ▷[_]_
  std-▷ .◁ⁱ[_]_ = ◁[_]_
  std-▷ .spendⁱ = spend
  std-▷ .▷ⁱ⊣◁ⁱ = ▷⊣◁
  std-▷ .▷ⁱ-map = ▷-map
  std-▷ .▷ⁱ/0 = ▷/0
  std-▷ .▷ⁱ/+ = ▷/+
  std-▷ .▷ⁱA⊗▷ⁱB≡▷ⁱ[A⊗B] = ▷A⊗▷B≡▷[A⊗B]
  std-▷ .▷ⁱA⊗B≡▷ⁱ[A⊗B] = ▷A⊗B≡▷[A⊗B]
  std-▷ .A⊗▷ⁱB≡▷ⁱ[A⊗B] = A⊗▷B≡▷[A⊗B]
  std-▷ .▷ⁱA+▷ⁱB≡▷ⁱ[A+B] = ▷A+▷B≡▷[A+B]

  alt-▷ : ▷-Laws
  alt-▷ .▷ⁱ[_]_ c A = A
  alt-▷ .◁ⁱ[_]_ c A = A
  alt-▷ .spendⁱ A c = CHARGE c
  alt-▷ .▷ⁱ⊣◁ⁱ = refl
  alt-▷ .▷ⁱ-map f = f
  alt-▷ .▷ⁱ/0 = refl
  alt-▷ .▷ⁱ/+ = refl
  alt-▷ .▷ⁱA⊗▷ⁱB≡▷ⁱ[A⊗B] c₁ c₂ = refl
  alt-▷ .▷ⁱA⊗B≡▷ⁱ[A⊗B] c = refl
  alt-▷ .A⊗▷ⁱB≡▷ⁱ[A⊗B] c = refl
  alt-▷ .▷ⁱA+▷ⁱB≡▷ⁱ[A+B] c = refl


std-giralf : Giralf
std-giralf = impl std-▷

alt-giralf : Giralf
alt-giralf = impl alt-▷
