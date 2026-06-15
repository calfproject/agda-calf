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
open import Calf.Computation.Credit
open import Calf.Computation.Debit
open import Calf.Computation.PList1
open import Calf.Computation.PList2
open import Calf.Computation.Free

Context : Type₁
Context = 𝒞 × val ℂ  -- List 𝒞 × val ℙ

module _ where  -- promonoid
  _⋎₀ : val ℂ → Type
  q ⋎₀ = 0ℂ ≡ q

  _⋎₂_ : val ℂ → (val ℂ × val ℂ) → Type  -- promonoid
  q ⋎₂ (q₁ , q₂) = q₁ +ℂ q₂ ≡ q

  -- _⋎_ : val ℂ → List (val ℂ) → Type  -- promonoid
  -- p ⋎ ps = foldr _+ℂ_ 0ℂ ps ≡ p


variable
  p p' p₁ p₂ q q' q₁ q₂ r r' : val ℂ


infix 1 _⊢_

_⊢_ : Context → 𝒞 → Type
Δ , q ⊢ A = ▷'[ q ] Δ ⊸ A

idᴳ :
  q ⋎₀
  → A , q ⊢ A
idᴳ {q} {A} split = transport (cong (_⊸ A) (sym ▷'/0 ∙ cong (▷'[_] _) split)) idᶜ

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
  releaseᴳ (storeᴳ p split e) spend

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
    → p ⋎₂ (p₂ , p₁)
    → val X
    → Δ , q' ⊢ PList₂ p p₂ X
    → Δ , q ⊢ PList₂ p₁ p₂ X
  cons₂ᴳ split-q split-p x e =
    storeᴳ _ split-q e ⨾ᶜ
    transport (cong (λ p → (▷'[ _ ] PList₂ p _ _) ⊸ _) split-p) (pcons₂ x)

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
