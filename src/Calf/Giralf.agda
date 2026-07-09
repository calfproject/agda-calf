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
open import Calf.Computation.PList1
open import Calf.Computation.PList2
open import Calf.Computation.Free
open import Calf.Computation.Power

Context : Type₁
Context = 𝒞 × ℂ  -- List 𝒞 × ℙ

module _ where  -- promonoid
  _⋎₀ : ℂ → Type
  q ⋎₀ = 0ℂ ≡ q

  _⋎₂_ : ℂ → (ℂ × ℂ) → Type  -- promonoid
  q ⋎₂ (q₁ , q₂) = q₁ +ℂ q₂ ≡ q

  -- _⋎_ : ℂ → List (ℂ) → Type  -- promonoid
  -- p ⋎ ps = foldr _+ℂ_ 0ℂ ps ≡ p


variable
  p p' p₁ p₂ q q' q₁ q₂ r r' : ℂ


infix 1 _⊢_

_⊢_ : Context → 𝒞 → Type
Δ , q ⊢ A = ▷[ q ] Δ ⊸ A

idᴳ :
  q ⋎₀
  → A , q ⊢ A
idᴳ {q} {A} split = transport (cong (_⊸ A) (sym ▷/0 ∙ cong (▷[_] _) split)) idᶜ

letᴳ :
  q ⋎₂ (q₁ , q₂)
  → A , q₁ ⊢ B
  → B , q₂ ⊢ C
  → A , q ⊢ C
letᴳ split e1 e2 =
  transport (cong (_⊸ _) (sym ▷/+ ∙ cong (▷[_] _) (+ℂ-comm _ _ ∙ split))) ((▷-map e1) ⨾ᶜ e2)

cmpᴳ : 𝒞 → Type
cmpᴳ = ⊤ , 0ℂ ⊢_
-- cmpᴳ A = ∀ {q} → q ⋎₀ → (⊤ , q ⊢ A)

cmpᴳ→cmp : cmpᴳ A → U A
cmpᴳ→cmp e = e .U (subst U (sym ▷/0) 0ℂ)

cmp→cmpᴳ : U A → cmpᴳ A
cmp→cmpᴳ {A} e =
  subst (_⊸ A) (sym ▷/0) $
  record { U = flip (A .charge) e ; charge = λ _ _ → A .charge/+ }

module _ where
  substᵐᴳ :
    q ≡ q'
    → Δ , q ⊢ A
    → Δ , q' ⊢ A
  substᵐᴳ qq = subst (_⊸ _) (cong (▷[_] _) qq)

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
  subst3ᴳ {p1 = p1} {p2' = p2'} {p3' = p3'} A ≡1 ≡2 ≡3 e = substᴳ (λ v → A v p2' p3') ≡1 (subst2ᴳ (A p1) ≡2 ≡3 e)

module _ where
  storeᴳ : ∀ p
    → q ⋎₂ (p , q')
    → Δ , q' ⊢ A
    → Δ , q ⊢ ▷[ p ] A
  storeᴳ p split e = subst (_⊸ _) (sym ▷/+ ∙ cong (▷[_] _) split) (▷-map e)
  -- TODO: use subst instead of transport if possible

  releaseᴳ :
    Δ , q ⊢ ▷[ p ] B
    → B , p ⊢ A
    → Δ , q ⊢ A
  releaseᴳ e k = e ⨾ᶜ k

spendᴳ : ∀ p
  → q ⋎₂ (p , q')
  → Δ , q' ⊢ A
  → Δ , q ⊢ A
spendᴳ p split e = releaseᴳ (storeᴳ p split e) (spend p)

module _ where
  getᴳ : ∀ p
    → q' ⋎₂ (p , q)
    → Δ , q' ⊢ A
    → Δ , q ⊢ ◁[ p ] A
  getᴳ p split = transport (sym (▷⊣◁ ∙ cong (_⊸ _) (sym ▷/+ ∙ cong (▷[_] _) split)))

  payᴳ :
    q ⋎₂ (p , q')
    → Δ , q' ⊢ ◁[ p ] A
    → Δ , q ⊢ A
  payᴳ split = transport (▷⊣◁ ∙ cong (_⊸ _) (sym ▷/+ ∙ cong (▷[_] _) split))

module _ where
  nil₁ᴳ : cmpᴳ (PList₁ p X)
  nil₁ᴳ = cmp→cmpᴳ pnil₁

  cons₁ᴳ :
    q ⋎₂ (p , q')
    → X
    → Δ , q' ⊢ PList₁ p X
    → Δ , q ⊢ PList₁ p X
  cons₁ᴳ split x e = storeᴳ _ split e ⨾ᶜ pcons₁ x

  foldr₁ᴳ :
    cmpᴳ A
    → (X → A , p ⊢ A)
    → Δ , q ⊢ PList₁ p X
    → Δ , q ⊢ A
  foldr₁ᴳ e-nil e-cons e = e ⨾ᶜ pfoldr₁ (cmpᴳ→cmp e-nil) e-cons

module _ where
  nil₂ᴳ : q ⋎₀ → ⊤ , q ⊢ (PList₂ p₁ p₂ X)
  nil₂ᴳ split = subst (λ x → ▷[ x ] _ ⊸ _) split (cmp→cmpᴳ pnil₂)

  cons₂ᴳ :
    q ⋎₂ (p₁ , q')
    → X
    → Δ , q' ⊢ PList₂ (p₂ +ℂ p₁) p₂ X
    → Δ , q ⊢ PList₂ p₁ p₂ X
  cons₂ᴳ split-q x e =
    storeᴳ _ split-q e ⨾ᶜ pcons₂ x

  foldr₂ᴳ :
    (A : ℂ → 𝒞)
    → (∀ r → cmpᴳ (A r))
    → (∀ r → X → A (p₂ +ℂ r) , r ⊢ A r)
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

module _ where
  powlamᴳ :
    (X → Δ , q ⊢ A)
    → Δ , q ⊢ X ⇀ A
  powlamᴳ {X = X} = powlam {X = X}

  powappᴳ :
    X → Δ , q ⊢ X ⇀ A
    → Δ , q ⊢ A
  powappᴳ {X = X} x e = powapp {X = X} e x
