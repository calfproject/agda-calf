open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence using (ua→; ua-gluePath)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Calf.Computation where

open import Calf.Core.Abstract
open import Calf.Value
open import Calf.Core.Cost
open import Cubical.Data.Nat using (ℕ; zero; suc) renaming (_+_ to _+ℕ_)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence using (ua; ua→; ua-gluePath)

record 𝒞 : 𝒱₁ where
  field
    U : 𝒱
    is-preorder : isPreorder U

  is-set : isSet U
  is-set = isPreorder→isSet is-preorder

  field
    charge : ℂ → U → U
    charge/0 : ∀ {a} → charge 0ℂ a ≡ a
    charge/+ : ∀ {a c₁ c₂} → charge (c₁ +ℂ c₂) a ≡ charge c₁ (charge c₂ a)

  opaque
    charge/comm : ∀ {c} {c'} {a}
      → charge c (charge c' a) ≡ charge c' (charge c a)
    charge/comm = sym charge/+ ∙ cong (flip charge _) (+ℂ-comm _ _) ∙ charge/+

  charge/BEH : ∀ {c} {a} → BEH → charge c a ≡ a
  charge/BEH {c} {a} beh =
    cong (flip charge a) (isContr→isProp (isAlgorithmicℂ beh) c 0ℂ) ∙ charge/0

  charge` : ℕ → U → U
  charge` zero a = a
  charge` (suc n) a = charge 1ℂ (charge` n a)

  charge`/charge : ∀ n {a} → charge` n a ≡ charge (` n) a
  charge`/charge zero = sym charge/0
  charge`/charge (suc n) = cong (charge 1ℂ) (charge`/charge n) ∙ sym charge/+

  charge`/+ : ∀ m n {a} → charge` (m +ℕ n) a ≡ charge` m (charge` n a)
  charge`/+ zero n = refl
  charge`/+ (suc m) n = cong (charge 1ℂ) (charge`/+ m n)

  charge`/BEH : ∀ n {a} → BEH → charge` n a ≡ a
  charge`/BEH zero beh = refl
  charge`/BEH (suc n) beh = charge/BEH beh ∙ charge`/BEH n beh
open 𝒞 public

variable
  A B C : 𝒞

Uₚ : 𝒞 → 𝒱ₚ
Uₚ A = U A , A .is-preorder

⊑-syntax : U A → U A → 𝒱
⊑-syntax {A} = _⊑_ {U A}

syntax ⊑-syntax {A} a a' = a ⊑[ A ] a'

module ⊑-Reasoning (A : 𝒞) where
  open import Relation.Binary

  ≡-isEquivalence : IsEquivalence (_≡_ {A = U A})
  ≡-isEquivalence = record { refl = refl ; sym = sym ; trans = _∙_ }

  open Preorder hiding (refl)
  open IsPreorder hiding (refl)

  ⊑-preorder : Preorder _ _ _
  ⊑-preorder .Carrier = U A
  ⊑-preorder ._≈_ = _≡_
  ⊑-preorder ._≲_ = _⊑_ {U A}
  ⊑-preorder .Preorder.isPreorder .isEquivalence = ≡-isEquivalence
  ⊑-preorder .Preorder.isPreorder .reflexive = ⊑-reflexive
  ⊑-preorder .Preorder.isPreorder .trans = ⊑-trans (A .is-preorder)

  open import Relation.Binary.Reasoning.Preorder ⊑-preorder as P public
    renaming (_∎ to _∎ᴾ)

  infixr 2 step-⊑
  step-⊑ = step-≲
  syntax step-⊑ x yRz x⊑ᵛy = x ⊑⟨ x⊑ᵛy ⟩ yRz

  infixr 2 step-≡'
  step-≡' = step-≈
  syntax step-≡' x yRz x⊑ᵛy = x ≡ᴾ⟨ x⊑ᵛy ⟩ yRz

infix 1 _⊸_
record _⊸_ (A B : 𝒞) : 𝒱 where
  field
    U : U A → U B
    charge : ∀ c a → U (A .charge c a) ≡ B .charge c (U a)
open _⊸_ public

isEquivᶜ : (A ⊸ B) → 𝒱
isEquivᶜ f = isEquiv (U f)

_≃ᶜ_ : 𝒞 → 𝒞 → 𝒱
A ≃ᶜ B = Σ (A ⊸ B) isEquivᶜ

idᶜ : A ⊸ A
idᶜ .U a = a
idᶜ .charge _ _ = refl

infixl 9 _⨾ᶜ_
_⨾ᶜ_ : (A ⊸ B) → (B ⊸ C) → (A ⊸ C)
(f ⨾ᶜ g) .U = g .U ∘ f .U
(f ⨾ᶜ g) .charge c a = cong (g .U) (f .charge c a) ∙ g .charge c (f .U a)

CHARGE : ℂ → A ⊸ A
CHARGE {A} c .U = charge A c
CHARGE {A} c .charge c' a = charge/comm A {c} {c'} {a}

opaque
  isPropCharge/0
    : {U : 𝒱} {isSetU : isSet U} (charge : ℂ → U → U)
    → isProp (∀ {a} → charge 0ℂ a ≡ a)
  isPropCharge/0 {U} {isSetU} charge =
    isPropImplicitΠ λ a → isSetU (charge 0ℂ a) a

opaque
  isPropCharge/+
    : {U : 𝒱} {isSetU : isSet U} (charge : ℂ → U → U)
    → isProp (∀ {a c₁ c₂} → charge (c₁ +ℂ c₂) a ≡ charge c₁ (charge c₂ a))
  isPropCharge/+ {U} {isSetU} charge =
    isPropImplicitΠ3 λ a c₁ c₂ →
      isSetU (charge (c₁ +ℂ c₂) a) (charge c₁ (charge c₂ a))

𝒞-path
  : {A B : 𝒞}
  → (U-path : A .U ≡ B .U)
  → PathP
      (λ i → ℂ → U-path i → U-path i)
      (charge A)
      (charge B)
  → A ≡ B
𝒞-path {A} {B} U-path charge-path i =
  record
    { U = U-path i
    ; is-preorder =
      isProp→PathP
        (λ i → isPropIsPreorder {X = U-path i})
        (A .is-preorder)
        (B .is-preorder)
        i
    ; charge = charge-path i
    ; charge/0 =
        isProp→PathP
          (λ i → isPropCharge/0 {U = U-path i} {isSetUi i} (charge-path i))
          (A .charge/0)
          (B .charge/0)
          i
    ; charge/+ =
        isProp→PathP
          (λ i → isPropCharge/+ {U = U-path i} {isSetUi i} (charge-path i))
          (A .charge/+)
          (B .charge/+)
          i
    }
  where
    opaque
      isSetUi : PathP (λ i → isSet (U-path i)) (is-set A) (is-set B)
      isSetUi =
        isProp→PathP
          (λ i → isPropIsSet {A = U-path i})
          (is-set A)
          (is-set B)

opaque
  isProp⊸charge
    : (A B : 𝒞) (f : U A → U B)
    → isProp ((c : ℂ) (a : U A) → f (A .charge c a) ≡ B .charge c (f a))
  isProp⊸charge A B f =
    isPropΠ2 λ c a → is-set B (f (A .charge c a)) (B .charge c (f a))

opaque
  ⊸-path
    : {A₀ A₁ B₀ B₁ : 𝒞}
    → (A-path : A₀ ≡ A₁)
    → (B-path : B₀ ≡ B₁)
    → {f₀ : A₀ ⊸ B₀}
    → {f₁ : A₁ ⊸ B₁}
    → PathP (λ i → U (A-path i) → U (B-path i)) (f₀ .U) (f₁ .U)
    → PathP (λ i → A-path i ⊸ B-path i) f₀ f₁
  ⊸-path A-path B-path {f₀ = f₀} {f₁ = f₁} U-path i .U = U-path i
  ⊸-path A-path B-path {f₀ = f₀} {f₁ = f₁} U-path i .charge =
    isProp→PathP
      (λ i → isProp⊸charge (A-path i) (B-path i) (U-path i))
      (f₀ .charge)
      (f₁ .charge)
      i

⊸-Σ-Iso
  : Iso (A ⊸ B)
      (Σ[ h ∈ (U A → U B) ]
        ((c : ℂ) (a : U A) → h (A .charge c a) ≡ B .charge c (h a)))
⊸-Σ-Iso .Iso.fun f = f .U , f .charge
⊸-Σ-Iso .Iso.inv (h , ch) .U = h
⊸-Σ-Iso .Iso.inv (h , ch) .charge = ch
⊸-Σ-Iso .Iso.rightInv _ = refl
⊸-Σ-Iso .Iso.leftInv _ = refl

opaque
  isSet⊸ : isSet (A ⊸ B)
  isSet⊸ {A} {B} =
    isOfHLevelRetractFromIso 2 ⊸-Σ-Iso
      (isSetΣ (isSet→ (is-set B)) λ h → isProp→isSet (isProp⊸charge A B h))

CHARGE-commute
  : ∀ c (e : A ⊸ B)
  → CHARGE c ⨾ᶜ e ≡ e ⨾ᶜ CHARGE c
CHARGE-commute c e =
  ⊸-path refl refl (funExt λ a → e .charge c a)

CHARGE-comm : ∀ c₁ c₂ → CHARGE {A} c₁ ⨾ᶜ CHARGE c₂ ≡ CHARGE c₂ ⨾ᶜ CHARGE c₁
CHARGE-comm c₁ c₂ = CHARGE-commute c₁ (CHARGE c₂)

CHARGE-0 : CHARGE {A} 0ℂ ≡ idᶜ
CHARGE-0 {A = A} =
  ⊸-path refl refl (funExt λ a → A .charge/0)

CHARGE-+ : ∀ c₁ c₂ → CHARGE {A} (c₁ +ℂ c₂) ≡ CHARGE c₂ ⨾ᶜ CHARGE c₁
CHARGE-+ {A = A} c₁ c₂ =
  ⊸-path refl refl (funExt λ a → A .charge/+)

idᶜ⨾ᶜf≡f : (f : A ⊸ B) → idᶜ ⨾ᶜ f ≡ f
idᶜ⨾ᶜf≡f f = ⊸-path refl refl refl

f⨾ᶜidᶜ≡f : (f : A ⊸ B) → f ⨾ᶜ idᶜ ≡ f
f⨾ᶜidᶜ≡f f = ⊸-path refl refl (funExt (λ x → refl))

opaque
  charge-path
    : {X Y : 𝒱}
    → (e : X ≃ Y)
    → (chargeX : ℂ → X → X)
    → (chargeY : ℂ → Y → Y)
    → ((c : ℂ) (x : X) → e .fst (chargeX c x) ≡ chargeY c (e .fst x))
    → PathP
        (λ i → ℂ → ua e i → ua e i)
        chargeX
        chargeY
  charge-path e chargeX chargeY h =
    funExt λ c → ua→ λ x → ua-gluePath e (h c x)

conservativity :
  (f : A ⊸ B)
  → isEquivᶜ f
  → A ≡ B
conservativity {A} {B} f f-equiv =
  𝒞-path
    (ua (f .U , f-equiv))
    (charge-path (f .U , f-equiv) (A .charge) (B .charge) (f .charge))

uaᶜ : A ≃ᶜ B → A ≡ B
uaᶜ = uncurry conservativity

conservativity-⊸ :
  {A A' B B' : 𝒞} (e : A ⊸ A') (ee : isEquivᶜ e) (e' : B ⊸ B') (ee' : isEquivᶜ e')
  {f : A ⊸ B} {g : A' ⊸ B'}
  → f ⨾ᶜ e' ≡ e ⨾ᶜ g
  → PathP (λ i → conservativity e ee i ⊸ conservativity e' ee' i) f g
conservativity-⊸ e ee e' ee' nat =
  ⊸-path (conservativity e ee) (conservativity e' ee')
    (ua→ {e = e .U , ee} λ a → ua-gluePath (e' .U , ee') (funExt⁻ (cong U nat) a))

opaque
  uaᶜ-⊸ :
    {A A' B B' : 𝒞} (e : A ≃ᶜ A') (e' : B ≃ᶜ B') {f : A ⊸ B} {g : A' ⊸ B'}
    → f ⨾ᶜ e' .fst ≡ e .fst ⨾ᶜ g
    → PathP (λ i → uaᶜ e i ⊸ uaᶜ e' i) f g
  uaᶜ-⊸ (e , ee) (e' , ee') = conservativity-⊸ e ee e' ee'

invEquivᶜ : (f : A ⊸ B) → isEquivᶜ f → B ⊸ A
invEquivᶜ {A} {B} f fe .U = invEq (f .U , fe)
invEquivᶜ {A} {B} f fe .charge c b =
    cong (invEq e) (cong (B .charge c) (sym (secEq e b)))
  ∙ cong (invEq e) (sym (f .charge c (invEq e b)))
  ∙ retEq e (A .charge c (invEq e b))
  where
    e = (f .U , fe)

infixr 30 _∙ₑᶜ_
_∙ₑᶜ_ : A ≃ᶜ B → B ≃ᶜ C → A ≃ᶜ C
(e ∙ₑᶜ f) .fst = e .fst ⨾ᶜ f .fst
(e ∙ₑᶜ f) .snd = ((e .fst .U , e .snd) ∙ₑ (f .fst .U , f .snd)) .snd

⊸-inv : (e : B ⊸ C) → isEquivᶜ e → C ⊸ B
⊸-inv e h .U = invIsEq h
⊸-inv {B = B} {C = C} e h .charge c x =
    sym (cong (invIsEq h)
      (e .charge c (invIsEq h x) ∙ cong (C .charge c) (secIsEq h x)))
  ∙ retIsEq h (B .charge c (invIsEq h x))

⊸-postcomp-isEquiv : {A B C : 𝒞} (e : B ⊸ C) → isEquivᶜ e
  → isEquiv (λ (f : A ⊸ B) → f ⨾ᶜ e)
⊸-postcomp-isEquiv e h =
  isoToIsEquiv (iso (_⨾ᶜ e) (_⨾ᶜ ⊸-inv e h)
    (λ g → ⊸-path refl refl (funExt λ a → secIsEq h (g .U a)))
    (λ f → ⊸-path refl refl (funExt λ a → retIsEq h (f .U a))))

⊸-postcomp-≃ : {A B C : 𝒞} (e : B ⊸ C) → isEquivᶜ e → (A ⊸ B) ≃ (A ⊸ C)
⊸-postcomp-≃ e h = (_⨾ᶜ e) , ⊸-postcomp-isEquiv e h

𝒞WithStr : (B : 𝒞 → 𝒱) → 𝒱₁
𝒞WithStr B = Σ[ A ∈ 𝒞 ] B A

⟨_⟩ᶜ : ∀ {B} → 𝒞WithStr B → 𝒞
⟨_⟩ᶜ = fst

strᶜ : ∀ {B} → (A : 𝒞WithStr B) → B ⟨ A ⟩ᶜ
strᶜ = snd
