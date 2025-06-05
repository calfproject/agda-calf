{-# OPTIONS --rewriting --allow-unsolved-metas #-}

open import Algebra.Cost
open import Relation.Binary using (IsPreorder)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; module ≡-Reasoning)

module Calf.Giralf (ℂᶜ : Set) (zeroᶜ : ℂᶜ) (_+ᶜ_ : ℂᶜ → ℂᶜ → ℂᶜ) (isCommutativeMonoid : IsCommutativeMonoid ℂᶜ _+ᶜ_ zeroᶜ) where

record _≤Temporal_ (c c' : ℂᶜ) : Set where
  field
    difference : ℂᶜ
    proof : c +ᶜ difference ≡ c'

isPreorder : IsPreorder _≡_ _≤Temporal_
isPreorder .IsPreorder.isEquivalence = Eq.isEquivalence
isPreorder .IsPreorder.reflexive refl ._≤Temporal_.difference = zeroᶜ
isPreorder .IsPreorder.reflexive refl ._≤Temporal_.proof = IsCommutativeMonoid.identityʳ ℂᶜ isCommutativeMonoid _
isPreorder .IsPreorder.trans x≤y y≤z ._≤Temporal_.difference = x≤y ._≤Temporal_.difference +ᶜ y≤z ._≤Temporal_.difference
isPreorder .IsPreorder.trans {x} {y} {z} x≤y y≤z ._≤Temporal_.proof =
  let open ≡-Reasoning in
  begin
    x +ᶜ (x≤y ._≤Temporal_.difference +ᶜ y≤z ._≤Temporal_.difference)
  ≡⟨ IsCommutativeMonoid.assoc ℂᶜ isCommutativeMonoid _ _ _ ⟨
    (x +ᶜ x≤y ._≤Temporal_.difference) +ᶜ y≤z ._≤Temporal_.difference
  ≡⟨ Eq.cong (_+ᶜ _) (_≤Temporal_.proof x≤y) ⟩
    y +ᶜ y≤z ._≤Temporal_.difference
  ≡⟨ _≤Temporal_.proof y≤z ⟩
    z
  ∎

open import Algebra.Bundles using (CommutativeSemigroup)

commutativeSemigroup : CommutativeSemigroup _ _
commutativeSemigroup .CommutativeSemigroup.Carrier = ℂᶜ
commutativeSemigroup .CommutativeSemigroup._≈_ = _≡_
commutativeSemigroup .CommutativeSemigroup._∙_ = _+ᶜ_
commutativeSemigroup .CommutativeSemigroup.isCommutativeSemigroup = IsCommutativeMonoid.isCommutativeSemigroup ℂᶜ isCommutativeMonoid

open import Algebra.Properties.CommutativeSemigroup commutativeSemigroup using (interchange)

costMonoid : CostMonoid
costMonoid .CostMonoid.ℂ = ℂᶜ
costMonoid .CostMonoid.zero = zeroᶜ
costMonoid .CostMonoid._+_ = _+ᶜ_
costMonoid .CostMonoid._≤_ = _≤Temporal_
costMonoid .CostMonoid.isCostMonoid .IsCostMonoid.isMonoid = IsCommutativeMonoid.isMonoid isCommutativeMonoid
costMonoid .CostMonoid.isCostMonoid .IsCostMonoid.isPreorder = isPreorder
costMonoid .CostMonoid.isCostMonoid .IsCostMonoid.isMonotone .IsMonotone.∙-mono-≤ x≤y u≤v ._≤Temporal_.difference = x≤y ._≤Temporal_.difference +ᶜ u≤v ._≤Temporal_.difference
costMonoid .CostMonoid.isCostMonoid .IsCostMonoid.isMonotone .IsMonotone.∙-mono-≤ {x} {y} {u} {v} x≤y u≤v ._≤Temporal_.proof =
  let open ≡-Reasoning in
  begin
    (x +ᶜ u) +ᶜ (x≤y ._≤Temporal_.difference +ᶜ u≤v ._≤Temporal_.difference)
  ≡⟨ interchange x u (x≤y ._≤Temporal_.difference) (u≤v ._≤Temporal_.difference) ⟩
    (x +ᶜ x≤y ._≤Temporal_.difference) +ᶜ (u +ᶜ u≤v ._≤Temporal_.difference)
  ≡⟨ Eq.cong₂ _+ᶜ_ (x≤y ._≤Temporal_.proof) (u≤v ._≤Temporal_.proof) ⟩
    y +ᶜ v
  ∎

open CostMonoid costMonoid


open import Calf.Prelude
open import Calf.CBPV
open import Calf.Directed
open import Calf.Step costMonoid
open import Calf.Data.Product
open import Calf.Data.Sum as Sum
open import Calf.Data.List


open import Function using (_∘_; const)

zero/min : (c : ℂ) → zero ≤ c
zero/min c ._≤Temporal_.difference = c
zero/min c ._≤Temporal_.proof = +-identityˡ c

+-comm : (a b : ℂ) → a + b ≡ b + a
+-comm = IsCommutativeMonoid.comm isCommutativeMonoid

open import Algebra using (CommutativeMonoid)

comm-monoid : CommutativeMonoid _ _
comm-monoid .CommutativeMonoid.Carrier = ℂ
comm-monoid .CommutativeMonoid._≈_ = _≡_
comm-monoid .CommutativeMonoid._∙_ = _+_
comm-monoid .CommutativeMonoid.ε = zero
comm-monoid .CommutativeMonoid.isCommutativeMonoid = isCommutativeMonoid

import Data.Fin as Fin
open import Algebra.Solver.CommutativeMonoid comm-monoid using (prove; Expr; var; _⊕_)
open import Data.Nat.Base using (ℕ; z≤n; s≤s)
module SolverHelp where
  v₁ : ∀ {n : ℕ} → Expr (ℕ.suc n)
  v₁ {n} = var (Fin.zero)
  v₂ : ∀ {n : ℕ} → Expr (ℕ.suc (ℕ.suc n))
  v₂ {n} = var (Fin.suc Fin.zero)
  v₃ : ∀ {n : ℕ} → Expr (ℕ.suc (ℕ.suc (ℕ.suc n)))
  v₃ {n} = var (Fin.suc (Fin.suc Fin.zero))
  v₄ : ∀ {n : ℕ} → Expr (ℕ.suc (ℕ.suc (ℕ.suc (ℕ.suc n))))
  v₄ {n} = var (Fin.suc (Fin.suc (Fin.suc Fin.zero)))
import Data.Vec.Base as Vec


open import Data.List.Base as List
module Perm-Split {E : Set} where
  data _≡_⊔_ : List E → List E → List E → Set where
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


record Giralf : Set₁ where
  𝓥 : Set
  𝓥 = tp⁺

  valᵍ : 𝓥 → Set
  valᵍ = val

  field
    𝓒 : Set
    _⨾_⊢_ : List 𝓒 → ℂ → 𝓒 → Set

    idᵍ : ∀ {q A} → [ A ] ⨾ q ⊢ A

  cmpᵍ : ℂ → 𝓒 → Set
  cmpᵍ q A = [] ⨾ q ⊢ A

  _⊸_ : 𝓒 → 𝓒 → 𝓥
  A ⊸ B = meta⁺ ([ A ] ⨾ zero ⊢ B)

  Uᵍ : 𝓒 → 𝓥
  Uᵍ A = meta⁺ (cmpᵍ zero A)

  field
    charge : ∀ {Δ r q A} (p : ℂ)
      → r ≡ q + p
      → Δ ⨾ q ⊢ A
      → Δ ⨾ r ⊢ A

    Fᵍ : 𝓥 → 𝓒
    retᵍ : ∀ {q X} → valᵍ X → cmpᵍ q (Fᵍ X)
    bindᵍ : ∀ {Δ Δ₁ Δ₂ q q₁ q₂ X A}
      → Δ ≡ Δ₁ ⊔ Δ₂
      → q ≡ q₁ + q₂
      → Δ₁ ⨾ q₁ ⊢ (Fᵍ X)
      → (valᵍ X → Δ₂ ⨾ q₂ ⊢ A)
      → Δ ⨾ q ⊢ A

    _⋊ᵍ_ : ℂ → 𝓒 → 𝓒
    store : ∀ {Δ r q A} (p : ℂ)
      → r ≡ q + p
      → Δ ⨾ q ⊢ A
      → Δ ⨾ r ⊢ (p ⋊ᵍ A)
    release : ∀ {Δ Δ₁ Δ₂ p q q₁ q₂ A B}
      → Δ ≡ Δ₁ ⊔ Δ₂
      → q ≡ q₁ + q₂
      → Δ₁ ⨾ q₁ ⊢ (p ⋊ᵍ A)
      → (A ∷ Δ₂) ⨾ p + q₂ ⊢ B
      → Δ ⨾ q ⊢ B

    ⊥ᵍ : 𝓒
    absurdᵍ : ∀ {Δ q C}
      → Δ ⨾ q ⊢ ⊥ᵍ
      → Δ ⨾ q ⊢ C

    _⊎ᵍ_ : 𝓒 → 𝓒 → 𝓒
    inj₁ᵍ : ∀ {Δ q A B} → Δ ⨾ q ⊢ A → Δ ⨾ q ⊢ (A ⊎ᵍ B)
    inj₂ᵍ : ∀ {Δ q A B} → Δ ⨾ q ⊢ B → Δ ⨾ q ⊢ (A ⊎ᵍ B)
    caseᵍ : ∀ {Δ Δ₁ Δ₂ q q₁ q₂ A B C}
      → Δ ≡ Δ₁ ⊔ Δ₂
      → q ≡ q₁ + q₂
      → Δ₁ ⨾ q₁ ⊢ (A ⊎ᵍ B)
      → (A ∷ Δ₂) ⨾ q₂ ⊢ C
      → (B ∷ Δ₂) ⨾ q₂ ⊢ C
      → Δ ⨾ q ⊢ C

    ⊤ᵍ : 𝓒
    trivᵍ : ∀ {q} → cmpᵍ q ⊤ᵍ
    checkᵍ : ∀ {Δ Δ₁ Δ₂ q q₁ q₂ C}
      → Δ ≡ Δ₁ ⊔ Δ₂
      → q ≡ q₁ + q₂
      → Δ₁ ⨾ q₁ ⊢ ⊤ᵍ
      → Δ₂ ⨾ q₂ ⊢ C
      → Δ ⨾ q ⊢ C

    _⊗ᵍ_ : 𝓒 → 𝓒 → 𝓒
    tensorᵍ : ∀ {Δ Δ₁ Δ₂ q q₁ q₂ A B}
      → Δ ≡ Δ₁ ⊔ Δ₂
      → q ≡ q₁ + q₂
      → Δ₁ ⨾ q₁ ⊢ A
      → Δ₂ ⨾ q₂ ⊢ B
      → Δ ⨾ q ⊢ (A ⊗ᵍ B)
    splitᵍ : ∀ {Δ Δ₁ Δ₂ q q₁ q₂ A B C}
      → Δ ≡ Δ₁ ⊔ Δ₂
      → q ≡ q₁ + q₂
      → Δ₁ ⨾ q₁ ⊢ (A ⊗ᵍ B)
      → (A ∷ B ∷ Δ₂) ⨾ q₂ ⊢ C
      → Δ ⨾ q ⊢ C

    listᵍ : 𝓒 → 𝓒
    nilᵍ : ∀ {q A} → cmpᵍ q (listᵍ A)
    consᵍ : ∀ {Δ Δ₁ Δ₂ q q₁ q₂ A}
      → Δ ≡ Δ₁ ⊔ Δ₂
      → q ≡ q₁ + q₂
      → Δ₁ ⨾ q₁ ⊢ A
      → Δ₂ ⨾ q₂ ⊢ listᵍ A
      → Δ ⨾ q ⊢ listᵍ A
    foldrᵍ : ∀ {Δ q A B}
      → Δ ⨾ q ⊢ listᵍ A
      → cmpᵍ zero B
      → (B ∷ A ∷ []) ⨾ zero ⊢ B
      → Δ ⨾ q ⊢ B

  variable
    X Y Z : 𝓥
    A B C : 𝓒
    p q r : ℂ


_⊸F_ : tp⁺ → tp⁺ → Set
X ⊸F Y = cmp (X ⇀ F Y)

record PotentialFunction : Set where
  field
    ₀ : tp⁺
    Φᶜ : val ₀ → ℂ
  Φ : ₀ ⊸F ₀
  Φ a = step (F _) (Φᶜ a) (ret a)
open PotentialFunction

_⇒_ : tp⁺ → tp⁺ → Set
X ⇒ Y = val X → val Y

record Square (A : PotentialFunction) (q : ℂ) (B : PotentialFunction) : Set where
  field
    top : A .₀ ⊸F B .₀
    bot : A .₀ ⇒ B .₀
    square :
      (a : val (A .₀)) →
        bind (F _) (top a) (Φ B) ≤⁻[ F _ ] bind (F _) (Φ A a) (step (F _) q ∘ ret ∘ bot)
open Square


weaken-pot : ∀ {A} (q : ℂ) → Square A q A
weaken-pot _ .top = ret
weaken-pot _ .bot = Function.id
weaken-pot {A} q .square a = bind-monoʳ-≤⁻ (Φ A a) (λ a → step-monoˡ-≤⁻ (ret a) (zero/min q))

step-ret-congˡ : ∀ {X c d} → (v : val X) → (c ≡ d) → (step (F X) c (ret v) ≡ step (F X) d (ret v))
step-ret-congˡ v = Eq.cong (λ c → step (F _) c (ret v))


_⋎_⨾□_ : ∀ {A B C p q r} → r ≡ p + q → Square A p B → Square B q C → Square A r C
(s ⋎ e ⨾□ f) .top a = bind (F _) (e .top a) (f .top)
(s ⋎ e ⨾□ f) .bot = (f .bot) ∘ (e .bot)
(_⋎_⨾□_ {A} {B} {C} {p} {q} {r} s e f) .square a =
  let open ≤⁻-Reasoning (F _) in
  begin
    bind (F _) (e .top a) (λ b → bind (F _) (f .top b) (Φ C))
  ≲⟨ bind-monoʳ-≤⁻ (e .top a) (f .square) ⟩
    bind (F _) (e .top a) (λ b → bind (F _) (Φ B b) (step (F _) q ∘ ret ∘ f .bot))
  ≡⟨⟩
    bind (F _) (bind (F _) (e .top a) (Φ B)) (step (F _) q ∘ ret ∘ f .bot)
  ≲⟨ bind-monoˡ-≤⁻ (step (F _) q ∘ ret ∘ f .bot) (e .square a) ⟩
    bind {B .₀} (F _) (bind (F _) (Φ A a) (step (F _) p ∘ ret ∘ e .bot)) (step (F _) q ∘ ret ∘ f .bot)
  ≡⟨ step-ret-congˡ _ (Eq.trans (+-assoc _ _ _) (Eq.cong (_ +_) (Eq.sym s))) ⟩
    step (F _) (A .Φᶜ a + r) (ret (f .bot (e .bot a)))
  ∎


-- Define tensor first, which is needed for contexts
_⊗_ : PotentialFunction → PotentialFunction → PotentialFunction
_⊗_ A B .₀ = A .₀ ×⁺ B .₀
_⊗_ A B .Φᶜ (a , b) = (A .Φᶜ a) + (B .Φᶜ b)

⊤ : PotentialFunction
⊤ .₀ = unit
⊤ .Φᶜ triv = zero


Tensorfy : List PotentialFunction → PotentialFunction
Tensorfy Δ = List.foldr _⊗_ ⊤ Δ

MultiSquare : List PotentialFunction → ℂ → PotentialFunction → Set
MultiSquare Δ = Square (Tensorfy Δ)

constᵍ : ∀ {A} → (a : val (A .₀)) → MultiSquare [] (A .Φᶜ a) A
constᵍ a .top triv = ret a
constᵍ a .bot triv = a
constᵍ _ .square triv = ≤⁻-refl


permute : ∀ {Δ Δ₁ Δ₂} → Δ ≡ Δ₁ ⊔ Δ₂ → val (Tensorfy Δ .₀) → val (Tensorfy Δ₁ .₀) × val (Tensorfy Δ₂ .₀)
permute base triv = triv , triv
permute (left s) (a , δ) =
  let δ₁ , δ₂ = permute s δ in
  (a , δ₁) , δ₂
permute (right s) (a , δ) =
  let δ₁ , δ₂ = permute s δ in
  δ₁ , (a , δ₂)

permute-Φ : ∀ {Δ Δ₁ Δ₂}
  → (s : Δ ≡ Δ₁ ⊔ Δ₂)
  → (δ : val (Tensorfy Δ .₀))
  → (
    let δ₁ , δ₂ = permute s δ in
    Tensorfy Δ₁ .Φᶜ δ₁ + Tensorfy Δ₂ .Φᶜ δ₂
  ) ≡ (Tensorfy Δ .Φᶜ δ)
permute-Φ base δ = +-identityˡ _
permute-Φ (left {A = A} s) (a , δ) = Eq.trans (+-assoc _ _ _) (Eq.cong (A .Φᶜ a +_) (permute-Φ s δ))
permute-Φ (right {A = A} s) (a , δ) =
  let helper a b c =
        let open SolverHelp in let open Vec in
        prove 3 (v₂ ⊕ (v₁ ⊕ v₃)) (v₁ ⊕ (v₂ ⊕ v₃))
        (a ∷ b ∷ c ∷ [])
  in
  Eq.trans (helper _ _ _) (Eq.cong (A .Φᶜ a +_) (permute-Φ s δ))


-- cut
_⨾_⋎_⨾□ᵐ_ : ∀ {Δ Δ₁ Δ₂ q q₁ q₂ A B} → _≡_⊔_ Δ Δ₁ Δ₂ → q ≡ q₁ + q₂ → MultiSquare Δ₁ q₁ A → MultiSquare (A ∷ Δ₂) q₂ B → MultiSquare Δ q B
(s ⨾ t ⋎ e ⨾□ᵐ f) .top δ =
  let δ₁ , δ₂ = permute s δ in
  bind (F _) (e .top δ₁) (λ a → f .top (a , δ₂))
(s ⨾ t ⋎ e ⨾□ᵐ f) .bot δ =
  let δ₁ , δ₂ = permute s δ in
  f .bot (e .bot δ₁ , δ₂)
(_⨾_⋎_⨾□ᵐ_ {Δ} {Δ₁} {Δ₂} {q} {q₁} {q₂} {A} {B} s t e f) .square δ =
  let δ₁ , δ₂ = permute s δ in
  let helper a b c d =
        let open SolverHelp in let open Vec in
        prove 4 ((v₁ ⊕ v₂) ⊕ (v₃ ⊕ v₄)) ((v₁ ⊕ v₃) ⊕ (v₂ ⊕ v₄))
        (a ∷ b ∷ c ∷ d ∷ [])
  in
  let open ≤⁻-Reasoning (F _) in
  begin
    bind (F _) (e .top δ₁) (λ a → bind (F _) (f .top (a , δ₂)) (Φ B))
  ≲⟨ bind-monoʳ-≤⁻ (e .top δ₁) (λ a → f .square (a , δ₂)) ⟩
    bind (F _) (e .top δ₁) (λ a → step (F _) (A .Φᶜ a + Tensorfy Δ₂ .Φᶜ δ₂ + q₂) (ret (f .bot (a , δ₂))))
  ≡⟨ Eq.cong (bind (F _) (e .top δ₁)) (funext (λ a → step-ret-congˡ _ (+-assoc _ _ _))) ⟩
    bind (F _) (bind (F _) (e .top δ₁) (Φ A)) (λ a → step (F _) (Tensorfy Δ₂ .Φᶜ δ₂ + q₂) (ret (f .bot (a , δ₂))))
  ≲⟨ bind-monoˡ-≤⁻ (λ a' → step (F _) _ (ret _)) (e .square δ₁) ⟩
    bind {A .₀} (F _)
      (step (F _) (Tensorfy Δ₁ .Φᶜ δ₁ + q₁) (ret (e .bot δ₁)))
      (λ a → step (F _) (Tensorfy Δ₂ .Φᶜ δ₂ + q₂) (ret (f .bot (a , δ₂))))
  ≡⟨⟩
    step (F _)
      (Tensorfy Δ₁ .Φᶜ δ₁ + q₁ + (Tensorfy Δ₂ .Φᶜ δ₂ + q₂))
      (ret (f .bot (e .bot δ₁ , δ₂)))
  ≡⟨ step-ret-congˡ _ (helper _ _ _ _) ⟩
    step (F _)
      ((Tensorfy Δ₁ .Φᶜ δ₁ + Tensorfy Δ₂ .Φᶜ δ₂) + (q₁ + q₂))
      (ret (f .bot (e .bot δ₁ , δ₂)))
  ≡⟨ step-ret-congˡ _ (Eq.cong₂ _+_ (permute-Φ s δ) (Eq.sym t)) ⟩
    step (F _)
      (Tensorfy Δ .Φᶜ δ + q)
      (ret (f .bot (e .bot δ₁ , δ₂)))
  ∎


giralf-list : PotentialFunction → PotentialFunction
giralf-list A .₀ = list (A .₀)
giralf-list A .Φᶜ = foldr (λ h ih → (A .Φᶜ h) + ih) zero


open Giralf
giralf : Giralf

giralf .𝓒 = PotentialFunction
giralf ._⨾_⊢_ = MultiSquare

giralf .idᵍ {q} {A} = Eq.sym (+-identityˡ _) ⋎ lemma ⨾□ weaken-pot q
  where
    lemma : MultiSquare [ A ] zero A
    lemma .top (a , _) = ret a
    lemma .bot (a , _) = a
    lemma .square (a , _) = ≤⁻-reflexive (step-ret-congˡ a (Eq.sym (+-identityʳ _)))


-- Charge effect
giralf .charge {A = A} p t e = t ⋎ e ⨾□ lemma
  where
    lemma : Square A p A
    lemma .top = step (F _) p ∘ ret
    lemma .bot = Function.id
    lemma .square a = ≤⁻-reflexive (step-ret-congˡ _ (+-comm _ _))


-- F type
giralf .Fᵍ X .₀ = X
giralf .Fᵍ X .Φᶜ _ = zero
giralf .retᵍ {q} {X} x = Eq.sym (+-identityˡ _) ⋎ constᵍ x ⨾□ weaken-pot q
giralf .bindᵍ {Δ₂ = Δ₂} {q₂ = q₂} {X} {A} s t e e' = s ⨾ t ⋎ e ⨾□ᵐ lemma
  where
    lemma : MultiSquare ((giralf .Fᵍ X) ∷ Δ₂) q₂ A
    lemma .top (x , δ₂) = e' x .top δ₂
    lemma .bot (x , δ₂) = e' x .bot δ₂
    lemma .square (x , δ₂) = ≤⁻-trans (e' x .square δ₂) (≤⁻-reflexive (step-ret-congˡ _ (Eq.cong (_+ q₂) (Eq.sym (+-identityˡ _)))))


-- Potential
giralf ._⋊ᵍ_ p A .₀ = A .₀
giralf ._⋊ᵍ_ p A .Φᶜ a = p + A .Φᶜ a
giralf .store {A = A} p t e = t ⋎ e ⨾□ store-square
  where
    store-square : Square A p (giralf ._⋊ᵍ_ p A)
    store-square .top = ret
    store-square .bot = Function.id
    store-square .square a = ≤⁻-reflexive (step-ret-congˡ _ (+-comm _ _))
giralf .release {Δ₂ = Δ₂} {p} {q₂ = q₂} {A} {B} s t e e' = s ⨾ t ⋎ e ⨾□ᵐ lemma
  where
    lemma : MultiSquare ((giralf ._⋊ᵍ_ p A) ∷ Δ₂) q₂ B
    lemma .top = e' .top
    lemma .bot = e' .bot
    lemma .square (a , δ₂) =
      let helper a b c d =
            let open SolverHelp in let open Vec in
            prove 4 ((v₁ ⊕ v₂) ⊕ (v₃ ⊕ v₄)) (((v₃ ⊕ v₁) ⊕ v₂) ⊕ v₄)
            (a ∷ b ∷ c ∷ d ∷ [])
      in
      let open ≤⁻-Reasoning (F _) in
      begin
        bind (F _) (e' .top (a , δ₂)) (Φ B)
      ≲⟨ e' .square (a , δ₂) ⟩
         step (F _) (A .Φᶜ a + Tensorfy Δ₂ .Φᶜ δ₂ + (p + q₂)) (ret (e' .bot (a , δ₂)))
      ≡⟨ step-ret-congˡ _ (helper _ _ _ _) ⟩
        step (F _) (p + A .Φᶜ a + Tensorfy Δ₂ .Φᶜ δ₂ + q₂) (ret (e' .bot (a , δ₂)))
      ∎

-- Void and Sum
giralf .⊥ᵍ .₀ = ⊥⁺
giralf .⊥ᵍ .Φᶜ ()
giralf .absurdᵍ {C = C} e = Eq.sym (+-identityʳ _) ⋎ e ⨾□ lemma
  where
    lemma : Square (giralf .⊥ᵍ) zero C
    lemma .top ()
    lemma .bot ()
    lemma .square ()

giralf ._⊎ᵍ_ A B .₀ = A .₀ ⊎⁺ B .₀
giralf ._⊎ᵍ_ A B .Φᶜ = [ A .Φᶜ , B .Φᶜ ]′
giralf .inj₁ᵍ e .top δ = bind (F _) (e .top δ) λ b → ret (inj₁ b)
giralf .inj₁ᵍ e .bot = inj₁ ∘ e .bot
giralf .inj₁ᵍ e .square δ = bind-monoˡ-≤⁻ (ret ∘ inj₁) (e .square δ)
giralf .inj₂ᵍ e .top δ = bind (F _) (e .top δ) λ b → ret (inj₂ b)
giralf .inj₂ᵍ e .bot = inj₂ ∘ e .bot
giralf .inj₂ᵍ e .square δ = bind-monoˡ-≤⁻ (ret ∘ inj₂) (e .square δ)
giralf .caseᵍ {Δ₂ = Δ₂} {q₂ = q₂} {A} {B} {C} s t e e₁ e₂ = s ⨾ t ⋎ e ⨾□ᵐ lemma
  where
    lemma : MultiSquare ((giralf ._⊎ᵍ_ A B) ∷ Δ₂) q₂ C
    lemma .top (inj₁ a , δ₂) = e₁ .top (a , δ₂)
    lemma .top (inj₂ b , δ₂) = e₂ .top (b , δ₂)
    lemma .bot (inj₁ a , δ₂) = e₁ .bot (a , δ₂)
    lemma .bot (inj₂ b , δ₂) = e₂ .bot (b , δ₂)
    lemma .square (inj₁ a , δ₂) = e₁ .square (a , δ₂)
    lemma .square (inj₂ b , δ₂) = e₂ .square (b , δ₂)


-- Top and Tensor Product
giralf .⊤ᵍ = ⊤
giralf .trivᵍ {q} = Eq.sym (+-identityˡ _) ⋎ constᵍ triv ⨾□ weaken-pot q
giralf .checkᵍ {Δ₂ = Δ₂} {q₂ = q₂} {C} s t e e' = s ⨾ t ⋎ e ⨾□ᵐ lemma
  where
    lemma : MultiSquare (⊤ ∷ Δ₂) q₂ C
    lemma .top (triv , δ₂) = e' .top δ₂
    lemma .bot (triv , δ₂) = e' .bot δ₂
    lemma .square (triv , δ₂) = ≤⁻-trans (e' .square δ₂) (≤⁻-reflexive (step-ret-congˡ _ (Eq.cong (_+ q₂) (Eq.sym (+-identityˡ _)))))

giralf ._⊗ᵍ_ = _⊗_
giralf .tensorᵍ {Δ₁ = Δ₁} {q₁ = q₁} {A = A} {B} s t e₁ e₂ = (switch s) ⨾ (Eq.trans t (+-comm _ _)) ⋎ e₂ ⨾□ᵐ lemma
  where
    lemma : MultiSquare (B ∷ Δ₁) q₁ (A ⊗ B)
    lemma .top (b , δ₁) = bind (F _) (e₁ .top δ₁) λ a → ret (a , b)
    lemma .bot (b , δ₁) = (e₁ .bot δ₁ , b)
    lemma .square (b , δ₁) =
      let helper a b c =
            let open SolverHelp in let open Vec in
            prove 3 ((v₁ ⊕ v₂) ⊕ v₃) ((v₃ ⊕ v₁) ⊕ v₂) (a ∷ b ∷ c ∷ [])
      in
      let open ≤⁻-Reasoning (F _) in
      begin
        bind (F _) (e₁ .top δ₁) (λ a → Φ (A ⊗ B) (a , b))
      ≡⟨⟩
        bind (F _)
          (bind (F _) (e₁ .top δ₁) (Φ A))
          (λ a → step (F _) (B .Φᶜ b) (ret (a , b)))
      ≲⟨ bind-monoˡ-≤⁻ (λ b → step (F _) _ (ret _)) (e₁ .square δ₁) ⟩
        bind (F _)
          (step (F (A .₀)) (Tensorfy Δ₁ .Φᶜ δ₁ + q₁) (ret (e₁ .bot δ₁)))
          (λ a → step (F _) (B .Φᶜ b) (ret (a , b)))
      ≡⟨ step-ret-congˡ _ (helper _ _ _) ⟩
        step (F _) (B .Φᶜ b + Tensorfy Δ₁ .Φᶜ δ₁ + q₁) (ret (e₁ .bot δ₁ , b))
      ∎
giralf .splitᵍ {Δ₂ = Δ₂} {q₂ = q₂} {A} {B} {C} s t e e' = s ⨾ t ⋎ e ⨾□ᵐ lemma
  where
    lemma : MultiSquare ((giralf ._⊗ᵍ_ A B) ∷ Δ₂) q₂ C
    lemma .top ((a , b) , δ₂) = e' .top (a , (b , δ₂))
    lemma .bot ((a , b) , δ₂) = e' .bot (a , (b , δ₂))
    lemma .square ((a , b) , δ₂) =
      ≤⁻-trans (e' .square (a , (b , δ₂))) (≤⁻-reflexive (step-ret-congˡ _ (Eq.cong (_+ q₂) (Eq.sym (+-assoc _ _ _)))))


-- Lists
giralf .listᵍ = giralf-list
giralf .nilᵍ {q} = Eq.sym (+-identityˡ _) ⋎ constᵍ [] ⨾□ weaken-pot q
giralf .consᵍ {Δ = Δ} {A = A} s t eₕ eₜ = (Eq.sym (+-identityʳ _)) ⋎ (giralf .tensorᵍ s t eₕ eₜ) ⨾□ lemma
  where
    lemma : Square (A ⊗ giralf-list A) zero (giralf-list A)
    lemma .top (h , t) = ret (h ∷ t)
    lemma .bot (h , t) = h ∷ t
    lemma .square (h , t) = ≤⁻-refl
giralf .foldrᵍ {A = A} {B = B} e e[] e∷ = (Eq.sym (+-identityʳ _)) ⋎ e ⨾□ lemma
  where
    lemma : Square (giralf-list A) zero B
    lemma .top [] = e[] .top triv
    lemma .top (h ∷ t) = bind (F _) (lemma .top t) (λ b' → e∷ .top (b' , h , triv))
    lemma .bot [] = e[] .bot triv
    lemma .bot (h ∷ t) = e∷ .bot (lemma .bot t , h , triv)
    lemma .square [] = e[] .square triv
    lemma .square (h ∷ t) =
      let open ≤⁻-Reasoning (F _) in
      begin
        (
          bind (F _) (lemma .top t) λ b →
          bind (F _) (e∷ .top (b , h , triv)) (Φ B)
        )
      ≲⟨ bind-monoʳ-≤⁻ (lemma .top t) (λ b → e∷ .square (b , h , triv)) ⟩
        (
          bind (F _) (lemma .top t) λ b →
          bind (F _) (Φ (B ⊗ (A ⊗ ⊤)) (b , h , triv)) (ret ∘ e∷ .bot)
        )
      ≡⟨ Eq.cong (bind (F _) (lemma .top t)) (funext λ b → step-ret-congˡ _ (Eq.cong (B .Φᶜ b +_) (+-identityʳ _))) ⟩
        bind (F _)
          (bind (F _) (lemma .top t) (Φ B))
          (
            λ b' →
            bind (F _) (Φ A h) λ h' →
            ret (e∷ .bot (b' , h' , triv))
          )
      ≲⟨ bind-monoˡ-≤⁻ (λ b' → bind (F _) (Φ A h) (λ h' → ret (e∷ .bot (b' , h' , triv)))) (lemma .square t) ⟩
        bind (F _)
          (bind (F (B .₀)) (Φ (giralf .listᵍ A) t) (ret ∘ lemma .bot))
          (
            λ b' →
            bind (F _) (Φ A h) λ h' →
            ret (e∷ .bot (b' , h' , triv))
          )
      ≡⟨ step-ret-congˡ _ (+-comm _ _) ⟩
        bind (F _)
          (Φ (giralf .listᵍ A) (h ∷ t))
          (ret ∘ lemma .bot)
      ∎
