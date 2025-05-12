{-# OPTIONS --rewriting --allow-unsolved-metas #-}

open import Algebra.Cost

module Calf.Giralf (costMonoid : CostMonoid) where

open CostMonoid costMonoid


open import Calf.Prelude
open import Calf.CBPV
open import Calf.Directed
open import Calf.Step costMonoid
open import Calf.Data.Product
open import Calf.Data.Sum as Sum
open import Calf.Data.List


open import Function using (_∘_; const)


open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
postulate
  zero/min : (c : ℂ) → zero ≤ c
  +-comm : (a : ℂ) → (b : ℂ) → a + b ≡ b + a

open import Algebra using (CommutativeMonoid)
open import Level using (0ℓ)

comm-monoid : CommutativeMonoid 0ℓ 0ℓ
comm-monoid = record
  { Carrier = ℂ
  ; _≈_  = _≡_
  ; _∙_ = _+_
  ; ε = zero
  ; isCommutativeMonoid = record { isMonoid = isMonoid ; comm = +-comm }
  }

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
    all-right : {Δ : List E} → Δ ≡ [] ⊔ Δ
    left : {Δ Δ₁ Δ₂ : List E} (A : E) → Δ ≡ Δ₁ ⊔ Δ₂ → (A ∷ Δ) ≡ (A ∷ Δ₁) ⊔ Δ₂
    switch : {Δ Δ₁ Δ₂ : List E} → Δ ≡ Δ₁ ⊔ Δ₂ → Δ ≡ Δ₂ ⊔ Δ₁

  right : {Δ Δ₁ Δ₂ : List E} (A : E) → Δ ≡ Δ₁ ⊔ Δ₂ → (A ∷ Δ) ≡ Δ₁ ⊔ (A ∷ Δ₂)
  right A s = switch (left A (switch s))

  all-left : {Δ : List E} → Δ ≡ Δ ⊔ []
  all-left = switch all-right


record Giralf : Set₁ where
  𝓥 : Set
  𝓥 = tp⁺

  valᵍ : 𝓥 → Set
  valᵍ = val

  field
    𝓒 : Set
    _⨾_⊢_ : List 𝓒 → ℂ → 𝓒 → Set

    idᵍ : ∀ {A} → [ A ] ⨾ zero ⊢ A

  _≡_⊔_ : List 𝓒 → List 𝓒 → List 𝓒 → Set
  _≡_⊔_ = Perm-Split._≡_⊔_

  cmpᵍ : 𝓒 → Set
  cmpᵍ A = [] ⨾ zero ⊢ A

  _⊸_ : 𝓒 → 𝓒 → 𝓥
  A ⊸ B = meta⁺ ([ A ] ⨾ zero ⊢ B)

  Uᵍ : 𝓒 → 𝓥
  Uᵍ A = meta⁺ (cmpᵍ A)

  field
    Fᵍ : 𝓥 → 𝓒
    retᵍ : ∀ {X} → valᵍ X → cmpᵍ (Fᵍ X)
    bindᵍ : ∀ {Δ Δ₁ Δ₂ q q₁ q₂ X A}
      → Δ ≡ Δ₁ ⊔ Δ₂
      → q ≡ q₁ + q₂
      → Δ₁ ⨾ q₁ ⊢ (Fᵍ X)
      → (valᵍ X → Δ₂ ⨾ q₂ ⊢ A)
      → Δ ⨾ q ⊢ A

    charge : ∀ {Δ r q A} (p : ℂ)
      → r ≡ q + p
      → Δ ⨾ q ⊢ A
      → Δ ⨾ r ⊢ A
    weaken : ∀ {Δ r q p A}
      → r ≡ q + p
      → Δ ⨾ q ⊢ A
      → Δ ⨾ r ⊢ A

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
    trivᵍ : [] ⨾ zero ⊢ ⊤ᵍ

    _⊗ᵍ_ : 𝓒 → 𝓒 → 𝓒
    tensorᵍ : ∀ {Δ Δ₁ Δ₂ q q₁ q₂ A B}
      → Δ ≡ Δ₁ ⊔ Δ₂
      → q ≡ q₁ + q₂
      → Δ₁ ⨾ q₁ ⊢ B
      → Δ₂ ⨾ q₂ ⊢ A
      → Δ ⨾ q ⊢ (A ⊗ᵍ B)
    splitᵍ : ∀ {Δ Δ₁ Δ₂ q q₁ q₂ A B C}
      → Δ ≡ Δ₁ ⊔ Δ₂
      → q ≡ q₁ + q₂
      → Δ₁ ⨾ q₁ ⊢ (A ⊗ᵍ B)
      → (A ∷ B ∷ Δ₂) ⨾ q₂ ⊢ C
      → Δ ⨾ q ⊢ C

    listᵍ : 𝓒 → 𝓒
    nilᵍ : ∀ {A} → cmpᵍ (listᵍ A)
    consᵍ : ∀ {Δ Δ₁ Δ₂ q q₁ q₂ A}
      → Δ ≡ Δ₁ ⊔ Δ₂
      → q ≡ q₁ + q₂
      → Δ₂ ⨾ q₂ ⊢ A
      → Δ₁ ⨾ q₁ ⊢ listᵍ A
      → Δ ⨾ q ⊢ listᵍ A
    foldrᵍ : ∀ {Δ q A B}
      → Δ ⨾ q ⊢ listᵍ A
      → cmpᵍ B
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


id□ : ∀ {A} → Square A zero A
id□ .top = ret
id□ .bot = Function.id
id□ .square a = ≤⁻-refl

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
  ≡⟨ Eq.cong (λ c → step (F _) c (ret _)) (Eq.trans (+-assoc _ _ _) (Eq.cong (_ +_) (Eq.sym s))) ⟩
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


permute : ∀ {Δ Δ₁ Δ₂} → Perm-Split._≡_⊔_ Δ Δ₁ Δ₂ → val (Tensorfy Δ .₀) → val (Tensorfy Δ₁ .₀) × val (Tensorfy Δ₂ .₀)
permute Perm-Split.all-right δ = triv , δ
permute (Perm-Split.left A s) (a , δ) =
  let δ₁ , δ₂ = permute s δ in
  (a , δ₁) , δ₂
permute (Perm-Split.switch s) δ =
  let δ₁ , δ₂ = permute s δ in
  δ₂ , δ₁


permute-Φ : ∀ {Δ Δ₁ Δ₂}
  → (s : Perm-Split._≡_⊔_ Δ Δ₁ Δ₂)
  → (δ : val (Tensorfy Δ .₀))
  → (
    let δ₁ , δ₂ = permute s δ in
    Tensorfy Δ₁ .Φᶜ δ₁ + Tensorfy Δ₂ .Φᶜ δ₂
  ) ≡ (Tensorfy Δ .Φᶜ δ)
permute-Φ Perm-Split.all-right δ = +-identityˡ _
permute-Φ (Perm-Split.left A s) (a , δ) = Eq.trans (+-assoc _ _ _) (Eq.cong (A .Φᶜ a +_) (permute-Φ s δ))
permute-Φ (Perm-Split.switch s) δ = Eq.trans (+-comm _ _) (permute-Φ s δ)


-- cut
_⨾_⋎_⨾□ᵐ_ : ∀ {Δ Δ₁ Δ₂ q q₁ q₂ A B} → Perm-Split._≡_⊔_ Δ Δ₁ Δ₂ → q ≡ q₁ + q₂ → MultiSquare Δ₁ q₁ A → MultiSquare (A ∷ Δ₂) q₂ B → MultiSquare Δ q B
(s ⨾ t ⋎ e ⨾□ᵐ f) .top δ =
  let δ₁ , δ₂ = permute s δ in
  bind (F _) (e .top δ₁) (λ a → f .top (a , δ₂))
(s ⨾ t ⋎ e ⨾□ᵐ f) .bot δ =
  let δ₁ , δ₂ = permute s δ in
  f .bot (e .bot δ₁ , δ₂)
(_⨾_⋎_⨾□ᵐ_ {Δ} {Δ₁} {Δ₂} {q} {q₁} {q₂} {A} {B} s t e f) .square δ =
  let δ₁ , δ₂ = permute s δ in
  -- let helper a b c d =
  --       -- torture
  --       let open Eq.≡-Reasoning in
  --       begin
  --         a + b + (c + d)
  --       ≡⟨ +-assoc _ _ _ ⟩
  --         a + (b + (c + d))
  --       ≡⟨ Eq.cong (a +_) (Eq.sym (+-assoc _ _ _)) ⟩
  --         a + (b + c + d)
  --       ≡⟨ Eq.cong (a +_) (Eq.cong (_+ d) (+-comm _ _)) ⟩
  --         a + (c + b + d)
  --       ≡⟨ Eq.cong (a +_) (+-assoc _ _ _) ⟩
  --         a + (c + (b + d))
  --       ≡⟨ Eq.sym (+-assoc _ _ _) ⟩
  --         (a + c) + (b + d)
  --       ∎
  -- in
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
  ≡⟨ Eq.cong (bind (F _) (e .top δ₁)) (funext (λ a → Eq.cong (λ c → step (F _) c (ret (f .bot (a , δ₂)))) (+-assoc _ _ _))) ⟩
    bind (F _) (bind (F _) (e .top δ₁) (Φ A)) (λ a → step (F _) (Tensorfy Δ₂ .Φᶜ δ₂ + q₂) (ret (f .bot (a , δ₂))))
  ≲⟨ bind-monoˡ-≤⁻ (λ a' → step (F _) _ (ret _)) (e .square δ₁) ⟩
    bind {A .₀} (F _)
      (step (F _) (Tensorfy Δ₁ .Φᶜ δ₁ + q₁) (ret (e .bot δ₁)))
      (λ a → step (F _) (Tensorfy Δ₂ .Φᶜ δ₂ + q₂) (ret (f .bot (a , δ₂))))
  ≡⟨⟩
    step (F _)
      (Tensorfy Δ₁ .Φᶜ δ₁ + q₁ + (Tensorfy Δ₂ .Φᶜ δ₂ + q₂))
      (ret (f .bot (e .bot δ₁ , δ₂)))
  ≡⟨ Eq.cong (λ c → step (F _) c (ret (f .bot (e .bot δ₁ , δ₂)))) (helper _ _ _ _) ⟩
    step (F _)
      ((Tensorfy Δ₁ .Φᶜ δ₁ + Tensorfy Δ₂ .Φᶜ δ₂) + (q₁ + q₂))
      (ret (f .bot (e .bot δ₁ , δ₂)))
  ≡⟨ Eq.cong (λ c → step (F _) c (ret (f .bot (e .bot δ₁ , δ₂)))) (Eq.cong₂ _+_ (permute-Φ s δ) (Eq.sym t)) ⟩
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
-- giralf ._≡_⊔_ = Perm-Split._≡_⊔_

-- Can we use id□ somehow instead?
giralf .idᵍ .top (a , _) = ret a
giralf .idᵍ .bot (a , _) = a
giralf .idᵍ .square _ = ≤⁻-reflexive (Eq.cong (λ c → step (F _) c (ret _)) (Eq.sym (+-identityʳ _)))

giralf .Fᵍ X .₀ = X
giralf .Fᵍ X .Φᶜ _ = zero
giralf .retᵍ x .top triv = ret x
giralf .retᵍ x .bot triv = x
giralf .retᵍ x .square triv = ≤⁻-refl
giralf .bindᵍ {Δ₂ = Δ₂} {q₂ = q₂} {X} {A} s t e e' = s ⨾ t ⋎ e ⨾□ᵐ lemma
  where
    lemma : MultiSquare ((giralf .Fᵍ X) ∷ Δ₂) q₂ A
    lemma .top (x , δ₂) = e' x .top δ₂
    lemma .bot (x , δ₂) = e' x .bot δ₂
    lemma .square (x , δ₂) = ≤⁻-trans (e' x .square δ₂) (≤⁻-reflexive (Eq.cong (λ c → step (F _) c (ret _)) (Eq.cong (_+ q₂) (Eq.sym (+-identityˡ _)))))

giralf .charge {A = A} p t e = t ⋎ e ⨾□ step-square
  where
    step-square : Square A p A
    step-square .top = step (F _) p ∘ ret
    step-square .bot = Function.id
    step-square .square a = ≤⁻-reflexive (Eq.cong (λ c → step (F _) c (ret _)) (+-comm _ _))

giralf .weaken {p = p} {A = A} t e = t ⋎ e ⨾□ weaken-square
  where
    weaken-square : Square A p A
    weaken-square .top = ret
    weaken-square .bot = Function.id
    weaken-square .square a = bind-monoʳ-≤⁻ (Φ A a) (λ a → step-monoˡ-≤⁻ (ret a) (zero/min p))

giralf ._⋊ᵍ_ p A .₀ = A .₀
giralf ._⋊ᵍ_ p A .Φᶜ a = p + A .Φᶜ a
giralf .store {A = A} p t e = t ⋎ e ⨾□ store-square
  where
    store-square : Square A p (giralf ._⋊ᵍ_ p A)
    store-square .top = ret
    store-square .bot = Function.id
    store-square .square a = ≤⁻-reflexive (Eq.cong (λ c → step (F _) c (ret _)) (+-comm _ _))
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
      ≡⟨ Eq.cong (λ c → step (F _) c (ret _)) (helper _ _ _ _) ⟩
        step (F _) (p + A .Φᶜ a + Tensorfy Δ₂ .Φᶜ δ₂ + q₂) (ret (e' .bot (a , δ₂)))
      ∎

giralf ._⊎ᵍ_ A B .₀ = A .₀ ⊎⁺ B .₀
giralf ._⊎ᵍ_ A B .Φᶜ = [ A .Φᶜ , B .Φᶜ ]′
giralf .inj₁ᵍ e .top δ = bind (F _) (e .top δ) λ b → ret (inj₁ b)
giralf .inj₁ᵍ e .bot = inj₁ ∘ e .bot
giralf .inj₁ᵍ e .square δ = bind-monoˡ-≤⁻ (ret ∘ inj₁) (e .square δ)
giralf .inj₂ᵍ e .top δ = bind (F _) (e .top δ) λ b → ret (inj₂ b)
giralf .inj₂ᵍ e .bot = inj₂ ∘ e .bot
giralf .inj₂ᵍ e .square δ = bind-monoˡ-≤⁻ (ret ∘ inj₂) (e .square δ)
giralf .caseᵍ {Δ₂ = Δ₂} {q₂ = q₂} {A} {B} {C} s t e e₁ e₂ = s ⨾ t ⋎  e ⨾□ᵐ lemma
  where
    lemma : MultiSquare ((giralf ._⊎ᵍ_ A B) ∷ Δ₂) q₂ C
    lemma .top (inj₁ a , δ₂) = e₁ .top (a , δ₂)
    lemma .top (inj₂ b , δ₂) = e₂ .top (b , δ₂)
    lemma .bot (inj₁ a , δ₂) = e₁ .bot (a , δ₂)
    lemma .bot (inj₂ b , δ₂) = e₂ .bot (b , δ₂)
    lemma .square (inj₁ a , δ₂) = e₁ .square (a , δ₂)
    lemma .square (inj₂ b , δ₂) = e₂ .square (b , δ₂)


giralf .⊤ᵍ = ⊤
giralf .trivᵍ = id□

giralf ._⊗ᵍ_ = _⊗_
giralf .tensorᵍ {Δ₂ = Δ₂} {q₂ = q₂} {A} {B} s t e₁ e₂ = s ⨾ t ⋎ e₁ ⨾□ᵐ lemma
  where
    lemma : MultiSquare (B ∷ Δ₂) q₂ (A ⊗ B)
    lemma .top (b , δ₂) = bind (F _) (e₂ .top δ₂) λ a → ret (a , b)
    lemma .bot (b , δ₂) = (e₂ .bot δ₂ , b)
    lemma .square (b , δ₂) =
      let helper a b c =
            let open SolverHelp in let open Vec in
            prove 3 ((v₁ ⊕ v₂) ⊕ v₃) ((v₃ ⊕ v₁) ⊕ v₂) (a ∷ b ∷ c ∷ [])
      in
      let open ≤⁻-Reasoning (F _) in
      begin
        bind (F _) (e₂ .top δ₂) (λ a → Φ (A ⊗ B) (a , b))
      ≡⟨⟩
        bind (F _)
          (bind (F _) (e₂ .top δ₂) (Φ A))
          (λ a → step (F _) (B .Φᶜ b) (ret (a , b)))
      ≲⟨ bind-monoˡ-≤⁻ (λ b → step (F _) _ (ret _)) (e₂ .square δ₂) ⟩
        bind (F _)
          (step (F (A .₀)) (Tensorfy Δ₂ .Φᶜ δ₂ + q₂) (ret (e₂ .bot δ₂)))
          (λ a → step (F _) (B .Φᶜ b) (ret (a , b)))
      ≡⟨ Eq.cong (λ c → step (F _) c (ret _)) (helper _ _ _) ⟩
        step (F _) (B .Φᶜ b + Tensorfy Δ₂ .Φᶜ δ₂ + q₂) (ret (e₂ .bot δ₂ , b))
      ∎
giralf .splitᵍ {Δ₂ = Δ₂} {q₂ = q₂} {A} {B} {C} s t e e' = s ⨾ t ⋎ e ⨾□ᵐ lemma
  where
    lemma : MultiSquare ((giralf ._⊗ᵍ_ A B) ∷ Δ₂) q₂ C
    lemma .top ((a , b) , δ₂) = e' .top (a , (b , δ₂))
    lemma .bot ((a , b) , δ₂) = e' .bot (a , (b , δ₂))
    lemma .square ((a , b) , δ₂) =
      ≤⁻-trans (e' .square (a , (b , δ₂))) (≤⁻-reflexive (Eq.cong (λ c → step (F _) c (ret _)) (Eq.cong (_+ q₂) (Eq.sym (+-assoc _ _ _)))))


giralf .listᵍ = giralf-list
giralf .nilᵍ .top triv = ret []
giralf .nilᵍ .bot triv = []
giralf .nilᵍ .square triv = ≤⁻-refl
giralf .consᵍ {Δ = Δ} {A = A} s t eₕ eₜ = (Eq.sym (+-identityʳ _)) ⋎ (giralf .tensorᵍ s t eₜ eₕ) ⨾□ lemma
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
      ≡⟨ Eq.cong (bind (F _) (lemma .top t)) (funext λ b → Eq.cong (λ c → step (F _) c (ret _)) (Eq.cong (B .Φᶜ b +_) (+-identityʳ _))) ⟩
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
      ≡⟨ Eq.cong (λ c → step (F _) c (ret (lemma .bot (h ∷ t)))) (+-comm _ _) ⟩
        bind (F _)
          (Φ (giralf .listᵍ A) (h ∷ t))
          (ret ∘ lemma .bot)
      ∎
