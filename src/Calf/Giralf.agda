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
module Permutation where
  data _≡_⊔_ {E : Set} : List E → List E → List E → Set where
    all_right : {Δ : List E} → Δ ≡ [] ⊔ Δ
    left : {Δ Δ₁ Δ₂ : List E} (A : E) → Δ ≡ Δ₁ ⊔ Δ₂ → (A ∷ Δ) ≡ (A ∷ Δ₁) ⊔ Δ₂
    swapa : {Δ Δ₁ Δ₂ : List E} → Δ ≡ Δ₁ ⊔ Δ₂ → Δ ≡ Δ₂ ⊔ Δ₁


record Giralf : Set₁ where
  𝓥 : Set
  𝓥 = tp⁺

  valᵍ : 𝓥 → Set
  valᵍ = val

  field
    𝓒 : Set
    _⨾_⊢_ : List 𝓒 → ℂ → 𝓒 → Set
    _≡_⊔_ : List 𝓒 → List 𝓒 → List 𝓒 → Set

    id : ∀ {A} → [ A ] ⨾ zero ⊢ A

    -- Fᵍ : 𝓥 → 𝓒
    -- retᵍ : ∀ {X} → valᵍ X → cmpᵍ (Fᵍ X)
    -- bindᵍ : ∀ {Δ q X A} → Δ ⨾ q ⊢ (Fᵍ X) → (valᵍ X → cmpᵍ A) → Δ ⨾ q ⊢ A

    -- Uᵍ : 𝓒 → 𝓥
    -- suspᵍ : {!   !}
    -- forceᵍ : {!   !}

  cmpᵍ : 𝓒 → Set
  cmpᵍ A = [] ⨾ zero ⊢ A

  _⊸_ : 𝓒 → 𝓒 → 𝓥
  A ⊸ B = meta⁺ ([ A ] ⨾ zero ⊢ B)

  field
    charge : ∀ {Δ q A} (p : ℂ) → Δ ⨾ q ⊢ A → Δ ⨾ q + p ⊢ A
    weaken : ∀ {Δ q p A} → Δ ⨾ q ⊢ A → Δ ⨾ q + p ⊢ A

    _⋊ᵍ_ : ℂ → 𝓒 → 𝓒
    store : ∀ {Δ q A} (p : ℂ) → Δ ⨾ q ⊢ A → Δ ⨾ q + p ⊢ (p ⋊ᵍ A)
    release : ∀ {Δ Δ₁ Δ₂ p q₁ q₂ A B}
      → Δ ≡ Δ₁ ⊔ Δ₂
      → Δ₁ ⨾ q₁ ⊢ (p ⋊ᵍ A)
      → (A ∷ Δ₂) ⨾ p + q₂ ⊢ B
      → Δ ⨾ q₁ + q₂ ⊢ B

    _⊎ᵍ_ : 𝓒 → 𝓒 → 𝓒
    inj₁ᵍ : ∀ {Δ q A B} → Δ ⨾ q ⊢ A → Δ ⨾ q ⊢ (A ⊎ᵍ B)
    inj₂ᵍ : ∀ {Δ q A B} → Δ ⨾ q ⊢ B → Δ ⨾ q ⊢ (A ⊎ᵍ B)
    caseᵍ : ∀ {Δ Δ₁ Δ₂ q₁ q₂ A B C}
      → Δ ≡ Δ₁ ⊔ Δ₂
      → Δ₁ ⨾ q₁ ⊢ (A ⊎ᵍ B)
      → (A ∷ Δ₂) ⨾ q₂ ⊢ C
      → (B ∷ Δ₂) ⨾ q₂ ⊢ C
      → Δ ⨾ q₁ + q₂ ⊢ C

    ⊤ᵍ : 𝓒
    trivᵍ : [] ⨾ zero ⊢ ⊤ᵍ

    _⊗ᵍ_ : 𝓒 → 𝓒 → 𝓒
    tensorᵍ : ∀ {Δ Δ₁ Δ₂ q₁ q₂ A B}
      → Δ ≡ Δ₁ ⊔ Δ₂
      → Δ₁ ⨾ q₁ ⊢ A
      → Δ₂ ⨾ q₂ ⊢ B
      → Δ ⨾ (q₁ + q₂) ⊢ (A ⊗ᵍ B)
    splitᵍ : ∀ {Δ Δ₁ Δ₂ q₁ q₂ A B C}
      → Δ ≡ Δ₁ ⊔ Δ₂
      → Δ₁ ⨾ q₁ ⊢ (A ⊗ᵍ B)
      → (A ∷ B ∷ Δ₂) ⨾ q₂ ⊢ C
      → Δ ⨾ q₁ + q₂ ⊢ C

    listᵍ : 𝓒 → 𝓒
    nilᵍ : ∀ {A} → cmpᵍ (listᵍ A)
    consᵍ : ∀ {Δ Δ₁ Δ₂ q₁ q₂ A}
      → Δ ≡ Δ₁ ⊔ Δ₂
      → Δ₁ ⨾ q₁ ⊢ A
      → Δ₂ ⨾ q₂ ⊢ listᵍ A
      → Δ ⨾ (q₁ + q₂) ⊢ listᵍ A
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

_⨾□_ : ∀ {A B C p q} → Square A p B → Square B q C → Square A (p + q) C
(e ⨾□ f) .top a = bind (F _) (e .top a) (f .top)
(e ⨾□ f) .bot = (f .bot) ∘ (e .bot)
(_⨾□_ {A} {B} {C} {p} {q} e f) .square a =
  let open ≤⁻-Reasoning (F _) in
  begin
    bind (F _) (e .top a) (λ b → bind (F _) (f .top b) (Φ C))
  ≲⟨ bind-monoʳ-≤⁻ (e .top a) (f .square) ⟩
    bind (F _) (e .top a) (λ b → bind (F _) (Φ B b) (step (F _) q ∘ ret ∘ f .bot))
  ≡⟨⟩
    bind (F _) (bind (F _) (e .top a) (Φ B)) (step (F _) q ∘ ret ∘ f .bot)
  ≲⟨ bind-monoˡ-≤⁻ (step (F _) q ∘ ret ∘ f .bot) (e .square a) ⟩
    bind {B .₀} (F _) (bind (F _) (Φ A a) (step (F _) p ∘ ret ∘ e .bot)) (step (F _) q ∘ ret ∘ f .bot)
  ≡⟨ Eq.cong (λ c → step (F _) c (ret _)) (+-assoc _ _ _) ⟩
    bind (F _) (Φ A a) (λ a' → step (F _) (p + q) (bind {B .₀} (F _) (ret (e .bot a')) (ret ∘ f .bot)))
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


permute : ∀ {Δ Δ₁ Δ₂} → Permutation._≡_⊔_ Δ Δ₁ Δ₂ → val (Tensorfy Δ .₀) → val (Tensorfy Δ₁ .₀) × val (Tensorfy Δ₂ .₀)
permute Permutation.all_right δ = triv , δ
permute (Permutation.left A s) (a , δ) =
  let δ₁ , δ₂ = permute s δ in
  (a , δ₁) , δ₂
permute (Permutation.swapa s) δ =
  let δ₁ , δ₂ = permute s δ in
  δ₂ , δ₁


permute-Φ : ∀ {Δ Δ₁ Δ₂}
  → (s : Permutation._≡_⊔_ Δ Δ₁ Δ₂)
  → (δ : val (Tensorfy Δ .₀))
  → (
    let δ₁ , δ₂ = permute s δ in
    Tensorfy Δ₁ .Φᶜ δ₁ + Tensorfy Δ₂ .Φᶜ δ₂
  ) ≡ (Tensorfy Δ .Φᶜ δ)
permute-Φ Permutation.all_right δ = +-identityˡ _
permute-Φ (Permutation.left A s) (a , δ) = Eq.trans (+-assoc _ _ _) (Eq.cong (A .Φᶜ a +_) (permute-Φ s δ))
permute-Φ (Permutation.swapa s) δ = Eq.trans (+-comm _ _) (permute-Φ s δ)


-- cut
_⨾_⨾□ᵐ_ : ∀ {Δ Δ₁ Δ₂ q₁ q₂ A B} → Permutation._≡_⊔_ Δ Δ₁ Δ₂ → MultiSquare Δ₁ q₁ A → MultiSquare (A ∷ Δ₂) q₂ B → MultiSquare Δ (q₁ + q₂) B
(s ⨾ e ⨾□ᵐ f) .top δ =
  let δ₁ , δ₂ = permute s δ in
  bind (F _) (e .top δ₁) (λ a → f .top (a , δ₂))
(s ⨾ e ⨾□ᵐ f) .bot δ =
  let δ₁ , δ₂ = permute s δ in
  f .bot (e .bot δ₁ , δ₂)
(_⨾_⨾□ᵐ_ {Δ} {Δ₁} {Δ₂} {q₁} {q₂} {A} {B} s e f) .square δ =
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
  ≡⟨ Eq.cong (λ c → step (F _) c (ret (f .bot (e .bot δ₁ , δ₂)))) (Eq.cong (_+ (q₁ + q₂)) (permute-Φ s δ)) ⟩
    step (F _)
      (Tensorfy Δ .Φᶜ δ + (q₁ + q₂))
      (ret (f .bot (e .bot δ₁ , δ₂)))
  ∎



open Giralf
giralf : Giralf

giralf .𝓒 = PotentialFunction
giralf ._⨾_⊢_ = MultiSquare
giralf ._≡_⊔_ = Permutation._≡_⊔_

-- Can we use id□ somehow instead?
giralf .id .top (a , _) = ret a
giralf .id .bot (a , _) = a
giralf .id .square _ = ≤⁻-reflexive (Eq.cong (λ c → step (F _) c (ret _)) (Eq.sym (+-identityʳ _)))

-- giralf .Fᵍ = {!   !}
-- giralf .retᵍ = {!   !}
-- giralf .bindᵍ = {!   !}
-- giralf .Uᵍ = {!   !}
-- giralf .suspᵍ = {!   !}
-- giralf .forceᵍ = {!   !}

giralf .charge {A = A} p e = e ⨾□ step-square
  where
    step-square : Square A p A
    step-square .top = step (F _) p ∘ ret
    step-square .bot = Function.id
    step-square .square a = ≤⁻-reflexive (Eq.cong (λ c → step (F _) c (ret _)) (+-comm _ _))

giralf .weaken {p = p} {A = A} e = e ⨾□ weaken-square
  where
    weaken-square : Square A p A
    weaken-square .top = ret
    weaken-square .bot = Function.id
    weaken-square .square a = bind-monoʳ-≤⁻ (Φ A a) (λ a → step-monoˡ-≤⁻ (ret a) (zero/min p))

giralf ._⋊ᵍ_ p A .₀ = A .₀
giralf ._⋊ᵍ_ p A .Φᶜ a = p + A .Φᶜ a
giralf .store {A = A} p e = e ⨾□ store-square
  where
    store-square : Square A p (giralf ._⋊ᵍ_ p A)
    store-square .top = ret
    store-square .bot = Function.id
    store-square .square a = ≤⁻-reflexive (Eq.cong (λ c → step (F _) c (ret _)) (+-comm _ _))
giralf .release {Δ₂ = Δ₂} {p} {q₂ = q₂} {A} {B} s e₁ e₂ = s ⨾ e₁ ⨾□ᵐ lemma
  where
    lemma : MultiSquare ((giralf ._⋊ᵍ_ p A) ∷ Δ₂) q₂ B
    lemma .top = e₂ .top
    lemma .bot = e₂ .bot
    lemma .square (a , δ₂) =
      let helper a b c d =
            let open SolverHelp in let open Vec in
            prove 4 ((v₁ ⊕ v₂) ⊕ (v₃ ⊕ v₄)) (((v₃ ⊕ v₁) ⊕ v₂) ⊕ v₄)
            (a ∷ b ∷ c ∷ d ∷ [])
      in
      let open ≤⁻-Reasoning (F _) in
      begin
        bind (F _) (e₂ .top (a , δ₂)) (Φ B)
      ≲⟨ e₂ .square (a , δ₂) ⟩
         step (F _) (A .Φᶜ a + Tensorfy Δ₂ .Φᶜ δ₂ + (p + q₂)) (ret (e₂ .bot (a , δ₂)))
      ≡⟨ Eq.cong (λ c → step (F _) c (ret _)) (helper _ _ _ _) ⟩
        step (F _) (p + A .Φᶜ a + Tensorfy Δ₂ .Φᶜ δ₂ + q₂) (ret (e₂ .bot (a , δ₂)))
      ∎

giralf ._⊎ᵍ_ A B .₀ = A .₀ ⊎⁺ B .₀
giralf ._⊎ᵍ_ A B .Φᶜ = [ A .Φᶜ , B .Φᶜ ]′
giralf .inj₁ᵍ e .top δ = bind (F _) (e .top δ) λ b → ret (inj₁ b)
giralf .inj₁ᵍ e .bot = inj₁ ∘ e .bot
giralf .inj₁ᵍ e .square δ = bind-monoˡ-≤⁻ (ret ∘ inj₁) (e .square δ)
giralf .inj₂ᵍ e .top δ = bind (F _) (e .top δ) λ b → ret (inj₂ b)
giralf .inj₂ᵍ e .bot = inj₂ ∘ e .bot
giralf .inj₂ᵍ e .square δ = bind-monoˡ-≤⁻ (ret ∘ inj₂) (e .square δ)
giralf .caseᵍ {Δ₂ = Δ₂} {q₂ = q₂} {A} {B} {C} s e e₁ e₂ = s ⨾ e ⨾□ᵐ lemma
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
giralf .tensorᵍ {Δ} {Δ₁} {Δ₂} {q₁} {q₂} {A} {B} s e₁ e₂ = s ⨾ e₁ ⨾□ᵐ lemma
  where
    lemma : MultiSquare (A ∷ Δ₂) q₂ (A ⊗ B)
    lemma .top (a , δ₂) = bind (F _) (e₂ .top δ₂) λ b → ret (a , b)
    lemma .bot (a , δ₂) = (a , e₂ .bot δ₂)
    lemma .square (a , δ₂) =
      let helper a b c =
            let open SolverHelp in let open Vec in
            prove 3 ((v₁ ⊕ v₂) ⊕ v₃) ((v₃ ⊕ v₁) ⊕ v₂) (a ∷ b ∷ c ∷ [])
      in
      let open ≤⁻-Reasoning (F _) in
      begin
        bind (F _) (e₂ .top δ₂) (λ b → Φ (A ⊗ B) (a , b))
      ≡⟨ Eq.cong (bind (F _) (e₂ .top δ₂)) (funext λ _ → Eq.cong (λ c → step (F _) c (ret _)) (+-comm _ _)) ⟩
        bind (F _)
          (bind (F _) (e₂ .top δ₂) (Φ B))
          (λ b → step (F _) (A .Φᶜ a) (ret (a , b)))
      ≲⟨ bind-monoˡ-≤⁻ (λ b → step (F _) _ (ret _)) (e₂ .square δ₂) ⟩
        bind (F _)
          (step (F (B .₀)) (Tensorfy Δ₂ .Φᶜ δ₂ + q₂) (ret (e₂ .bot δ₂)))
          (λ b → step (F _) (A .Φᶜ a) (ret (a , b)))
      ≡⟨ Eq.cong (λ c → step (F _) c (ret _)) (helper _ _ _) ⟩
        step (F _) (A .Φᶜ a + Tensorfy Δ₂ .Φᶜ δ₂ + q₂) (ret (a , e₂ .bot δ₂))
      ∎
giralf .splitᵍ {Δ₂ = Δ₂} {q₂ = q₂} {A} {B} {C} s e e' = s ⨾ e ⨾□ᵐ lemma
  where
    lemma : MultiSquare ((giralf ._⊗ᵍ_ A B) ∷ Δ₂) q₂ C
    lemma .top ((a , b) , δ₂) = e' .top (a , (b , δ₂))
    lemma .bot ((a , b) , δ₂) = e' .bot (a , (b , δ₂))
    lemma .square ((a , b) , δ₂) =
      ≤⁻-trans (e' .square (a , (b , δ₂))) (≤⁻-reflexive (Eq.cong (λ c → step (F _) c (ret _)) (Eq.cong (_+ q₂) (Eq.sym (+-assoc _ _ _)))))


giralf .listᵍ A .₀ = list (A .₀)
giralf .listᵍ A .Φᶜ [] = zero
giralf .listᵍ A .Φᶜ (h ∷ t) = (A .Φᶜ h) + (giralf .listᵍ A .Φᶜ t)
giralf .nilᵍ .top triv = ret []
giralf .nilᵍ .bot triv = []
giralf .nilᵍ .square triv = ≤⁻-refl
giralf .consᵍ {Δ = Δ} {A = A} s eₕ eₜ = Eq.subst (λ q → MultiSquare Δ q (giralf .listᵍ A)) (+-identityʳ _) ((giralf .tensorᵍ s eₕ eₜ) ⨾□ lemma)
  where
    lemma : Square (A ⊗ giralf .listᵍ A) zero (giralf .listᵍ A)
    lemma .top (h , t) = ret (h ∷ t)
    lemma .bot (h , t) = h ∷ t
    lemma .square (h , t) = ≤⁻-refl
giralf .foldrᵍ {A = A} {B = B} e e[] e∷ = Eq.subst (λ q → Square _ q _) (+-identityʳ _) (e ⨾□ lemma)
  where
    lemma : Square (giralf .listᵍ A) zero B
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
