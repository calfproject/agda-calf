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
-- open import Calf.Data.List


open import Function using (_∘_; const)


open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
postulate
  step/comm : ∀ {X A c e f} →  -- commutativity of step with other effects
    bind {X} A (step (F X) c e) f ≡ bind A e (step A c ∘ f)
  zero/min : (c : ℂ) → zero ≤ c

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
    tensor : ∀ {Δ Δ₁ Δ₂ q₁ q₂ A B}
      → Δ ≡ Δ₁ ⊔ Δ₂
      → Δ₁ ⨾ q₁ ⊢ A
      → Δ₂ ⨾ q₂ ⊢ B
      → Δ ⨾ (q₁ + q₂) ⊢ (A ⊗ᵍ B)
    split : ∀ {Δ Δ₁ Δ₂ q₁ q₂ A B C}
      → Δ ≡ Δ₁ ⊔ Δ₂
      → Δ₁ ⨾ q₁ ⊢ (A ⊗ᵍ B)
      → (A ∷ B ∷ Δ₂) ⨾ q₂ ⊢ C
      → Δ ⨾ q₁ + q₂ ⊢ C

    -- listᵍ : ℂ → 𝓥 → 𝓒
    -- nil : ∀ {p X} → cmpᵍ (listᵍ p X)
    -- cons : ∀ {Δ q p X}
    --   → val X
    --   → Δ ⨾ q ⊢ listᵍ p X
    --   → Δ ⨾ (q + p) ⊢ listᵍ p X
    -- foldrᵍ : ∀ {Δ q p X A}
    --   → Δ ⨾ q ⊢ listᵍ p X
    --   → cmpᵍ A
    --   → (val X → A ⨾ p ⊢ A)
    --   → Δ ⨾ q ⊢ A

  variable
    X Y Z : 𝓥
    A B C : 𝓒
    p q r : ℂ


open import Calf.Data.List as CalfList

_⊸F_ : tp⁺ → tp⁺ → Set
X ⊸F Y = cmp (X ⇀ F Y)

record PotentialFunction : Set where
  field
    ₀ : tp⁺
    Φ : ₀ ⊸F ₀
open PotentialFunction

giralf-list : ℂ → tp⁺ → PotentialFunction
giralf-list p X .₀ = list X
giralf-list p X .Φ = foldr (λ x e → bind (F _) e (step (F _) p ∘ ret ∘ (x ∷_))) (ret [])

record Square (Δ : PotentialFunction) (q : ℂ) (A : PotentialFunction) : Set where
  field
    top : Δ .₀ ⊸F A .₀
    bot : Δ .₀ ⊸F A .₀
    square :
      (δ : val (Δ .₀)) →
        bind (F _) (top δ) (A .Φ) ≤⁻[ F _ ] bind (F _) (Δ .Φ δ) (step (F _) q ∘ bot)
open Square


id□ : ∀ {A} → Square A zero A
id□ .top = ret
id□ .bot = ret
id□ .square a = ≤⁻-refl

_⨾□_ : ∀ {A B C p q} → Square A p B → Square B q C → Square A (p + q) C
(e ⨾□ f) .top a = bind (F _) (e .top a) (f .top)
(e ⨾□ f) .bot a = bind (F _) (e .bot a) (f .bot)
(_⨾□_ {A} {B} {C} {p} {q} e f) .square a =
  let open ≤⁻-Reasoning (F _) in
  begin
    bind (F _) (e .top a) (λ b → bind (F _) (f .top b) (C .Φ))
  ≲⟨ bind-monoʳ-≤⁻ (e .top a) (f .square) ⟩
    bind (F _) (e .top a) (λ b → bind (F _) (B .Φ b) (step (F _) q ∘ f .bot))
  ≡⟨⟩
    bind (F _) (bind (F _) (e .top a) (B .Φ)) (step (F _) q ∘ f .bot)
  ≲⟨ bind-monoˡ-≤⁻ (step (F _) q ∘ f .bot) (e .square a) ⟩
    bind (F _) (bind (F _) (A .Φ a) (step (F _) p ∘ e .bot)) (step (F _) q ∘ f .bot)
  ≡⟨⟩
    bind (F _) (A .Φ a) (λ a' → bind (F _) (step (F _) p (e .bot a')) (step (F _) q ∘ f .bot))
  ≡⟨⟩
    bind (F _) (A .Φ a) (λ a' → step (F _) p (bind (F _) (e .bot a') (step (F _) q ∘ f .bot)))
  ≡⟨ Eq.cong (bind (F _) (A .Φ a)) (funext (λ a' → Eq.cong (step (F _) p) (step/comm {_} {F _} {q} {e .bot a'} {f .bot}))) ⟨
    bind (F _) (A .Φ a) (λ a' → step (F _) (p + q) (bind (F _) (e .bot a') (f .bot)))
  ∎


-- Define tensor first, which is needed for contexts
_⊗_ : PotentialFunction → PotentialFunction → PotentialFunction
_⊗_ A B .₀ = A .₀ ×⁺ B .₀
_⊗_ A B .Φ (a , b) =
  bind (F _) (A .Φ a) λ a' →
  bind (F _) (B .Φ b) λ b' →
  ret (a' , b')

⊤ : PotentialFunction
⊤ .₀ = unit
⊤ .Φ = ret

MultiSquare : List PotentialFunction → ℂ → PotentialFunction → Set
MultiSquare Δ = Square (List.foldr _⊗_ ⊤ Δ)


permute : ∀ {Δ Δ₁ Δ₂ : List PotentialFunction} → Permutation._≡_⊔_ Δ Δ₁ Δ₂ → val (List.foldr _⊗_ ⊤ Δ .₀) → val (List.foldr _⊗_ ⊤ Δ₁ .₀) × val (List.foldr _⊗_ ⊤ Δ₂ .₀)
permute Permutation.all_right δ = triv , δ
permute (Permutation.left A s) (a , δ) =
  let δ₁ , δ₂ = permute s δ in
  (a , δ₁) , δ₂
permute (Permutation.swapa s) δ =
  let δ₁ , δ₂ = permute s δ in
  δ₂ , δ₁


permute-Φ : ∀ {Δ Δ₁ Δ₂ X} (s : Permutation._≡_⊔_ Δ Δ₁ Δ₂)
  → (δ : val (List.foldr _⊗_ ⊤ Δ .₀))
  → (f : val (List.foldr _⊗_ ⊤ Δ₁ .₀) → val (List.foldr _⊗_ ⊤ Δ₂ .₀) → cmp (F X))
  → (
    let δ₁ , δ₂ = permute s δ in
    bind (F _) (foldr _⊗_ ⊤ Δ₁ .Φ δ₁) λ δ₁' →
    bind (F _) (foldr _⊗_ ⊤ Δ₂ .Φ δ₂) λ δ₂' →
    f δ₁' δ₂'
  ) ≡ (
    bind (F _) (foldr _⊗_ ⊤ Δ .Φ δ) λ δ' →
    let δ₁' , δ₂' = permute s δ' in
    f δ₁' δ₂' )
permute-Φ Permutation.all_right δ f = refl
permute-Φ {Δ = _ ∷ Δ} {Δ₁ = _ ∷ Δ₁} {Δ₂} (Permutation.left A s) (a , δ) f =
  let δ₁ , δ₂ = permute s δ in
  let open Eq.≡-Reasoning in
  begin
    (
      bind (F _) (A .Φ a) λ a' →
      bind (F _) (foldr _⊗_ ⊤ Δ₁ .Φ δ₁) λ δ₁' →
      bind (F _) (foldr _⊗_ ⊤ Δ₂ .Φ δ₂) λ δ₂' →
      f (a' , δ₁') δ₂'
    )
  ≡⟨ Eq.cong (bind (F _) (A .Φ a)) (funext (λ a' → permute-Φ s δ (λ d₁ d₂ → f (a' , d₁) d₂))) ⟩
    (
      bind (F _) (A .Φ a) λ a' →
      bind (F _) (foldr _⊗_ ⊤ Δ .Φ δ) λ δ' →
      let δ₁' , δ₂' = permute s δ' in
      f (a' , δ₁') δ₂'
    )
  ∎

permute-Φ {Δ} {Δ₁} {Δ₂} (Permutation.swapa s) δ f =
  let δ₂ , δ₁  = permute s δ in
  let open Eq.≡-Reasoning in
  begin
    (
      bind (F _) (foldr _⊗_ ⊤ Δ₁ .Φ δ₁) λ δ₁' →
      bind (F _) (foldr _⊗_ ⊤ Δ₂ .Φ δ₂) λ δ₂' →
      f δ₁' δ₂'
    )
  ≡⟨ {! commute effects !} ⟩
    (
      bind (F _) (foldr _⊗_ ⊤ Δ₂ .Φ δ₂) λ δ₂' →
      bind (F _) (foldr _⊗_ ⊤ Δ₁ .Φ δ₁) λ δ₁' →
      f δ₁' δ₂'
    )
  ≡⟨ permute-Φ s δ (λ d₁ d₂ → f d₂ d₁) ⟩
      bind (F _) (foldr _⊗_ ⊤ Δ .Φ δ) (λ δ' →
      let δ₂' , δ₁' = permute s δ' in
      f δ₁' δ₂')
  ∎


-- cut
_⨾_⨾□ᵐ_ : ∀ {Δ Δ₁ Δ₂ q₁ q₂ A B} → Permutation._≡_⊔_ Δ Δ₁ Δ₂ → MultiSquare Δ₁ q₁ A → MultiSquare (A ∷ Δ₂) q₂ B → MultiSquare Δ (q₁ + q₂) B
(s ⨾ e ⨾□ᵐ f) .top δ =
  let δ₁ , δ₂ = permute s δ
  in  bind (F _) (e .top δ₁) (λ a → f .top (a , δ₂))
(s ⨾ e ⨾□ᵐ f) .bot δ =
  let δ₁ , δ₂ = permute s δ
  in  bind (F _) (e .bot δ₁) (λ a → f .bot (a , δ₂))
(_⨾_⨾□ᵐ_ {Δ} {Δ₁} {Δ₂} {q₁} {q₂} {A} {B} s e f) .square δ =
  let δ₁ , δ₂ = permute s δ in
  let open ≤⁻-Reasoning (F _) in
  begin
    bind (F _) (e .top δ₁) (λ a → bind (F _) (f .top (a , δ₂)) (B .Φ))
  ≲⟨ bind-monoʳ-≤⁻ (e .top δ₁) (λ a → f .square (a , δ₂)) ⟩
    (
      bind (F _) (e .top δ₁) λ a →
      bind (F _) (A .Φ a) λ a' →
      bind (F _) (foldr _⊗_ ⊤ Δ₂ .Φ δ₂) λ δ₂' →
      step (F _) q₂ (f .bot (a' , δ₂'))
    )
  ≡⟨⟩ -- bind-assoc
    bind (F _)
      (bind (F _) (e .top δ₁) (A .Φ))
      (
        λ a' →
        bind (F _) (foldr _⊗_ ⊤ Δ₂ .Φ δ₂) λ δ₂' →
        step (F _) q₂ (f .bot (a' , δ₂'))
      )
  ≲⟨ bind-monoˡ-≤⁻ (λ a' → bind (F _) (foldr _⊗_ ⊤ Δ₂ .Φ δ₂) _) (e .square δ₁) ⟩
    bind (F _)
      (bind (F _) (foldr _⊗_ ⊤ Δ₁ .Φ δ₁) (step (F _) q₁ ∘ e .bot))
      (
        λ a' →
        bind (F _) (foldr _⊗_ ⊤ Δ₂ .Φ δ₂) λ δ₂' →
        step (F _) q₂ (f .bot (a' , δ₂'))
      )
  ≡⟨⟩ -- bind-assoc
    (
      bind (F _) (foldr _⊗_ ⊤ Δ₁ .Φ δ₁) λ δ₁' →
      bind (F _) ((step (F _) q₁ ∘ e .bot) δ₁') λ a' →
      bind (F _) (foldr _⊗_ ⊤ Δ₂ .Φ δ₂) λ δ₂' →
      step (F _) q₂ (f .bot (a' , δ₂'))
    )
  ≡⟨ {! some commutativity thing  !} ⟩
    (
      bind (F _) (foldr _⊗_ ⊤ Δ₁ .Φ δ₁) λ δ₁' →
      bind (F _) (foldr _⊗_ ⊤ Δ₂ .Φ δ₂) λ δ₂' →
      bind (F _) ((step (F _) q₁ ∘ e .bot) δ₁') λ a' →
      step (F _) q₂ (f .bot (a' , δ₂'))
    )
  ≡⟨ permute-Φ s δ _ ⟩
    (
      bind (F _) (foldr _⊗_ ⊤ Δ .Φ δ) λ δ' →
      let δ₁' , δ₂' = permute s δ' in
      bind (F _) ((step (F _) q₁ ∘ e .bot) δ₁') λ a' →
      step (F _) q₂ (f .bot (a' , δ₂'))
    )
  ≡⟨⟩
    (
      bind (F _) (foldr _⊗_ ⊤ Δ .Φ δ)
      (
        step (F _) q₁ ∘ (λ δ' →
          let δ₁' , δ₂' = permute s δ' in
          bind (F _) (e .bot δ₁') λ a' →
          step (F _) q₂ (f .bot (a' , δ₂'))
        )
      )
    )
  ≡⟨ Eq.cong (bind (F _) (foldr _⊗_ ⊤ Δ .Φ δ)) (funext (λ δ' → Eq.cong (step (F _) q₁) (Eq.sym (step/comm {A .₀} {F _} {q₂} {e .bot (permute s δ' .proj₁)})))) ⟩
      bind (F _) (foldr _⊗_ ⊤ Δ .Φ δ)
      (
        step (F _) (q₁ + q₂) ∘ (λ δ' →
          let δ₁' , δ₂' = permute s δ' in
          bind (F _) (e .bot δ₁') λ a' →
          f .bot (a' , δ₂')
        )
      )
  ∎


open Giralf
giralf : Giralf

giralf .𝓒 = PotentialFunction
giralf ._⨾_⊢_ = MultiSquare
giralf ._≡_⊔_ = Permutation._≡_⊔_

-- Can we use id□ somehow instead?
giralf .id .top (a , _) = ret a
giralf .id .bot (a , _) = ret a
giralf .id .square _ = ≤⁻-refl

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
    step-square .bot = ret
    step-square .square a = ≤⁻-reflexive (step/comm {A .₀} {F _} {p} {A .Φ a} {ret})

giralf .weaken {p = p} {A = A} e = e ⨾□ weaken-square
  where
    weaken-square : Square A p A
    weaken-square .top = ret
    weaken-square .bot = ret
    weaken-square .square a = bind-monoʳ-≤⁻ (A .Φ a) (λ a' → step-monoˡ-≤⁻ (ret a') (zero/min p))

giralf ._⋊ᵍ_ p A .₀ = A .₀
giralf ._⋊ᵍ_ p A .Φ a = step (F _) p (A .Φ a)
giralf .store {A = A} p e = e ⨾□ store-square
  where
    store-square : Square A p (giralf ._⋊ᵍ_ p A)
    store-square .top = ret
    store-square .bot = ret
    store-square .square a = ≤⁻-reflexive (step/comm {A .₀} {F _} {p} {A .Φ a} {ret})
giralf .release {Δ₂ = Δ₂} {p} {q₂ = q₂} {A} {B} s e₁ e₂ = s ⨾ e₁ ⨾□ᵐ lemma
  where
    lemma : MultiSquare ((giralf ._⋊ᵍ_ p A) ∷ Δ₂) q₂ B
    lemma .top = e₂ .top
    lemma .bot = e₂ .bot
    lemma .square (a , δ₂) =
      let open ≤⁻-Reasoning (F _) in
      begin
        bind (F _) (e₂ .top (a , δ₂)) (B .Φ)
      ≲⟨ e₂ .square (a , δ₂) ⟩
        bind (F _) (A .Φ a) (λ a' →
          bind (F _) (foldr _⊗_ ⊤ Δ₂ .Φ δ₂) (λ δ₂' →
            step (F _) (p + q₂) (e₂ .bot (a' , δ₂'))))
      ≡⟨ Eq.cong (bind (F _) (A .Φ a)) (funext (λ a' → Eq.sym (step/comm {foldr _⊗_ ⊤ Δ₂ .₀} {F _} {p} {foldr _⊗_ ⊤ Δ₂ .Φ δ₂}))) ⟩
        bind (F _) (A .Φ a) (λ a' →
          step (F _) p (bind (F _) (foldr _⊗_ ⊤ Δ₂ .Φ δ₂) (λ δ₂' →
            step (F _) q₂ (e₂ .bot (a' , δ₂')))))
      ≡⟨ Eq.sym (step/comm {A .₀} {F _} {p} {A .Φ a}) ⟩
        bind (F _) ((giralf ⋊ᵍ p) A .Φ a) (λ a' →
          bind (F _) (foldr _⊗_ ⊤ Δ₂ .Φ δ₂) (λ δ₂' →
            step (F _) q₂ (lemma .bot (a' , δ₂'))))
      ∎

giralf ._⊎ᵍ_ A B .₀ = A .₀ ⊎⁺ B .₀
giralf ._⊎ᵍ_ A B .Φ (inj₁ a) = bind (F _) (A .Φ a) λ a' → ret (inj₁ a')
giralf ._⊎ᵍ_ A B .Φ (inj₂ b) = bind (F _) (B .Φ b) λ b' → ret (inj₂ b')
giralf .inj₁ᵍ {A = A} {B = B} e = Eq.subst (λ q → Square _ q _) (+-identityʳ _) (e ⨾□ inl-square)
  where
    inl-square : Square A zero (giralf ._⊎ᵍ_ A B)
    inl-square .top = ret ∘ inj₁
    inl-square .bot = ret ∘ inj₁
    inl-square .square a = bind-monoʳ-≤⁻ (A .Φ a) (λ _ → ≤⁻-refl)
giralf .inj₂ᵍ e .top δ = bind (F _) (e .top δ) λ b → ret (inj₂ b)
giralf .inj₂ᵍ e .bot δ = bind (F _) (e .bot δ) λ b → ret (inj₂ b)
giralf .inj₂ᵍ e .square δ = bind-monoˡ-≤⁻ _ (e .square δ)
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
giralf .tensor s e₁ e₂ .top δ =
  let δ₁ , δ₂ = permute s δ in
  bind (F _) (e₁ .top δ₁) λ a →
  bind (F _) (e₂ .top δ₂) λ b →
  ret (a , b)
giralf .tensor s e₁ e₂ .bot δ =
  let δ₁ , δ₂ = permute s δ in
  bind (F _) (e₁ .bot δ₁) λ a →
  bind (F _) (e₂ .bot δ₂) λ b →
  ret (a , b)
giralf .tensor {Δ} {Δ₁} {Δ₂} {q₁} {q₂} {A} {B} s e₁ e₂ .square δ =
  let δ₁ , δ₂ = permute s δ in
  let open ≤⁻-Reasoning (F _) in
  begin
    (
      bind (F _) (e₁ .top δ₁) λ a →
      bind (F _) (e₂ .top δ₂) λ b →
      bind (F _) (A .Φ a) λ a' →
      bind (F _) (B .Φ b) λ b' →
      ret (a' , b')
    )
  ≡⟨ {! some commutativity thing  !} ⟩
    (
      bind (F _) (bind (F _) (e₁ .top δ₁) (A .Φ)) λ a' →
      bind (F _) (bind (F _) (e₂ .top δ₂) (B .Φ)) λ b' →
      ret (a' , b')
    )
  ≲⟨ bind-monoˡ-≤⁻ _ (e₁ .square δ₁) ⟩
    bind (F _)
    (bind (F _) (foldr _⊗_ ⊤ Δ₁ .Φ δ₁)  (step (F _) q₁ ∘ e₁ .bot))
    (
      λ a' →
      bind (F _) (bind (F _) (e₂ .top δ₂) (B .Φ)) λ b' →
      ret (a' , b')
    )
  ≲⟨ bind-monoʳ-≤⁻ (bind (F _) (foldr _⊗_ ⊤ Δ₁ .Φ δ₁)  (step (F _) q₁ ∘ e₁ .bot)) (λ a' → bind-monoˡ-≤⁻ _ (e₂ .square δ₂)) ⟩
    bind (F _)
    (bind (F _) (foldr _⊗_ ⊤ Δ₁ .Φ δ₁)  (step (F _) q₁ ∘ e₁ .bot))
    (
      λ a' →
      bind (F _)
        (bind (F _) (foldr _⊗_ ⊤ Δ₂ .Φ δ₂)  (step (F _) q₂ ∘ e₂ .bot))
        (λ b' → ret (a' , b'))
    )
  ≡⟨⟩
    (
      bind (F _) (foldr _⊗_ ⊤ Δ₁ .Φ δ₁) λ δ₁' →
      bind (F _) ((step (F _) q₁ ∘ e₁ .bot) δ₁') λ a' →
      bind (F _) (foldr _⊗_ ⊤ Δ₂ .Φ δ₂) λ δ₂' →
      bind (F _) ((step (F _) q₂ ∘ e₂ .bot) δ₂') λ b' →
      ret (a' , b')
    )
  ≡⟨ {! commutativity thing !} ⟩
    (
      bind (F _) (foldr _⊗_ ⊤ Δ₁ .Φ δ₁) λ δ₁' →
      bind (F _) (foldr _⊗_ ⊤ Δ₂ .Φ δ₂) λ δ₂' →
      bind (F _) ((step (F _) q₁ ∘ e₁ .bot) δ₁') λ a' →
      bind (F _) ((step (F _) q₂ ∘ e₂ .bot) δ₂') λ b' →
      ret (a' , b')
    )
  ≡⟨ permute-Φ s δ _ ⟩
    (
      bind (F _) (foldr _⊗_ ⊤ Δ .Φ δ) λ δ' →
      let δ₁' , δ₂' = permute s δ' in
      bind (F _) ((step (F _) q₁ ∘ e₁ .bot) δ₁') λ a' →
      bind (F _) ((step (F _) q₂ ∘ e₂ .bot) δ₂') λ b' →
      ret (a' , b')
    )
  ≡⟨ Eq.cong (bind (F _) (foldr _⊗_ ⊤ Δ .Φ δ)) (funext (λ δ' → Eq.cong (step (F _) q₁) (Eq.sym (step/comm {A .₀} {F _} {q₂} {e₁ .bot (permute s δ' .proj₁)})))) ⟩
    bind (F _) (foldr _⊗_ ⊤ Δ .Φ δ)
      (step (F _) (q₁ + q₂) ∘
      (λ δ' →
        let δ₁' , δ₂' = permute s δ' in
          bind (F _) (e₁ .bot δ₁') λ a →
          bind (F _) (e₂ .bot δ₂') λ b →
          ret (a , b)
      ))
  ∎
giralf .split {Δ} {Δ₁} {Δ₂} {q₁} {q₂} {A} {B} {C} s e e' = s ⨾ e ⨾□ᵐ lemma
  where
    lemma : MultiSquare ((giralf ._⊗ᵍ_ A B) ∷ Δ₂) q₂ C
    lemma .top ((a , b) , δ₂) = e' .top (a , (b , δ₂))
    lemma .bot ((a , b) , δ₂) = e' .bot (a , (b , δ₂))
    lemma .square ((a , b) , δ₂) = e' .square (a , (b , δ₂))


-- giralf .listᵍ = giralf-list
-- giralf .nil .top triv = ret []
-- giralf .nil .bot triv = ret []
-- giralf .nil .square triv = ≤⁻-refl
-- giralf .cons {p = p} {X = X} x e = e ⨾□ cons-square
--   where
--     cons-square : Square (giralf .listᵍ p X) p (giralf .listᵍ p X)
--     cons-square .top = ret ∘ (x ∷_)
--     cons-square .bot = ret ∘ (x ∷_)
--     cons-square .square _ = ≤⁻-refl
-- giralf .foldrᵍ {p = p} {X = X} {A = A} e e[] e∷ = Eq.subst (λ q → Square _ q _) (+-identityʳ _) (e ⨾□ lemma)
--   where
--     lemma : Square (giralf-list p X) zero A
--     lemma .top = foldr (λ x ih → bind (F _) ih (e∷ x .top)) (e[] .top triv)
--     lemma .bot = foldr (λ x ih → bind (F _) ih (e∷ x .bot)) (e[] .bot triv)
--     lemma .square [] = e[] .square triv
--     lemma .square (x ∷ l) =
--       let open ≤⁻-Reasoning (F _) in
--       begin
--         bind (F _)
--           (foldr (λ x ih → bind (F _) ih (e∷ x .top)) (e[] .top triv) l)
--           (λ a → bind (F _) (e∷ x .top a) (A .Φ))
--       ≲⟨ bind-monoʳ-≤⁻ (foldr (λ x ih → bind (F _) ih (e∷ x .top)) (e[] .top triv) l) (λ a → e∷ x .square a) ⟩
--         bind (F _)
--           (foldr (λ x ih → bind (F _) ih (e∷ x .top)) (e[] .top triv) l)
--           (λ a → bind (F _) (A .Φ a) (step (F _) p ∘ e∷ x .bot))
--       ≡⟨⟩
--         bind (F _)
--           (bind (F _) (foldr (λ x ih → bind (F _) ih (e∷ x .top)) (e[] .top triv) l) (A .Φ))
--           (step (F _) p ∘ e∷ x .bot)
--       ≲⟨ bind-monoˡ-≤⁻ (step (F _) p ∘ e∷ x .bot) (lemma .square l) ⟩
--         bind (F _)
--           (foldr (λ x ih → bind (F (list X)) ih (λ l → step (F _) p (ret (x ∷ l)))) (ret []) l)
--           (λ l → bind (F _) (foldr (λ x ih → bind (F _) ih (e∷ x .bot)) (e[] .bot triv) l) (step (F _) p ∘ e∷ x .bot))
--       ≡⟨
--         Eq.cong (bind (F _) (foldr (λ x ih → bind (F (list X)) ih (λ l → step (F _) p (ret (x ∷ l)))) (ret []) l)) (funext λ l →
--         step/comm {_} {F (A .₀)} {p} {foldr (λ x ih → bind (F _) ih (e∷ x .bot)) (e[] .bot triv) l} {e∷ x .bot})
--       ⟨
--         bind (F _)
--           (foldr (λ x ih → bind (F (list X)) ih (λ l → step (F _) p (ret (x ∷ l)))) (ret []) l)
--           (λ l → step (F _) p (bind (F _) (foldr (λ x ih → bind (F _) ih (e∷ x .bot)) (e[] .bot triv) l) (e∷ x .bot)))
--       ∎
