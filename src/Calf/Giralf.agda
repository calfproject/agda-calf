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
  step/comm : ∀ {X A c e f} →  -- commutativity of step with other effects
    bind {X} A (step (F X) c e) f ≡ bind A e (step A c ∘ f)
  zero/min : (c : ℂ) → zero ≤ c

record Giralf : Set₁ where
  𝓥 : Set
  𝓥 = tp⁺

  valᵍ : 𝓥 → Set
  valᵍ = val

  field
    𝓒 : Set
    _⨾_⊢_ : 𝓒 → ℂ → 𝓒 → Set

    id : ∀ {A} → A ⨾ zero ⊢ A

    -- Fᵍ : 𝓥 → 𝓒
    -- retᵍ : ∀ {X} → valᵍ X → cmpᵍ (Fᵍ X)
    -- bindᵍ : ∀ {Δ q X A} → Δ ⨾ q ⊢ (Fᵍ X) → (valᵍ X → cmpᵍ A) → Δ ⨾ q ⊢ A

    -- Uᵍ : 𝓒 → 𝓥
    -- suspᵍ : {!   !}
    -- forceᵍ : {!   !}

    ⊤ : 𝓒
    trivᵍ : ⊤ ⨾ zero ⊢ ⊤
  -- ⊤ = Fᵍ unit

  cmpᵍ : 𝓒 → Set
  cmpᵍ A = ⊤ ⨾ zero ⊢ A

  _⊸_ : 𝓒 → 𝓒 → 𝓥
  A ⊸ B = meta⁺ (A ⨾ zero ⊢ B)

  field
    charge : ∀ {Δ q A} (p : ℂ) → Δ ⨾ q ⊢ A → Δ ⨾ q + p ⊢ A
    weaken : ∀ {Δ q p A} → Δ ⨾ q ⊢ A → Δ ⨾ q + p ⊢ A

    _⋊ᵍ_ : ℂ → 𝓒 → 𝓒
    store : ∀ {Δ q A} (p : ℂ) → Δ ⨾ q ⊢ A → Δ ⨾ q + p ⊢ (p ⋊ᵍ A)
    release : ∀ {Δ p q A B} → Δ ⨾ q ⊢ (p ⋊ᵍ A) → A ⨾ p ⊢ B → Δ ⨾ q ⊢ B

    _⊎ᵍ_ : 𝓒 → 𝓒 → 𝓒
    inj₁ᵍ : ∀ {Δ q A B} → Δ ⨾ q ⊢ A → Δ ⨾ q ⊢ (A ⊎ᵍ B)
    inj₂ᵍ : ∀ {Δ q A B} → Δ ⨾ q ⊢ B → Δ ⨾ q ⊢ (A ⊎ᵍ B)
    caseᵍ : ∀ {Δ q A B C} → Δ ⨾ q ⊢ (A ⊎ᵍ B) → A ⨾ zero ⊢ C → B ⨾ zero ⊢ C → Δ ⨾ q ⊢ C

    -- ⊤ : 𝓒
    -- _⊗_ : 𝓒 → 𝓒 → 𝓒
    -- tensor : ∀ {Δ₁ Δ₂ q₁ q₂ A₁ A₂}
    --   → Δ₁ ⨾ q₁ ⊢ A₁
    --   → Δ₂ ⨾ q₂ ⊢ A₂
    --   → (Δ₁ ⊗ Δ₂) ⨾ (q₁ + q₂) ⊢ (A₁ ⊗ A₂)
    -- split : {!   !}

    listᵍ : ℂ → 𝓥 → 𝓒
    nil : ∀ {p X} → cmpᵍ (listᵍ p X)
    cons : ∀ {Δ q p X}
      → val X
      → Δ ⨾ q ⊢ listᵍ p X
      → Δ ⨾ (q + p) ⊢ listᵍ p X
    foldrᵍ : ∀ {Δ q p X A}
      → Δ ⨾ q ⊢ listᵍ p X
      → cmpᵍ A
      → (val X → A ⨾ p ⊢ A)
      → Δ ⨾ q ⊢ A

  variable
    X Y Z : 𝓥
    A B C : 𝓒
    p q r : ℂ
open Giralf

_⊸F_ : tp⁺ → tp⁺ → Set
X ⊸F Y = cmp (X ⇀ F Y)

record PotentialFunction : Set where
  field
    ₀ : tp⁺
    Φ : ₀ ⊸F ₀
open PotentialFunction

record Square (Δ : PotentialFunction) (q : ℂ) (A : PotentialFunction) : Set where
  field
    top : Δ .₀ ⊸F A .₀
    bot : Δ .₀ ⊸F A .₀
    square :
      (δ : val (Δ .₀)) →
        bind (F _) (top δ) (A .Φ) ≤⁻[ F _ ] bind (F _) (Δ .Φ δ) (step (F _) q ∘ bot)
        -- bind (F _) (top δ) (A .Φ) ≤⁻[ F _ ] bind (F _) (Δ .Φ δ) (λ δ' → bind (F _) (bot δ') (step (F _) q ∘ ret))
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

giralf-list : ℂ → tp⁺ → PotentialFunction
giralf-list p X .₀ = list X
giralf-list p X .Φ = foldr (λ x e → bind (F _) e (step (F _) p ∘ ret ∘ (x ∷_))) (ret [])


giralf : Giralf

giralf .𝓒 = PotentialFunction
giralf ._⨾_⊢_ = Square
giralf .id = id□

-- giralf .Fᵍ = {!   !}
-- giralf .retᵍ = {!   !}
-- giralf .bindᵍ = {!   !}
-- giralf .Uᵍ = {!   !}
-- giralf .suspᵍ = {!   !}
-- giralf .forceᵍ = {!   !}

giralf .⊤ .₀ = unit
giralf .⊤ .Φ = ret
giralf .trivᵍ = id□

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
giralf .release {p = p} {A = A} {B = B} e₁ e₂ = Eq.subst (λ q → Square _ q _) (+-identityʳ _) (e₁ ⨾□ lemma)
  where
    lemma : Square (giralf ._⋊ᵍ_ p A) zero B
    lemma .top = e₂ .top
    lemma .bot = e₂ .bot
    lemma .square a = ≤⁻-trans (e₂ .square a) (≤⁻-reflexive (Eq.sym (step/comm {A .₀} {F _} {p} {A .Φ a})))

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
giralf .caseᵍ {A = A} {B = B} {C = C} e e₁ e₂ = Eq.subst (λ q → Square _ q _) (+-identityʳ _) (e ⨾□ lemma)
  where
    lemma : Square (giralf ._⊎ᵍ_ A B) zero C
    lemma .top = [ e₁ .top , e₂ .top ]′
    lemma .bot = [ e₁ .bot , e₂ .bot ]′
    lemma .square (inj₁ a) = e₁ .square a
    lemma .square (inj₂ b) = e₂ .square b
    -- lemma .square = Sum.[ e₁ .square , e₂ .square ]

-- giralf ._⊗_ A B .₀ = A .₀ ×⁺ B .₀
-- giralf ._⊗_ A B .Φ (a , b) =
--   bind (F _) (A .Φ a) λ a' →
--   bind (F _) (B .Φ b) λ b' →
--   ret (a' , b')
-- giralf .tensor e₁ e₂ .top (δ₁ , δ₂) =
--   bind (F _) (e₁ .top δ₁) λ a₁ →
--   bind (F _) (e₂ .top δ₂) λ a₂ →
--   ret (a₁ , a₂)
-- giralf .tensor e₁ e₂ .bot (δ₁ , δ₂) =
--   bind (F _) (e₁ .bot δ₁) λ a₁ →
--   bind (F _) (e₂ .bot δ₂) λ a₂ →
--   ret (a₁ , a₂)
-- giralf .tensor {Δ₁ = Δ₁} {Δ₂} {A₁ = A₁} {A₂} e₁ e₂ .square (δ₁ , δ₂) =
--   let open ≤⁻-Reasoning (F _) in
--   begin
--     ( bind (F _) (e₁ .top δ₁) λ a₁ →
--       bind (F _) (e₂ .top δ₂) λ a₂ →
--       bind (F _) (A₁ .Φ a₁) λ a₁' →
--       bind (F _) (A₂ .Φ a₂) λ a₂' →
--       ret (a₁' , a₂')
--     )
--   ≡⟨ {! commutativity of effects  !} ⟩
--     ( bind (F _) (e₁ .top δ₁) λ a₁ →
--       bind (F _) (A₁ .Φ a₁) λ a₁' →
--       bind (F _) (e₂ .top δ₂) λ a₂ →
--       bind (F _) (A₂ .Φ a₂) λ a₂' →
--       ret (a₁' , a₂')
--     )
--   ≡⟨⟩
--     ( bind (F _) (bind (F _) (e₁ .top δ₁) (A₁ .Φ)) λ a₁' →
--       bind (F _) (bind (F _) (e₂ .top δ₂) (A₂ .Φ)) λ a₂' →
--       ret (a₁' , a₂')
--     )
--   ≲⟨ ≤⁻-mono
--       (λ e →
--         bind (F _) e λ a₁' →
--         bind (F _) (bind (F _) (e₂ .top δ₂) (A₂ .Φ)) λ a₂' →
--         ret (a₁' , a₂')
--       )
--       (e₁ .square δ₁)
--   ⟩
--     ( bind (F _) (bind (F _) (Δ₁ .Φ δ₁) (e₁ .bot)) λ a₁' →
--       bind (F _) (bind (F _) (e₂ .top δ₂) (A₂ .Φ)) λ a₂' →
--       ret (a₁' , a₂')
--     )
--   ≲⟨
--     ≤⁻-mono {X = A₁ .₀ ⇀ F _} (bind (F _) (bind (F _) (Δ₁ .Φ δ₁) (e₁ .bot))) (λ-mono-≤⁻ λ a₁' →
--     ≤⁻-mono (λ e → bind (F _) e λ a₂' → ret (a₁' , a₂')) (e₂ .square δ₂))
--   ⟩
--     ( bind (F _) (bind (F _) (Δ₁ .Φ δ₁) (e₁ .bot)) λ a₁' →
--       bind (F _) (bind (F _) (Δ₂ .Φ δ₂) (e₂ .bot)) λ a₂' →
--       ret (a₁' , a₂')
--     )
--   ≡⟨⟩
--     ( bind (F _) (Δ₁ .Φ δ₁) λ δ₁' →
--       bind (F _) (e₁ .bot δ₁') λ a₁' →
--       bind (F _) (Δ₂ .Φ δ₂) λ δ₂' →
--       bind (F _) (e₂ .bot δ₂') λ a₂' →
--       ret (a₁' , a₂')
--     )
--   ≡⟨ {! commutativity of effects  !} ⟩
--     ( bind (F _) (Δ₁ .Φ δ₁) λ δ₁' →
--       bind (F _) (Δ₂ .Φ δ₂) λ δ₂' →
--       bind (F _) (e₁ .bot δ₁') λ a₁' →
--       bind (F _) (e₂ .bot δ₂') λ a₂' →
--       ret (a₁' , a₂')
--     )
--   ∎
-- giralf .split = {!   !}

giralf .listᵍ = giralf-list
giralf .nil .top triv = ret []
giralf .nil .bot triv = ret []
giralf .nil .square triv = ≤⁻-refl
giralf .cons {p = p} {X = X} x e = e ⨾□ cons-square
  where
    cons-square : Square (giralf .listᵍ p X) p (giralf .listᵍ p X)
    cons-square .top = ret ∘ (x ∷_)
    cons-square .bot = ret ∘ (x ∷_)
    cons-square .square _ = ≤⁻-refl
giralf .foldrᵍ {p = p} {X = X} {A = A} e e[] e∷ = Eq.subst (λ q → Square _ q _) (+-identityʳ _) (e ⨾□ lemma)
  where
    lemma : Square (giralf-list p X) zero A
    lemma .top = foldr (λ x ih → bind (F _) ih (e∷ x .top)) (e[] .top triv)
    lemma .bot = foldr (λ x ih → bind (F _) ih (e∷ x .bot)) (e[] .bot triv)
    lemma .square [] = e[] .square triv
    lemma .square (x ∷ l) =
      let open ≤⁻-Reasoning (F _) in
      begin
        bind (F _)
          (foldr (λ x ih → bind (F _) ih (e∷ x .top)) (e[] .top triv) l)
          (λ a → bind (F _) (e∷ x .top a) (A .Φ))
      ≲⟨ bind-monoʳ-≤⁻ (foldr (λ x ih → bind (F _) ih (e∷ x .top)) (e[] .top triv) l) (λ a → e∷ x .square a) ⟩
        bind (F _)
          (foldr (λ x ih → bind (F _) ih (e∷ x .top)) (e[] .top triv) l)
          (λ a → bind (F _) (A .Φ a) (step (F _) p ∘ e∷ x .bot))
      ≡⟨⟩
        bind (F _)
          (bind (F _) (foldr (λ x ih → bind (F _) ih (e∷ x .top)) (e[] .top triv) l) (A .Φ))
          (step (F _) p ∘ e∷ x .bot)
      ≲⟨ bind-monoˡ-≤⁻ (step (F _) p ∘ e∷ x .bot) (lemma .square l) ⟩
        bind (F _)
          (foldr (λ x ih → bind (F (list X)) ih (λ l → step (F _) p (ret (x ∷ l)))) (ret []) l)
          (λ l → bind (F _) (foldr (λ x ih → bind (F _) ih (e∷ x .bot)) (e[] .bot triv) l) (step (F _) p ∘ e∷ x .bot))
      ≡⟨
        Eq.cong (bind (F _) (foldr (λ x ih → bind (F (list X)) ih (λ l → step (F _) p (ret (x ∷ l)))) (ret []) l)) (funext λ l →
        step/comm {_} {F (A .₀)} {p} {foldr (λ x ih → bind (F _) ih (e∷ x .bot)) (e[] .bot triv) l} {e∷ x .bot})
      ⟨
        bind (F _)
          (foldr (λ x ih → bind (F (list X)) ih (λ l → step (F _) p (ret (x ∷ l)))) (ret []) l)
          (λ l → step (F _) p (bind (F _) (foldr (λ x ih → bind (F _) ih (e∷ x .bot)) (e[] .bot triv) l) (e∷ x .bot)))
      ∎
