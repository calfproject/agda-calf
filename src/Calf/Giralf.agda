{-# OPTIONS --rewriting --allow-unsolved-metas #-}

open import Algebra.Cost

module Calf.Giralf (costMonoid : CostMonoid) where

open CostMonoid costMonoid


open import Calf.Prelude
open import Calf.CBPV
open import Calf.Directed
open import Calf.Step costMonoid
open import Calf.Data.Product
open import Calf.Data.List

open import Function using (_∘_; const)


open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
postulate
  step/comm : ∀ {X A c e f} →  -- commutativity of step with other effects
    bind {X} A (step (F X) c e) f ≡ bind A e (step A c ∘ f)

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
    charge : ∀ {Δ q A} (p : ℂ) → Δ ⨾ q ⊢ A → Δ ⨾ p + q ⊢ A

    _⋊ᵍ_ : ℂ → 𝓒 → 𝓒
    store : ∀ {Δ q A} (p : ℂ) → Δ ⨾ q ⊢ A → Δ ⨾ p + q ⊢ (p ⋊ᵍ A)
    release : ∀ {Δ p q A B} → Δ ⨾ q ⊢ (p ⋊ᵍ A) → A ⨾ p ⊢ B → Δ ⨾ q ⊢ B

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
      → Δ ⨾ (p + q) ⊢ listᵍ p X
    foldrᵍ : ∀ {Δ q p X A}
      → Δ ⨾ q ⊢ listᵍ p X
      → cmpᵍ A
      → (val X → A ⨾ p ⊢ A)
      → Δ ⨾ q ⊢ A
open Giralf

_⊸F_ : tp⁺ → tp⁺ → Set
X ⊸F Y = cmp (X ⇀ F Y)

record PotentialFunction : Set where
  field
    X : tp⁺
    Φ : X ⊸F X
open PotentialFunction

record Square (Δ : PotentialFunction) (q : ℂ) (A : PotentialFunction) : Set where
  field
    top : Δ .X ⊸F A .X
    bot : Δ .X ⊸F A .X
    square :
      (δ : val (Δ .X)) →
        bind (F _) (top δ) (A .Φ) ≤⁻[ F _ ] bind (F _) (Δ .Φ δ) (step (F _) q ∘ bot)
open Square

giralf : Giralf

giralf .𝓒 = PotentialFunction
-- giralf .cmpᵍ A = cmp (F (A .X)) -- problematic?
giralf ._⨾_⊢_ = Square
giralf .id .top = ret
giralf .id .bot = ret
giralf .id .square δ = ≤⁻-refl

-- giralf .Fᵍ = {!   !}
-- giralf .retᵍ = {!   !}
-- giralf .bindᵍ = {!   !}
-- giralf .Uᵍ = {!   !}
-- giralf .suspᵍ = {!   !}
-- giralf .forceᵍ = {!   !}

giralf .⊤ .X = unit
giralf .⊤ .Φ = ret
giralf .trivᵍ .top = ret
giralf .trivᵍ .bot = ret
giralf .trivᵍ .square triv = ≤⁻-refl

giralf .charge p e .top δ = step (F _) p (e .top δ)
giralf .charge p e .bot = e .bot
giralf .charge {Δ} {q} {A} p e .square δ =
  let open ≤⁻-Reasoning (F _) in
  begin
    step (F _) p (bind (F _) (e .top δ) (A .Φ))
  ≲⟨ step-monoʳ-≤⁻ p (e .square δ) ⟩
    step (F _) p (bind (F _) (Δ .Φ δ) (step (F _) q ∘ e .bot))
  ≡⟨ step/comm {X = Δ .X} {A = F _} {c = p} {e = Δ .Φ δ} {f = step (F _) q ∘ e .bot} ⟩
    bind (F _) (Δ .Φ δ) (step (F _) p ∘ step (F _) q ∘ e .bot)
  ≡⟨⟩
    bind (F _) (Δ .Φ δ) (step (F _) (p + q) ∘ e .bot)
  ∎

(giralf ⋊ᵍ p) A .X = A .X
(giralf ⋊ᵍ p) A .Φ a = step (F _) p (A .Φ a)
giralf .store p e .top = e .top
giralf .store p e .bot = e. bot
giralf .store {Δ} {q} {A} p e .square δ =
  let open ≤⁻-Reasoning (F _) in
  begin
    bind (F _) (e .top δ) (step (F _) p ∘ (A .Φ))
  ≡⟨ Eq.sym (step/comm {X = A .X} {A = F _} {c = p} {e = e .top δ} {f = A .Φ}) ⟩
    step (F _) p (bind (F _) (e .top δ) (A .Φ))
  ≲⟨ step-monoʳ-≤⁻ p (e .square δ) ⟩
    step (F _) p (bind (F _) (Δ .Φ δ) (step (F _) q ∘ e .bot))
  ≡⟨ step/comm {X = Δ .X} {A = F _} {c = p} {e = Δ .Φ δ} ⟩
    bind (F _) (Δ .Φ δ) (step (F _) p ∘ step (F _) q ∘ e .bot)
  ≡⟨⟩
    bind (F _) (Δ .Φ δ) (step (F _) (p + q) ∘ e .bot)
  ∎
giralf .release e₁ e₂ .top δ = bind (F _) (e₁ .top δ) (e₂ .top)
giralf .release e₁ e₂ .bot δ = bind (F _) (e₁ .bot δ) (e₂ .bot)
giralf .release {Δ} {p} {q} {A} {B} e₁ e₂ .square δ =
  let open ≤⁻-Reasoning (F _) in
  begin
    bind (F _) (e₁ .top δ) (λ a → bind (F _) (e₂ .top a) (B .Φ))
  ≲⟨ bind-monoʳ-≤⁻ (e₁ .top δ) (e₂ .square) ⟩
    bind (F _) (e₁ .top δ) (λ a → bind (F _) (A .Φ a) (step (F _) p ∘ e₂ .bot))
  ≡⟨ Eq.cong (bind (F _) (e₁ .top δ)) (funext (λ a → Eq.sym (step/comm {X = A .X} {A = F _} {c = p} {e = A .Φ a}))) ⟩
    bind (F _) (e₁ .top δ) (λ a → bind (F _) (step (F _) p (A .Φ a)) (e₂ .bot))
  ≡⟨⟩ -- bind assoc
    bind (F _) (bind (F _) (e₁ .top δ) (step (F _) p ∘ A .Φ)) (e₂ .bot)
  ≲⟨ bind-monoˡ-≤⁻ (e₂ .bot) (e₁ .square δ) ⟩
    bind (F _) (bind (F _) (Δ .Φ δ) (step (F _) q ∘ e₁ .bot)) (e₂ .bot)
  ≡⟨⟩ -- bind assoc
    bind (F _) (Δ .Φ δ) (step (F _) q ∘ (λ δ' → bind (F _) (e₁ .bot δ') (e₂ .bot)))
  ∎

-- giralf ._⊗_ A B .X = A .X ×⁺ B .X
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
--     ≤⁻-mono {X = A₁ .X ⇀ F _} (bind (F _) (bind (F _) (Δ₁ .Φ δ₁) (e₁ .bot))) (λ-mono-≤⁻ λ a₁' →
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

giralf .listᵍ p X .X = list X
giralf .listᵍ p X .Φ = foldr (λ x e → bind (F _) e (step (F _) p ∘ ret ∘ (x ∷_))) (ret [])
giralf .nil .top triv = ret []
giralf .nil .bot triv = ret []
giralf .nil .square triv = ≤⁻-refl
giralf .cons x e .top δ = bind (F _) (e .top δ) (ret ∘ (x ∷_))
giralf .cons x e .bot δ = bind (F _) (e .bot δ) (ret ∘ (x ∷_))
giralf .cons {Δ} {q} {p} {X} x e .square δ =
  let open ≤⁻-Reasoning (F _) in
  begin
    bind (F _) (e .top δ) (λ l → foldr (λ x e → bind (F _) e (step (F _) p ∘ ret ∘ (x ∷_))) (ret []) (x ∷ l))
  ≡⟨⟩
    bind (F _) (e .top δ) (λ l → bind {list X} (F _) (foldr (λ x e → bind (F _) e (step (F _) p ∘ ret ∘ (x ∷_))) (ret []) l) (step (F _) p ∘ ret ∘ (x ∷_)))
  ≡⟨⟩
    bind {list X} (F _) (bind (F _) (e .top δ) (foldr (λ x e → bind (F _) e (step (F _) p ∘ ret ∘ (x ∷_))) (ret []))) (step (F _) p ∘ ret ∘ (x ∷_))
  ≲⟨ bind-monoˡ-≤⁻ (step (F _) p ∘ ret ∘ (x ∷_)) (e .square δ) ⟩
    bind {list X} (F _) (bind (F _) (Δ .Φ δ) (step (F _) q ∘ e .bot)) (step (F _) p ∘ ret ∘ (x ∷_))
  ≡⟨⟩
    bind (F _) (Δ .Φ δ) (λ δ' → bind (F _) (step (F _) q (e .bot δ')) (step (F _) p ∘ ret ∘ (x ∷_)))
  ≡⟨ Eq.cong (bind (F _) (Δ .Φ δ)) (funext (λ δ' → step/comm {list X} {F _} {p} {step (F _) q (e .bot δ')} {ret ∘ (x ∷_)})) ⟨
    bind (F _) (Δ .Φ δ) (λ δ' → step (F _) (p + q) (bind (F _) (e .bot δ') (ret ∘ (x ∷_))))
  ∎
giralf .foldrᵍ e e[] e∷ .top δ =
  bind (F _) (e .top δ) (foldr (λ x ih → bind (F _) ih (e∷ x .top)) (e[] .top triv))
giralf .foldrᵍ e e[] e∷ .bot δ =
  bind (F _) (e .bot δ) (foldr (λ x ih → bind (F _) ih (e∷ x .bot)) (e[] .bot triv))
giralf .foldrᵍ {Δ} {q} {p} {X} {A} e e[] e∷ .square δ =
  let open ≤⁻-Reasoning (F _) in
  begin
    bind (F _) (bind (F _) (e .top δ) (foldr (λ x ih → bind (F _) ih (e∷ x .top)) (e[] .top triv))) (A .Φ)
  ≡⟨⟩
    bind (F _) (e .top δ) (λ l → bind (F _) (foldr (λ x ih → bind (F _) ih (e∷ x .top)) (e[] .top triv) l) (A .Φ))
  ≲⟨ bind-monoʳ-≤⁻ (e .top δ) lemma ⟩
    bind (F _) (e .top δ) (λ l → bind {list X} (F _) (foldr (λ x e → bind (F _) e (step (F _) p ∘ ret ∘ (x ∷_))) (ret []) l) (foldr (λ x ih → bind (F _) ih (e∷ x .bot)) (e[] .bot triv)))
  ≡⟨⟩
    bind {list X} (F _) (bind (F _) (e .top δ) (foldr (λ x e → bind (F _) e (step (F _) p ∘ ret ∘ (x ∷_))) (ret []))) (foldr (λ x ih → bind (F _) ih (e∷ x .bot)) (e[] .bot triv))
  ≲⟨ bind-monoˡ-≤⁻ (foldr (λ x ih → bind (F _) ih (e∷ x .bot)) (e[] .bot triv)) (e .square δ) ⟩
    bind (F _) (bind (F _) (Δ .Φ δ) (λ l → step (F _) q (e .bot l))) (foldr (λ x ih → bind (F _) ih (e∷ x .bot)) (e[] .bot triv))
  ≡⟨⟩
    bind (F _) (Δ .Φ δ) (λ l → step (F _) q (bind (F _) (e .bot l) (foldr (λ x ih → bind (F _) ih (e∷ x .bot)) (e[] .bot triv))))
  ∎
  where
    lemma : ∀ l →
      bind (F _) (foldr (λ x ih → bind (F _) ih (e∷ x .top)) (e[] .top triv) l) (A .Φ) ≤⁻[ F _ ]
      bind {list X} (F _) (foldr (λ x e → bind (F _) e (step (F _) p ∘ ret ∘ (x ∷_))) (ret []) l) (foldr (λ x ih → bind (F _) ih (e∷ x .bot)) (e[] .bot triv))
    lemma [] = e[] .square triv
    lemma (x ∷ l) =
      let open ≤⁻-Reasoning (F _) in
      begin
        bind (F _) (foldr (λ x ih → bind (F _) ih (e∷ x .top)) (e[] .top triv) (x ∷ l)) (A .Φ)
      ≡⟨⟩
        bind (F _) (bind (F _) (foldr (λ x ih → bind (F _) ih (e∷ x .top)) (e[] .top triv) l) (e∷ x .top)) (A .Φ)
      ≡⟨⟩
        bind (F _) (foldr (λ x ih → bind (F _) ih (e∷ x .top)) (e[] .top triv) l) (λ ih → bind (F _) (e∷ x .top ih) (A .Φ))
      ≲⟨ ≤⁻-mono {X = A .PotentialFunction.X ⇀ F _} (bind (F _) (foldr (λ x ih → bind (F _) ih (e∷ x .top)) (e[] .top triv) l)) (λ-mono-≤⁻ (e∷ x .square)) ⟩
        bind (F _) (foldr (λ x ih → bind (F _) ih (e∷ x .top)) (e[] .top triv) l) (λ ih → bind (F _) (A .Φ ih) (step (F _) p ∘ e∷ x .bot))
      ≡⟨⟩
        bind (F _) (bind (F _) (foldr (λ x ih → bind (F _) ih (e∷ x .top)) (e[] .top triv) l) (A .Φ)) (step (F _) p ∘ e∷ x .bot)
      ≲⟨ bind-monoˡ-≤⁻ (step (F _) p ∘ e∷ x .bot) (lemma l) ⟩
        bind (F _) (bind {list X} (F _) (foldr (λ x e → bind (F _) e (step (F _) p ∘ ret ∘ (x ∷_))) (ret []) l) (foldr (λ x ih → bind (F _) ih (e∷ x .bot)) (e[] .bot triv))) (step (F _) p ∘ e∷ x .bot)
      ≡⟨⟩
        bind {list X} (F _) (foldr (λ x e → bind (F _) e (step (F _) p ∘ ret ∘ (x ∷_))) (ret []) l) (λ l → bind (F _) (foldr (λ x ih → bind (F _) ih (e∷ x .bot)) (e[] .bot triv) l) (step (F _) p ∘ e∷ x .bot))
      ≡⟨ Eq.cong (bind {list X} (F _) (foldr (λ x e → bind (F _) e (step (F _) p ∘ ret ∘ (x ∷_))) (ret []) l)) (funext (λ l → step/comm {X = A .PotentialFunction.X} {A = F _} {c = p} {e = foldr (λ x ih → bind (F _) ih (e∷ x .bot)) (e[] .bot triv) l} {f = e∷ x .bot})) ⟨
        bind {list X} (F _) (foldr (λ x e → bind (F _) e (step (F _) p ∘ ret ∘ (x ∷_))) (ret []) l) (λ l → step (F _) p (bind (F _) (foldr (λ x ih → bind (F _) ih (e∷ x .bot)) (e[] .bot triv) l) (e∷ x .bot)))
      ≡⟨⟩
        bind {list X} (F _) (foldr (λ x e → bind (F _) e (step (F _) p ∘ ret ∘ (x ∷_))) (ret []) l) (λ l → step (F _) p (foldr (λ x ih → bind (F _) ih (e∷ x .bot)) (e[] .bot triv) (x ∷ l)))
      ≡⟨⟩
        bind {list X} (F _) (foldr (λ x e → bind (F _) e (step (F _) p ∘ ret ∘ (x ∷_))) (ret []) l) (λ l → bind {list X} (F _) (step (F _) p (ret (x ∷ l))) (foldr (λ x ih → bind (F _) ih (e∷ x .bot)) (e[] .bot triv)))
      ≡⟨⟩
        bind {list X} (F _) (bind {list X} (F _) (foldr (λ x e → bind (F _) e (step (F _) p ∘ ret ∘ (x ∷_))) (ret []) l) (step (F _) p ∘ ret ∘ (x ∷_))) (foldr (λ x ih → bind (F _) ih (e∷ x .bot)) (e[] .bot triv))
      ≡⟨⟩
        bind {list X} (F _) (foldr (λ x e → bind (F _) e (step (F _) p ∘ ret ∘ (x ∷_))) (ret []) (x ∷ l)) (foldr (λ x ih → bind (F _) ih (e∷ x .bot)) (e[] .bot triv))
      ∎
