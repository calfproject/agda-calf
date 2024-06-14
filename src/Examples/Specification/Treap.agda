{-# OPTIONS --cubical --rewriting #-}

module Examples.Specification.Treap where

open import Cubical.Data.List
open import Cubical.Data.Nat using (ℕ; +-assoc; +-suc)
open import Data.Product 
open import Data.Interval.Base using (_/_)
open import Cubical.Foundations.Prelude hiding (empty)
open import Cubical.Foundations.Everything using (section; retract; _≃_; isoToEquiv; equiv-proof; I)
open import Cubical.Data.List.Properties using (++-assoc)
open import Agda.Builtin.Cubical.HCompU
open import Examples.Decalf.ProbabilisticChoice
open import Function using (_$_)
open import Calf.Data.Nat as Nat using (nat; zero; suc; _+_) 

open import Calf


module _ (A : Set) (B : tp⁺) where
  data Tree : Set where
    empty : Tree
    node  : Tree → A → Tree → Tree
    assoc : {t₁ t₂ t₃ : Tree} {a a' : A} → ext → node (node t₁ a t₂) a' t₃ ≡ node t₁ a (node t₂ a' t₃)


  inord : Tree → List A
  inord empty = []
  inord (node t₁ a t₂) = inord t₁ ++ [ a ] ++ inord t₂
  inord (assoc {t₁} {t₂} {t₃} {a} {a'} u i) = ++-assoc (inord t₁) (a ∷ inord t₂) (a' ∷ inord t₃) i

  data ITreap : Set where
    leaf : ITreap
    vtx : ITreap → val B → ITreap → ITreap
    law : {t₁ t₂ t₃ : ITreap} {b b' : val B} → ext → vtx (vtx t₁ b t₂) b' t₃ ≡ vtx t₁ b (vtx t₂ b' t₃)
  
  itreap : tp⁺
  itreap = meta⁺ ITreap

  size : ITreap → ℕ
  size leaf = 0
  size (vtx t₁ x t₂) = 1 + size t₁ + size t₂
  size (law {t₁} {t₂} {t₃} x i) = lemma t₁ t₂ t₃ i 
    where 
    lemma : (t₁ t₂ t₃ : ITreap) → suc (suc (size t₁ + size t₂ + size t₃)) ≡ suc (size t₁ + suc (size t₂ + size t₃))
    lemma t₁ t₂ t₃ = cong suc (cong suc (sym (+-assoc (size t₁) _ _)) ∙ sym (+-suc _ _))

  no-flip-join : cmp $ Π itreap λ _ → Π B λ _ → Π itreap λ _ → F itreap
  no-flip-join leaf x leaf = ret (vtx leaf x leaf)
  no-flip-join leaf x t@(vtx t₂ x₁ t₃) = ret (vtx leaf x t)
  no-flip-join leaf x (law {t₁} {t₂} {t₃} {b} {b'} u i) = lemma i
    where 
    lemma : ret (vtx leaf x (vtx (vtx t₁ b t₂) b' t₃)) ≡ ret (vtx leaf x (vtx t₁ b (vtx t₂ b' t₃)))
    lemma = cong (λ t → ret (vtx leaf x t)) (law u)
  no-flip-join t@(vtx t₁₁ x t₁₂) y leaf = ret (vtx t y leaf)
  no-flip-join t@(vtx t₁₁ x t₁₂) y (vtx t₂₁ z t₂₂) = bind (F itreap) (no-flip-join t y t₂₁) λ t' → ret (vtx t' z t₂₂)
  no-flip-join (vtx t₁₁ x t₁₂) y (law {t₁} {t₂} {t₃} {b} {b'} u i) = lemma i
    where 
    lemma2 : (λ t' → ret (vtx (vtx t' b t₂) b' t₃)) ≡ (λ t' → ret (vtx t' b (vtx t₂ b' t₃)))
    lemma2 = {!   !}
    lemma : bind (F itreap) (no-flip-join (vtx t₁₁ x t₁₂) y t₁) (λ a → ret (vtx (vtx a b t₂) b' t₃)) ≡ bind (F itreap) (no-flip-join (vtx t₁₁ x t₁₂) y t₁) (λ t' → ret (vtx t' b (vtx t₂ b' t₃)))
    lemma = cong  (λ f → bind (F itreap) (no-flip-join (vtx t₁₁ x t₁₂) y t₁) f) lemma2
  no-flip-join (law {t₁} {t₃} {t₄} {b} {b'} u i) x t₂ = lemma i
    where 
    lemma : no-flip-join (vtx (vtx t₁ b t₃) b' t₄) x t₂ ≡ no-flip-join (vtx t₁ b (vtx t₃ b' t₄)) x t₂
    lemma = cong (λ t → no-flip-join t x t₂) (law u)

  det-join : cmp $ Π itreap λ _ → Π B λ _ → Π itreap λ _ → F itreap
  det-join leaf x leaf = ret (vtx leaf x leaf)
  det-join leaf x t@(vtx t₂₁ y t₂₂) = flip (F _) (1 / 1) (bind (F _) (det-join leaf x t₂₁) λ t' → ret (vtx t' y t₂₂)) (ret (vtx leaf x t))
  det-join leaf x (law x₁ i) = {!   !}
  det-join (vtx t₁ x₁ t₃) x t₂ = {!   !}
  det-join (law x₁ i) x t₂ = {!   !}

  -- data ITreap : val nat → Set where 
  --   leaf : ITreap 0
  --   vtx : {n m : val nat} → ITreap n → val B → ITreap m → ITreap (1 + n + m)
  --   law : {n m k : val nat} → {t₁ : ITreap n} → {t₂ : ITreap m} → {t₃ : ITreap k} → {b b' : val B} → ext → vtx (vtx t₁ b t₂) b' t₃ ≡ vtx t₁ b (vtx t₂ b' t₃)

  right-spine : List A → Tree
  right-spine [] = empty
  right-spine (x ∷ l) = node empty x (right-spine l)


  sec-inord-spine : section inord right-spine
  sec-inord-spine [] = refl
  sec-inord-spine (x ∷ xs) = cong (x ∷_) (sec-inord-spine xs)


  -- tree-append : (t₁ t₂ : Tree) → Tree
  -- tree-append empty t₂ = t₂
  -- tree-append (node t₁ x t₂) t₃ = node t₁ x (tree-append t₂ t₃)
  -- tree-append (assoc {t₁} {t₂} {t₃} {a} {a'} u i) t₄ = assoc {t₁} {t₂} {tree-append t₃ t₄} {a} {a'} u i

  -- right-spine-lemma : (l₁ l₂ : List A) → right-spine (l₁ ++ l₂) ≡ tree-append (right-spine l₁) (right-spine l₂)
  -- right-spine-lemma [] l₂ = refl
  -- right-spine-lemma (x ∷ l₁) l₂ = cong (λ t → node empty x t) (right-spine-lemma l₁ l₂)

  -- tree-append-lemma : (u : ext) → (t₁ t₂ : Tree) → (x : A) → tree-append t₁ (node empty x t₂) ≡ node t₁ x t₂
  -- tree-append-lemma u empty t₂ x = refl
  -- tree-append-lemma u (node t₁ x₁ t₂) t₃ x = cong (λ t → node t₁ x₁ t) (tree-append-lemma u t₂ t₃ x) ∙ sym (assoc u)
  -- tree-append-lemma u (assoc x₁ i₁) t₂ x = {!   !}

  -- ext-right-spine-inord u empty = λ _ → empty
  -- ext-right-spine-inord u (node t₁ x t₂) = right-spine-lemma (inord t₁) (x ∷ (inord t₂))
  --                                       ∙ cong (λ t → tree-append t (node empty x (right-spine (inord t₂)))) (ext-right-spine-inord u t₁)
  --                                       ∙ cong (λ t → tree-append t₁ (node empty x t)) (ext-right-spine-inord u t₂)
  --                                       ∙ tree-append-lemma u t₁ t₂ x
  -- ext-right-spine-inord u (assoc _ i) = {!   !}

  right-spine-lemma : ∀ l₁ y l₂ → ext → right-spine (l₁ ++ y ∷ l₂) ≡ node (right-spine l₁) y (right-spine l₂)
  right-spine-lemma [] y l₂ u = refl
  right-spine-lemma (x ∷ l₁) y l₂ u = cong (node empty x) (right-spine-lemma l₁ y l₂ u) ∙ sym (assoc u)

  ret-inord-spine : ext → retract inord right-spine
  ret-inord-spine u empty = refl
  ret-inord-spine u (node t₁ x t₂) =
    right-spine-lemma (inord t₁) x (inord t₂) u
    ∙ cong₂ (λ t₁ t₂ → node t₁ x t₂) (ret-inord-spine u t₁) (ret-inord-spine u t₂)
  ret-inord-spine u (assoc {t₁} {t₂} {t₃} {a} {a'} u' i) j = lemma i j
    where
    lemma : Square
      (right-spine-lemma (inord t₁ ++ a ∷ inord t₂) a' (inord t₃) u ∙
          (λ i₁ → node ((right-spine-lemma (inord t₁) a (inord t₂) u ∙
            (λ i₂ → node (ret-inord-spine u t₁ i₂) a (ret-inord-spine u t₂ i₂)))
              i₁) a' (ret-inord-spine u t₃ i₁)))
      (right-spine-lemma (inord t₁) a (inord t₂ ++ a' ∷ inord t₃) u ∙
          (λ i₁ → node (ret-inord-spine u t₁ i₁) a
             ((right-spine-lemma (inord t₂) a' (inord t₃) u ∙
               (λ i₂ → node (ret-inord-spine u t₂ i₂) a' (ret-inord-spine u t₃ i₂)))
              i₁)))
      (cong right-spine (++-assoc (inord t₁) (a ∷ inord t₂) (a' ∷ inord t₃)))
      (assoc u')
    lemma i j = {!   !}

  theorem : ext → Tree ≃ List A
  theorem u = isoToEquiv (Cubical.Foundations.Everything.iso inord right-spine sec-inord-spine (ret-inord-spine u))
  -- proj₁ (theorem u) = inord
  -- proj₁ (equiv-proof (proj₂ (theorem u)) l) = right-spine l , sec-inord-spine l
  -- proj₂ (equiv-proof (proj₂ (theorem u)) l) (t , h) = cong₂ _,_ (cong right-spine (sym h) ∙ ret-inord-spine u t) {!   !}
