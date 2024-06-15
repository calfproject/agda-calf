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


module _ (A : Set) (B : tp⁺) (u : ext) where
  data Tree : Set where
    empty : Tree
    node  : Tree → A → Tree → Tree
    assoc : (t₁ t₂ t₃ : Tree) (a a' : A) → ext → node (node t₁ a t₂) a' t₃ ≡ node t₁ a (node t₂ a' t₃)


  inord : Tree → List A
  inord empty = []
  inord (node t₁ a t₂) = inord t₁ ++ [ a ] ++ inord t₂
  inord (assoc t₁ t₂ t₃ a a' u i) = ++-assoc (inord t₁) (a ∷ inord t₂) (a' ∷ inord t₃) i

  data ITreap : Set where
    leaf : ITreap
    vtx : ITreap → val B → ITreap → ITreap
    law : (t₁ t₂ t₃ : ITreap) (b b' : val B) → ext → vtx (vtx t₁ b t₂) b' t₃ ≡ vtx t₁ b (vtx t₂ b' t₃)
  
  itreap : tp⁺
  itreap = meta⁺ ITreap

  -- TODO: Optimize this proof
  size : ITreap → ℕ
  size leaf = 0
  size (vtx t₁ x t₂) = 1 + size t₁ + size t₂
  size (law t₁ t₂ t₃ _ _ x i) = cong suc (cong suc (sym (+-assoc (size t₁) (size t₂) (size t₃))) ∙ sym (+-suc (size t₁) (size t₂ + size t₃))) i


  no-flip-join-Tree : Tree → A → Tree → Tree
  no-flip-join-Tree empty a empty = node empty a empty
  no-flip-join-Tree empty a t@(node t₂₁ a' t₃₂) = node empty a t
  no-flip-join-Tree empty b (assoc t₁ t₂ t₃ a a' u i) = cong (node empty b) (assoc t₁ t₂ t₃ a a' u) i
  no-flip-join-Tree t@(node t₁ x t₃) a empty = node t a empty
  no-flip-join-Tree t@(node t₁ x t₂) a (node t₃ y t₄) = node (no-flip-join-Tree t a t₃) y t₄
  no-flip-join-Tree (node t₁ x t₂) a (assoc t₃ t₄ t₅ a' a'' u i) = assoc (no-flip-join-Tree (node t₁ x t₂) a t₃) t₄ t₅ a' a'' u i
  no-flip-join-Tree (assoc t₁ t₂ t₃ a a' u i) b empty = cong (λ eq → node eq b empty) (assoc t₁ t₂ t₃ a a' u) i
  no-flip-join-Tree (assoc t₁ t₂ t₃ a a' u i) b (node t₄ x t₅) = cong (λ eq → node (no-flip-join-Tree eq b t₄) x t₅) ((assoc t₁ t₂ t₃ a a' u)) i
  no-flip-join-Tree (assoc t₁ t₂ t₃ a a' u i) b (assoc t₄ t₅ t₆ a'' a''' u' j) = cong (λ eq → (assoc (no-flip-join-Tree eq b t₄) t₅ t₆ a'' a''' u) j) (assoc t₁ t₂ t₃ a a' u) i

  inord-nfjT : (t₁ t₂ : Tree) → (x : A) → inord (no-flip-join-Tree t₁ x t₂) ≡ inord t₁ ++ x ∷ inord t₂
  inord-nfjT empty empty x = refl
  inord-nfjT empty (node t₂ x₁ t₃) x = refl
  inord-nfjT empty (assoc t₂ t₃ t₄ a a' x₁ i) x = refl
  inord-nfjT (node t₁ x t₂) empty y = refl
  inord-nfjT (node t₁ x t₂) (node t₃ x₁ t₄) y = cong (λ eq → eq ++ x₁ ∷ inord t₄) (inord-nfjT (node t₁ x t₂) t₃ y) ∙ ++-assoc ((inord t₁ ++ x ∷ inord t₂)) (y ∷ inord t₃) (x₁ ∷ inord t₄)
  inord-nfjT (node t₁ x t₂) (assoc t₃ t₄ t₅ a a' _ i) y = {!   !}
  inord-nfjT (assoc t₁ t₂ t₃ a a' _ i) empty x = refl
  inord-nfjT (assoc t₁ t₂ t₃ a a' _ i) (node t₄ x₁ t₅) x = {!   !}
  inord-nfjT (assoc t₁ t₂ t₃ a a' _ i) (assoc t₄ t₅ t₆ a₁ a'' x₁ i₁) x = {!   !}
  
  no-flip-join : cmp $ Π itreap λ _ → Π B λ _ → Π itreap λ _ → F itreap
  no-flip-join leaf x leaf = ret (vtx leaf x leaf)
  no-flip-join leaf x t@(vtx t₂ x₁ t₃) = ret (vtx leaf x t)
  no-flip-join leaf x (law t₁ t₂ t₃ b b' u i) = cong (λ eq → ret {A = itreap} (vtx leaf x eq)) (law t₁ t₂ t₃ b b' u) i
  no-flip-join t@(vtx t₁₁ x t₁₂) y leaf = ret (vtx t y leaf)
  no-flip-join t@(vtx t₁₁ x t₁₂) y (vtx t₂₁ z t₂₂) = bind (F itreap) (no-flip-join t y t₂₁) λ t' → ret (vtx t' z t₂₂)
  no-flip-join (vtx t₁₁ x t₁₂) y (law t₁ t₂ t₃ b b' u i) = cong (λ f → bind (F itreap) (no-flip-join (vtx t₁₁ x t₁₂) y t₁) f) (funExt λ t → cong ret (law t t₂ t₃ b b' u)) i
  no-flip-join (law t₁ t₃ t₄ b b' u i) x leaf = cong (λ t → ret {A = itreap} (vtx t x leaf)) (law t₁ t₃ t₄ b b' u) i
  no-flip-join (law t₁ t₃ t₄ b b' u i) x (vtx t₂ x₁ t₅) = (cong (λ foo → bind (F itreap) (no-flip-join foo x t₂) (λ t' → ret (vtx t' x₁ t₅))) (law t₁ t₃ t₄ b b' u)) i
  no-flip-join (law t₁ t₂ t₃ b b' u i) x (law t₄ t₅ t₆ b'' b''' u' j) = cong (λ eq → bind (F itreap) (no-flip-join eq x t₄) (funExt (λ t i₁ → ret (law t t₅ t₆ b'' b''' u i₁)) j)) (law t₁ t₂ t₃ b b' u) i

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
  right-spine-lemma (x ∷ l₁) y l₂ u = cong (node empty x) (right-spine-lemma l₁ y l₂ u) ∙ sym (assoc _ _ _ _ _ u)

  ret-inord-spine : ext → retract inord right-spine
  ret-inord-spine u empty = refl
  ret-inord-spine u (node t₁ x t₂) =
    right-spine-lemma (inord t₁) x (inord t₂) u
    ∙ cong₂ (λ t₁ t₂ → node t₁ x t₂) (ret-inord-spine u t₁) (ret-inord-spine u t₂)
  ret-inord-spine u (assoc t₁ t₂ t₃ a a' u' i) j = lemma i j
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
      (assoc _ _ _ _ _ u')
    lemma i j = {!   !}

  theorem : ext → Tree ≃ List A
  theorem u = isoToEquiv (Cubical.Foundations.Everything.iso inord right-spine sec-inord-spine (ret-inord-spine u))
  -- proj₁ (theorem u) = inord
  -- proj₁ (equiv-proof (proj₂ (theorem u)) l) = right-spine l , sec-inord-spine l
  -- proj₂ (equiv-proof (proj₂ (theorem u)) l) (t , h) = cong₂ _,_ (cong right-spine (sym h) ∙ ret-inord-spine u t) {!   !}
  