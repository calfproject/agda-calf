{-# OPTIONS -WnoInteractionMetaBoundaries #-}

module Examples where

open import Calf.Core.Cost
open import Calf.Value
open import Calf.Value.List
open import Calf.Value.Nat
open import Calf.Value.Product
open import Calf.Computation
open import Calf.Computation.Copower
open import Calf.Computation.Free
open import Calf.Computation.Power
open import Cubical.Foundations.Prelude
import Cubical.Data.List.Properties as List
import Cubical.Data.Nat.Properties as Nat
open import Function

double : cmp (ℕᵛ ⇀ F ℕᵛ)
double zero = ret 0
double (suc n) =
  F ℕᵛ .charge 1 $
  bind[ F ℕᵛ ] n' ← double n ⨾
  ret (suc (suc n'))

opaque
  unfolding ℂ

  DOUBLE : ℕ → ℕ
  DOUBLE zero = 0
  DOUBLE (suc n) = suc (suc (DOUBLE n))

  foo : double ⊑[ U (ℕᵛ ⇀ F ℕᵛ) ] (λ n → F ℕᵛ .charge (` n) (ret (DOUBLE n)))
  foo = ⊑-funext lemma
    where
      lemma : ∀ n → double n ⊑[ U (F ℕᵛ) ] F ℕᵛ .charge (` n) (ret (DOUBLE n))
      lemma zero = ≡⇒⊑ (sym (F ℕᵛ .charge/0))
      lemma (suc n) =
        ⊑-trans (⊑-mono (λ e → F ℕᵛ .charge 1 (bind e _)) (lemma n)) $
        ⊑-trans (⊑-mono {X = U (F ℕᵛ)} (F ℕᵛ .charge 1) (⊑-trans (≡⇒⊑ bind/charge) (⊑-mono {X = U (F ℕᵛ)} (F ℕᵛ .charge n) (≡⇒⊑ F/η)))) $
        ≡⇒⊑ (sym (F ℕᵛ .charge/+ {c₁ = 1}))

BQ : 𝒞
BQ = F (Listᵛ ℕᵛ ×ᵛ Listᵛ ℕᵛ)

LQ : 𝒞
LQ = F (Listᵛ ℕᵛ)

φ : BQ ⊸ LQ
φ =
  bind (l₁ , l₂) ← id⊸ ⨾
  LQ .charge (` length l₁) (ret (l₂ ++ reverse l₁))

emptyq : cmp LQ
emptyq = ret []

enqueue : val ℕᵛ → LQ ⊸ LQ
enqueue e = bind' id⊸ λ l → LQ .charge 1 (ret (l ++ [ e ]))

dequeue : LQ ⊸ (ℕᵛ ⋊ LQ)
dequeue = bind' id⊸ λ
  { []      → 0 , ret []
  ; (x ∷ l) → x , ret l }

emptyᵗ : cmp BQ
emptyᵗ = ret ([] , [])

enqueueᵗ : val ℕᵛ → BQ ⊸ BQ
enqueueᵗ e = bind' id⊸ λ (back , front) → ret (e ∷ back , front)

dequeueᵗ : BQ ⊸ (ℕᵛ ⋊ BQ)
dequeueᵗ = bind' id⊸ λ
  { (back , x ∷ front) → x , ret (back , front)
  ; (back , [])        → reverse-front back }
  where
    reverse-front : List ℕ → cmp (ℕᵛ ⋊ BQ)
    reverse-front back with reverse back
    ... | []     = 0 , BQ .charge (` length back) (ret ([] , []))
    ... | x ∷ l  = x , BQ .charge (` length back) (ret ([] , l))

mapφ : (ℕᵛ ⋊ BQ) ⊸ (ℕᵛ ⋊ LQ)
mapφ .U (x , q) = x , φ .U q
mapφ .charge c (x , q) i .fst = x
mapφ .charge c (x , q) i .snd = φ .charge c q i

opaque
  unfolding ℂ
  unfolding F
  unfolding bind'

  enqueue-cost : (c n : ℕ) → c + 0 + suc (n + 0) ≡ c + (n + 0) + 1
  enqueue-cost c n =
    cong (_+ suc (n + 0)) (Nat.+-zero c)
    ∙ Nat.+-suc c (n + 0)
    ∙ Nat.+-comm 1 ((c + (n + 0)))

  dequeue-front-cost : (c n : ℕ) → c + 0 + (n + 0) ≡ c + (n + 0) + 0
  dequeue-front-cost c n =
    cong (_+ (n + 0)) (Nat.+-zero c)
    ∙ sym (Nat.+-zero (c + (n + 0)))

  empty-coherent : φ .U emptyᵗ ≡ emptyq
  empty-coherent = refl

  enqueue-coherent :
    (e : val ℕᵛ) (q : cmp BQ)
    → φ .U (enqueueᵗ e .U q) ≡ enqueue e .U (φ .U q)
  enqueue-coherent e (c , back , front) =
    cong₂ _,_
      (enqueue-cost c (length back))
      (sym (List.++-assoc front (reverse back) [ e ]))

  dequeue-coherent :
    (q : cmp BQ)
    → mapφ .U (dequeueᵗ .U q) ≡ dequeue .U (φ .U q)
  dequeue-coherent (c , back , []) with reverse back
  ... | [] = refl
  ... | x ∷ front =
    λ i → x , c + (length back + 0) + 0 , List.++-unit-r front i
  dequeue-coherent (c , back , x ∷ front) =
    λ i → x , dequeue-front-cost c (length back) i , front ++ reverse back
