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
import Cubical.Data.List.Properties as List
import Cubical.Data.Nat.Properties as Nat


BQ : 𝒞
BQ = F (List ℕ × List ℕ)

LQ : 𝒞
LQ = F (List ℕ)

φ : BQ ⊸ LQ
φ =
  bind (l₁ , l₂) ← idᶜ ⨾
  LQ .charge (` length l₁) (ret (l₂ ++ reverse l₁))

emptyq : U LQ
emptyq = ret []

enqueue : ℕ → LQ ⊸ LQ
enqueue e = bind' λ l → LQ .charge 1 (ret (l ++ [ e ]))

dequeue : LQ ⊸ (ℕₛ ⋊ LQ)
dequeue = bind' λ
  { []      → 0 , ret []
  ; (x ∷ l) → x , ret l }

emptyᵗ : U BQ
emptyᵗ = ret ([] , [])

enqueueᵗ : ℕ → BQ ⊸ BQ
enqueueᵗ e = bind' λ (back , front) → ret (e ∷ back , front)

dequeueᵗ : BQ ⊸ (ℕₛ ⋊ BQ)
dequeueᵗ = bind' λ
  { (back , x ∷ front) → x , ret (back , front)
  ; (back , [])        → reverse-front back }
  where
    reverse-front : List ℕ → U (ℕₛ ⋊ BQ)
    reverse-front back with reverse back
    ... | []     = 0 , BQ .charge (` length back) (ret ([] , []))
    ... | x ∷ l  = x , BQ .charge (` length back) (ret ([] , l))

mapφ : (ℕₛ ⋊ BQ) ⊸ (ℕₛ ⋊ LQ)
mapφ .U (x , q) = x , φ .U q
mapφ .charge c (x , q) i .fst = x
mapφ .charge c (x , q) i .snd = φ .charge c q i

dequeueᵗ-snd : BQ ⊸ BQ
dequeueᵗ-snd .U q = snd (dequeueᵗ .U q)
dequeueᵗ-snd .charge c q = cong snd (dequeueᵗ .charge c q)

dequeue-snd : LQ ⊸ LQ
dequeue-snd .U q = snd (dequeue .U q)
dequeue-snd .charge c q = cong snd (dequeue .charge c q)

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
  empty-coherent = {!   !} -- refl

  enqueue-coherent :
    (e : ℕ) (q : U BQ)
    → φ .U (enqueueᵗ e .U q) ≡ enqueue e .U (φ .U q)
  enqueue-coherent = {!   !}
  -- enqueue-coherent e (c , back , front) =
  --   cong₂ _,_
  --     (enqueue-cost c (length back))
  --     (sym (List.++-assoc front (reverse back) [ e ]))

  dequeue-coherent :
    (q : U BQ)
    → mapφ .U (dequeueᵗ .U q) ≡ dequeue .U (φ .U q)
  dequeue-coherent = {!   !}
  -- dequeue-coherent (c , back , []) with reverse back
  -- ... | [] = refl
  -- ... | x ∷ front =
  --   λ i → x , c + (length back + 0) + 0 , List.++-unit-r front i
  -- dequeue-coherent (c , back , x ∷ front) =
  --   λ i → x , dequeue-front-cost c (length back) i , front ++ reverse back


open import Cubical.Foundations.Equiv
open import Calf.Computation.Open as ◯ᶜ
open import Calf.Computation.Closed as ●ᶜ hiding (law)
open import Calf.Computation.Glue
open import Calf.Value.Open as ◯
open import Calf.Value.Closed as ●

BLQ : 𝒞
BLQ = Glueᶜ' BQ LQ φ

empty' : U BLQ
empty' = triangleᶜ' emptyᵗ emptyq empty-coherent

enqueue' : ℕ → BLQ ⊸ BLQ
enqueue' e = squareᶜ' (enqueueᵗ e) (enqueue e) (enqueue-coherent e)

opaque
  unfolding Glueᶜ'

  dequeue'-fst-glue : U BLQ → fromFRAC (toFRAC ℕ)
  dequeue'-fst-glue =
    square'
      (λ bq → fst (dequeueᵗ .U bq))
      (λ lq → fst (dequeue .U lq))
      (λ q → cong fst (dequeue-coherent q))

  dequeue'-snd : BLQ ⊸ BLQ
  dequeue'-snd = squareᶜ' dequeueᵗ-snd dequeue-snd (λ q → cong snd (dequeue-coherent q))

  dequeueᵗ-fst-●-charge
    : (c : ℂ) (q• : (●ᶜ BQ .U))
    → ●.map (λ bq → fst (dequeueᵗ .U bq)) (●ᶜ BQ .charge c q•)
      ≡ ●.map (λ bq → fst (dequeueᵗ .U bq)) q•
  dequeueᵗ-fst-●-charge c (η• bq) = cong η• (cong fst (dequeueᵗ .charge c bq))
  dequeueᵗ-fst-●-charge c (∗ p) = refl
  dequeueᵗ-fst-●-charge c (law bq p i) =
    isProp→PathP
      (λ i → ●-preserves-isSet isSetℕ
        (●.map (λ bq → fst (dequeueᵗ .U bq)) (●ᶜ BQ .charge c (law bq p i)))
        (●.map (λ bq → fst (dequeueᵗ .U bq)) (law bq p i)))
      (cong η• (cong fst (dequeueᵗ .charge c bq)))
      refl
      i

  dequeue-fst-◯-charge
    : (c : ℂ) (q◦ : (◯ᶜ LQ .U))
    → ◯.map (λ lq → fst (dequeue .U lq)) (◯ᶜ LQ .charge c q◦)
      ≡ ◯.map (λ lq → fst (dequeue .U lq)) q◦
  dequeue-fst-◯-charge c q◦ i p = cong fst (dequeue .charge c (q◦ p)) i

  dequeue'-fst-glue-charge
    : (c : ℂ) (q : U BLQ)
    → dequeue'-fst-glue (BLQ .charge c q) ≡ dequeue'-fst-glue q
  dequeue'-fst-glue-charge c q i .• = dequeueᵗ-fst-●-charge c (q .•) i
  dequeue'-fst-glue-charge c q i .◦ = dequeue-fst-◯-charge c (q .◦) i
  dequeue'-fst-glue-charge c q i .•→◦ =
    isProp→PathP
      (λ i → ●-preserves-isSet (◯-preserves-isSet isSetℕ)
        (●.map η◦ (dequeueᵗ-fst-●-charge c (q .•) i))
        (η• (dequeue-fst-◯-charge c (q .◦) i)))
      (dequeue'-fst-glue (BLQ .charge c q) .•→◦)
      (dequeue'-fst-glue q .•→◦)
      i

  open import Cubical.Data.Sigma using (ΣPathP)

  dequeue' : BLQ ⊸ (ℕₛ ⋊ BLQ)
  dequeue' .U q .fst =
    invIsEq fracture-isEquiv (dequeue'-fst-glue q)
  dequeue' .U q .snd = dequeue'-snd .U q
  dequeue' .charge c q =
    ΣPathP
      ( cong (invIsEq fracture-isEquiv) (dequeue'-fst-glue-charge c q)
      , dequeue'-snd .charge c q
      )
