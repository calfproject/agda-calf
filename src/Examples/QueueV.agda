module Examples.QueueV where

open import Cubical.Foundations.Univalence
import Cubical.Data.List.Properties as List
import Cubical.Data.Nat.Properties as Nat
import Cubical.Data.Bool.Properties as Bool
open import Cubical.Data.Sigma using (map-snd; ΣPathP)

open import Calf.Core.Abstract
open import Calf.Core.Cost
open import Calf.Value hiding (empty)
open import Calf.Value.Abstraction
open import Calf.Value.Glue using (fracture-isEquiv)
open import Calf.Value.List
open import Calf.Value.Nat
open import Calf.Value.Bool
open import Calf.Value.Product


record PreQueue : 𝒱₁ where
  field
    Q : 𝒱
    empty : Q
    enqueue : ℕ → Q → Q
    dequeue : Q → ℕ × Q
    isEmpty : Q → Bool

open PreQueue

LQ : 𝒱
LQ = List ℕ

emptyᴸ : LQ
emptyᴸ = []

enqueueᴸ : ℕ → LQ → LQ
enqueueᴸ x l = l ++ [ x ]

dequeueᴸ : LQ → ℕ × LQ
dequeueᴸ [] = 0 , []
dequeueᴸ (x ∷ l) = x , l

isEmptyᴸ : LQ → Bool
isEmptyᴸ [] = true
isEmptyᴸ (x ∷ xs) = false


list-prequeue : PreQueue
list-prequeue .Q = LQ
list-prequeue .empty = emptyᴸ
list-prequeue .enqueue = enqueueᴸ
list-prequeue .dequeue = dequeueᴸ
list-prequeue .isEmpty = isEmptyᴸ



BQ : 𝒱
BQ = List ℕ × List ℕ

emptyᴮ : BQ
emptyᴮ = [] , []

enqueueᴮ : ℕ → BQ → BQ
enqueueᴮ x (back , front) = x ∷ back , front

reverse-front : List ℕ → ℕ × BQ
reverse-front back with reverse back
... | []    = 0 , ([] , [])
... | x ∷ l = x , ([] , l)

dequeueᴮ : BQ → ℕ × BQ
dequeueᴮ (back , x ∷ front) = x , (back , front)
dequeueᴮ (back , []) = reverse-front back

isEmptyᴮ : BQ → Bool
isEmptyᴮ ([] , []) = true
isEmptyᴮ _ = false

batched-prequeue : PreQueue
batched-prequeue .Q = BQ
batched-prequeue .empty = emptyᴮ
batched-prequeue .enqueue = enqueueᴮ
batched-prequeue .dequeue = dequeueᴮ
batched-prequeue .isEmpty = isEmptyᴮ


record Queue : 𝒱₁ where
  field
    prequeue : PreQueue
    spec : ⟨ ABS ⟩ → prequeue ≡ list-prequeue
open Queue

χ : BQ → LQ
χ (l₁ , l₂) = l₂ ++ reverse l₁


empty-coherent : χ emptyᴮ ≡ emptyᴸ
empty-coherent = refl

enqueue-coherent :
  (x : ℕ) (q : BQ)
  → χ (enqueueᴮ x q) ≡ enqueueᴸ x (χ q)
enqueue-coherent x (back , front) = sym (List.++-assoc front (reverse back) [ x ])

dequeue-coherent :
  (q : BQ) → map-snd χ (dequeueᴮ q) ≡ dequeueᴸ (χ q)
dequeue-coherent (back , []) with reverse back
... | [] = refl
... | x ∷ xs = ΣPathP (refl , List.++-unit-r xs)
dequeue-coherent (back , x ∷ front) = refl

isEmpty-coherent  :
  (q : BQ) → isEmptyᴮ q ≡ isEmptyᴸ (χ q)
isEmpty-coherent ([] , []) = refl
isEmpty-coherent ([] , x ∷ front) = refl
isEmpty-coherent (x ∷ back , []) with reverse back
... | [] = refl
... | y ∷ ys = refl
isEmpty-coherent (x ∷ back , y ∷ front) = refl



module _ (Y : 𝒱) where
  ×-Abstraction : Abstraction (map-snd {A = Y} χ) → Y × Abstraction χ
  ×-Abstraction x =
    invIsEq fracture-isEquiv (square _ id proj₁ proj₁ (λ _ → refl) x) ,
    square _ χ proj₂ proj₂ (λ _ → refl) x

  ×-Abstraction-openP : (abs : ⟨ ABS ⟩)
    → PathP
        (λ i →
          ua (Abstraction-open (map-snd {A = Y} χ) abs) i
          → Y × ua (Abstraction-open χ abs) i)
        ×-Abstraction
        id
  ×-Abstraction-openP abs =
    ua→
     λ p →
      ΣPathP
        ( cong (equivFun (Abstraction-open id abs))
            (secIsEq fracture-isEquiv (square _ id proj₁ proj₁ (λ _ → refl) p))
        , ua-gluePath (Abstraction-open χ abs) refl
        )

  out-Abstraction-openP : (abs : ⟨ ABS ⟩)
    → PathP
      (λ i →
        ua (Abstraction-open id abs) i → Y)
        (invEq (Abstraction-id Y))
        id
  out-Abstraction-openP abs =
    ua→
      λ y →
        cong (equivFun (Abstraction-open id abs)) (secEq (Abstraction-id Y) y)

batched-queue : Queue
batched-queue .prequeue .Q = Abstraction χ
batched-queue .prequeue .empty =
  triangle χ emptyᴮ emptyᴸ empty-coherent
batched-queue .prequeue .enqueue e =
  square χ χ (enqueueᴮ e) (enqueueᴸ e) (enqueue-coherent e)
batched-queue .prequeue .dequeue =
  square χ (map-snd χ) dequeueᴮ dequeueᴸ dequeue-coherent ⨾ ×-Abstraction ℕ
batched-queue .spec abs i .Q =
  ua (Abstraction-open χ abs) i
batched-queue .spec abs i .empty =
  triangle-openP χ emptyᴮ emptyᴸ empty-coherent abs i
batched-queue .spec abs i .enqueue e =
  square-openP χ χ (enqueueᴮ e) (enqueueᴸ e) (enqueue-coherent e) abs i
batched-queue .spec abs i .dequeue =
  ( (square-openP χ (map-snd χ) dequeueᴮ dequeueᴸ dequeue-coherent abs)
    ∙ᴾ ×-Abstraction-openP ℕ abs
  ) i
