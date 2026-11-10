{-# OPTIONS --type-in-type #-}

module Examples.QueueV where

open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Function
import Cubical.Data.List.Properties as List
import Cubical.Data.Nat.Properties as Nat
import Cubical.Data.Bool.Properties as Bool

open import Cubical.Data.Sigma using (map-snd; ΣPathP; Σ-contractFst; Σ-cong-snd)

open import Calf.Core.Abstract
open import Calf.Core.Cost
open import Calf.Value hiding (empty)
open import Calf.Value.Abstraction
open import Calf.Value.Glue using (fracture-isEquiv)
open import Calf.Value.List
open import Calf.Value.Nat
open import Calf.Value.Bool
open import Calf.Value.Product
open import Calf.Value.Open
open import Calf.Value.Closed


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



spec : {X : 𝒱} (center : X) → 𝒱
spec {X} center = Σ[ x ∈ X ] ◯ (x ≡ center) 


Queue : 𝒱
Queue = spec list-prequeue


{-
record Queue : 𝒱₁ where
  field
    prequeue : PreQueue
    spec : ⟨ ABS ⟩ → prequeue ≡ list-prequeue
open Queue
-}

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

{-
batched-queue .prequeue .Q = Abstraction χ
batched-queue .prequeue .empty =
  triangle χ emptyᴮ emptyᴸ empty-coherent
batched-queue .prequeue .enqueue e =
  square χ χ (enqueueᴮ e) (enqueueᴸ e) (enqueue-coherent e)
batched-queue .prequeue .dequeue =
  square χ (map-snd χ) dequeueᴮ dequeueᴸ dequeue-coherent ⨾ ×-Abstraction ℕ
batched-queue .prequeue .isEmpty =
 square χ id isEmptyᴮ isEmptyᴸ isEmpty-coherent ⨾ invEq (Abstraction-id Bool)
batched-queue .spec abs i .Q =
  ua (Abstraction-open χ abs) i
batched-queue .spec abs i .empty =
  triangle-openP χ emptyᴮ emptyᴸ empty-coherent abs i
batched-queue .spec abs i .enqueue e = square-openP χ χ (enqueueᴮ e) (enqueueᴸ e) (enqueue-coherent e) abs i
batched-queue .spec abs i .dequeue =
  ( (square-openP χ (map-snd χ) dequeueᴮ dequeueᴸ dequeue-coherent abs)
    ∙ᴾ ×-Abstraction-openP ℕ abs
  ) i
batched-queue .spec abs i .isEmpty =
  ((square-openP χ id isEmptyᴮ isEmptyᴸ isEmpty-coherent abs)
    ∙ᴾ out-Abstraction-openP Bool abs) i
-}


batched-queue .fst .Q = Abstraction χ
batched-queue .fst .empty =
  triangle χ emptyᴮ emptyᴸ empty-coherent
batched-queue .fst .enqueue e =
  square χ χ (enqueueᴮ e) (enqueueᴸ e) (enqueue-coherent e)
batched-queue .fst .dequeue =
  square χ (map-snd χ) dequeueᴮ dequeueᴸ dequeue-coherent ⨾ ×-Abstraction ℕ
batched-queue .fst .isEmpty =
 square χ id isEmptyᴮ isEmptyᴸ isEmpty-coherent ⨾ invEq (Abstraction-id Bool)
batched-queue .snd abs i .Q =
  ua (Abstraction-open χ abs) i
batched-queue .snd abs i .empty =
  triangle-openP χ emptyᴮ emptyᴸ empty-coherent abs i
batched-queue .snd abs i .enqueue e = square-openP χ χ (enqueueᴮ e) (enqueueᴸ e) (enqueue-coherent e) abs i
batched-queue .snd abs i .dequeue =
  ( (square-openP χ (map-snd χ) dequeueᴮ dequeueᴸ dequeue-coherent abs)
    ∙ᴾ ×-Abstraction-openP ℕ abs
  ) i
batched-queue .snd abs i .isEmpty =
  ((square-openP χ id isEmptyᴮ isEmptyᴸ isEmpty-coherent abs)
    ∙ᴾ out-Abstraction-openP Bool abs) i
    

list-queue : Queue
list-queue .fst = list-prequeue
list-queue .snd abs = refl

module Open where
  isConcrete : 𝒱 → 𝒱
  isConcrete X = Calf.Value.Closed.isModal X

  ◯Σ≃◯Σ◯ : ∀ {X Y} → ◯ (Σ X Y) ≃ (◯ (Σ X (◯ ∘ Y)))
  ◯Σ≃◯Σ◯ {X} {Y} = isoToEquiv isoΣ◯
    where
      isoΣ◯ : Iso (◯ (Σ X Y)) (◯ (Σ X (◯ ∘ Y)))
      isoΣ◯ .Iso.fun x,y abs = map-snd η◦ (x,y abs)
      isoΣ◯ .Iso.inv x,y◦ abs = map-snd (_$ abs) (x,y◦ abs) 
      isoΣ◯ .Iso.rightInv x,y◦ =
        funExt (λ abs i → x,y◦ abs .proj₁ ,
                λ abs' → x,y◦ abs .snd (str ABS abs abs' i))
      isoΣ◯ .Iso.leftInv x,y = refl
{-
  concrete→◯contr : ∀ {X} → isConcrete X → ◯ (isContr X)
  concrete→◯contr is-concrete abs = subst isContr (ua (◯-open abs)) is-concrete

  ◯contr→concrete : ∀ {X} → ◯ (isContr X) → isConcrete X
  ◯contr→concrete ◯is-contr .fst abs = ◯is-contr abs .fst
  ◯contr→concrete ◯is-contr .snd x◦ = funExt λ abs → ◯is-contr abs .snd (x◦ abs)
-}

  isConcreteSpec : {X : 𝒱} (center : X) → isConcrete (spec center)
  isConcreteSpec center =
    isConnected◯→isModal●
      (invEq isConnected≃◯isContr (λ abs →
        subst isContr (lemma abs) (isContrSingl center)))
    where lemma : ⟨ ABS ⟩ → singl center ≡ spec center
          lemma abs = {!!}
 









{-
  non-interference : ∀ {X Y} → isConcrete X → ◯ (((x : X) → Y x) ≃ Σ X Y)
  non-interference {X} {Y} is-concrete abs =
    let is-contr = concrete→◯contr is-concrete abs in
        ((x : X) → Y x)
      ≃⟨ Π-contractDom is-contr ⟩
        Y (is-contr .fst)
      ≃⟨ invEquiv (Σ-contractFst is-contr) ⟩
        Σ X Y
      ■
-}
{-
  modularity : ∀ {X Y} → isConcrete X → (f : X → Y) → (x x' : X) → ◯ (f x ≡ f x')
  modularity is-concrete f x x' abs =
    let is-contr = concrete→◯contr is-concrete abs
        contr-path = is-contr .snd
    in cong f ((sym $ contr-path x) ∙ (contr-path x'))

  

open Open

module QueueReverse where
{-
  fromList : (q : Queue) → List ℕ → q .prequeue .Q
  fromList q [] = q .prequeue .empty
  fromList q (x ∷ l) = q .prequeue .enqueue x (fromList q l)

  toList : (q : Queue) → ℕ → q .prequeue .Q → List ℕ
  toList q zero x = []
  toList q (suc n) x = 
    let e , x' = q .prequeue .dequeue x in
    e ∷ toList q n x'
 -}

  fromList : (q : Queue) → List ℕ → q .fst .Q
  fromList q [] = q .fst .empty
  fromList q (x ∷ l) = q .fst .enqueue x (fromList q l)

  toList : (q : Queue) → ℕ → q .fst .Q → List ℕ
  toList q zero x = []
  toList q (suc n) x = 
    let e , x' = q .fst .dequeue x in
    e ∷ toList q n x'

  qreverse : Queue → List ℕ → List ℕ
  qreverse q l = toList q (length l) (fromList q l)

  isConcreteQueue : isConcrete Queue
  isConcreteQueue = isConcreteSpec list-prequeue

  ◯qreverse≡reverse : (q : Queue) → ◯ (qreverse q ≡ reverse)
  ◯qreverse≡reverse q abs = funExt λ l →
      qreverse q l
    ≡⟨ modularity isConcreteQueue ((λ q → qreverse q l)) q list-queue abs ⟩
      qreverse list-queue l
    ≡⟨ refl ⟩
      toList list-queue (length l) (fromList list-queue l)
    ≡⟨ {!!} ⟩ {!!}

data Batch : 𝒱 where
  inj : List ℕ → List ℕ → Batch
  tilt : ⟨ ABS ⟩ → (n : ℕ) (back front : List ℕ) →
    inj (back ++ [ n ]) front ≡ inj back (front ++ [ n ])
  squash : isSet Batch


batched-prequeue' : PreQueue
batched-prequeue' .Q = Batch
batched-prequeue' .empty = inj [] []
batched-prequeue' .enqueue n (inj back front) = inj (n ∷ back) front
batched-prequeue' .enqueue n (tilt abs n' back front i) =
  tilt abs n' (n ∷ back) front i
batched-prequeue' .enqueue n (squash l l₁ x y i i₁) = {!!}
batched-prequeue' .dequeue (inj back []) with reverse back
... | [] = 0 , inj [] []
... | (x ∷ xs) = x , inj [] xs
batched-prequeue' .dequeue (inj back (x ∷ front)) = x , inj back front
batched-prequeue' .dequeue (tilt abs n back [] i) = {!!}
batched-prequeue' .dequeue (tilt abs n back (x ∷ front) i) = {!!}
batched-prequeue' .dequeue (squash q q₁ x y i i₁) = {!!}
batched-prequeue' .isEmpty = {!!}
  
batched-queue' : Queue
batched-queue' .fst = batched-prequeue'
batched-queue' .snd abs i .Q = {!!}
batched-queue' .snd abs i .empty = {!!}
batched-queue' .snd abs i .enqueue = {!!}
batched-queue' .snd abs i .dequeue = {!!}
batched-queue' .snd abs i .isEmpty = {!!}
-}
