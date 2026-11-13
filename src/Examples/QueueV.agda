{-# OPTIONS --type-in-type #-}

module Examples.QueueV where

open import Cubical.Foundations.Function
open import Cubical.Foundations.Path
open import Cubical.Foundations.Univalence
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
open import Calf.Value.Sigma
open import Calf.Value.Open
open import Calf.Value.Closed as ●


record PreQueue : 𝒱₁ where
  field
    Q : 𝒱
    empty : Q
    enqueue : ℕ → Q → Q
    dequeue : Q → ℕ × Q
    isEmpty : Q → Bool

open PreQueue

PreQueue-path
  : ∀ {P P' : PreQueue} (P≃P' : P .Q ≃ P' .Q)
  → (equivFun P≃P' (P .empty) ≡ P' .empty)
  → (∀ e p → equivFun P≃P' (P .enqueue e p) ≡ P' .enqueue e (equivFun P≃P' p))
  → (∀ p → fst (P .dequeue p) ≡ fst (P' .dequeue (equivFun P≃P' p)))
  → (∀ p → equivFun P≃P' (snd (P .dequeue p)) ≡ snd (P' .dequeue (equivFun P≃P' p)))
  → (∀ p → P .isEmpty p ≡ P' .isEmpty (equivFun P≃P' p))
  → P ≡ P'
PreQueue-path P≃P' _ _ _ _ _ i .Q = ua P≃P' i
PreQueue-path P≃P' h-empty _ _ _ _ i .empty = ua-gluePath P≃P' h-empty i
PreQueue-path {P} {P'} P≃P' _ h-enqueue _ _ _ i .enqueue e =
  ua→ {e = P≃P'} {f₁ = P' .enqueue e} (ua-gluePath P≃P' ∘ h-enqueue e) i
PreQueue-path {P} {P'} P≃P' _ _ h-fst-dequeue _ _ i .dequeue p .fst =
  ua→ {e = P≃P'} {f₁ = fst ∘ P' .dequeue} h-fst-dequeue i p
PreQueue-path {P} {P'} P≃P' _ _ _ h-snd-dequeue _ i .dequeue p .snd =
  ua→ {e = P≃P'} {f₁ = snd ∘ P' .dequeue} (ua-gluePath P≃P' ∘ h-snd-dequeue) i p
PreQueue-path {P} {P'} P≃P' _ _ _ _ h-isEmpty i .isEmpty =
  ua→ {e = P≃P'} {f₁ = P' .isEmpty}  h-isEmpty i

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
  isConcrete X = ●.isModal X

  isConcreteSpec : {X : 𝒱} (center : X) → isConcrete (spec center)
  isConcreteSpec center =
    isConnected◯→isModal● $ invEq isConnected≃◯isContr $ λ abs →
    isOfHLevelRespectEquiv 0 (lemma abs) (isContrSingl center)
    where
      lemma : ⟨ ABS ⟩ → singl center ≃ spec center
      lemma abs = Σ-cong-equiv-snd (λ _ → isoToEquiv symIso ∙ₑ invEquiv (◯-open abs))

  concrete→◯contr : isConcrete X → ◯ (isContr X)
  concrete→◯contr concrete abs = equivFun isConnected≃◯isContr
            (isModal●→isConnected◯ concrete) abs


  non-interference : ∀ {X Y} → isConcrete X → ◯ (((x : X) → Y x) ≃ Σ X Y)
  non-interference {X} {Y} is-concrete abs =
    let is-contr = concrete→◯contr is-concrete abs in
        ((x : X) → Y x)
      ≃⟨ Π-contractDom is-contr ⟩
        Y (is-contr .fst)
      ≃⟨ invEquiv (Σ-contractFst is-contr) ⟩
        Σ X Y
      ■



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

  length-reverse : (l : List ℕ) → length (reverse l) ≡ length l
  length-reverse [] = refl
  length-reverse (x ∷ xs) =
    List.length++ (reverse xs) [ x ] ∙
    Nat.+-suc (length (reverse xs)) 0 ∙
    cong suc (Nat.+-zero (length (reverse xs))) ∙
    cong suc (length-reverse xs)

  ◯qreverse≡reverse : (q : Queue) → ◯ (qreverse q ≡ reverse)
  ◯qreverse≡reverse q abs = funExt λ l →
      qreverse q l
    ≡⟨ modularity isConcreteQueue ((λ q → qreverse q l)) q list-queue abs ⟩
      qreverse list-queue l
    ≡⟨ refl ⟩
      toList list-queue (length l) (fromList list-queue l)
    ≡⟨ cong (toList list-queue (length l)) (fromList-lemma l) ⟩
      toList list-queue (length l) (reverse l)
    ≡⟨ cong (λ len → toList list-queue len (reverse l)) (sym (length-reverse l)) ⟩
      toList list-queue (length (reverse l)) (reverse l)
    ≡⟨ toList-lemma (reverse l) ⟩
      reverse l
    ∎
    where
      fromList-lemma : (l : List ℕ) → fromList list-queue l ≡ reverse l
      fromList-lemma [] = refl
      fromList-lemma (x ∷ xs) = cong (_++ [ x ]) (fromList-lemma xs)

      toList-lemma : (l : List ℕ) → toList list-queue (length l) l ≡ l
      toList-lemma [] = refl
      toList-lemma (x ∷ xs) = cong (x ∷_) (toList-lemma xs)

data Batch : 𝒱 where
  inj : (back front : List ℕ) → Batch
  tilt : ◯ ((n : ℕ) (back front : List ℕ) →
    inj (back ++ [ n ]) front ≡ inj back (front ++ [ n ]))
  squash : isSet Batch

Batch-rec :
    isSet X
  → (f : (back front : List ℕ) → X)
  → ◯ ((n : ℕ) (back front : List ℕ) → f (back ++ [ n ]) front ≡ f back (front ++ [ n ]))
  → Batch
  → X
Batch-rec isSetX f f-tilt (inj back front) = f back front
Batch-rec isSetX f f-tilt (tilt abs n back front i) = f-tilt abs n back front i
Batch-rec isSetX f f-tilt (squash q q' h h' i i') =
  isSetX
    _ _
    (cong (Batch-rec isSetX f f-tilt) h) (cong (Batch-rec isSetX f f-tilt) h')
    i i'

Batch-ind-prop :
  {P : Batch → 𝒱}
  → ((q : Batch) → isProp (P q))
  → ((back front : List ℕ) → P (inj back front))
  → (q : Batch)
  → P q
Batch-ind-prop isPropP f (inj back front) = f back front
Batch-ind-prop {P} isPropP f (tilt abs n back front i) =
  isProp→PathP (λ i → isPropP (tilt _ _ _ _ i))
    (f (back ++ [ n ]) front) (f back (front ++ [ n ])) i
Batch-ind-prop isPropP f (squash q q' h h' i i') =
  isProp→SquareP (λ i i' → isPropP (squash q q' h h' i i'))
    refl refl
    (cong (Batch-ind-prop isPropP f) h) (cong (Batch-ind-prop isPropP f) h')
    i i'

dequeue-help : List ℕ → ℕ × Batch
dequeue-help [] = 0 , inj [] []
dequeue-help (x ∷ xs) = x , inj [] xs

multitilt : ◯ ((back front other : List ℕ) →
  inj back (front ++ reverse other) ≡ inj (back ++ other) front)
multitilt abs back front [] =
    inj back (front ++ [])
  ≡⟨ cong (λ hole → inj back hole) (List.++-unit-r front) ⟩
    inj back front
  ≡⟨ cong (λ hole → inj hole front) (sym (List.++-unit-r back)) ⟩
    inj (back ++ []) front
  ∎
multitilt abs back front (x ∷ other) =
    inj back (front ++ reverse other ++ [ x ])
  ≡⟨ cong (λ hole → inj back hole)
     (sym $ List.++-assoc front (reverse other) [ x ]) ⟩
    inj back ((front ++ reverse other) ++ [ x ])
  ≡⟨ sym (tilt abs x back (front ++ (reverse other))) ⟩
    inj (back ++ [ x ]) (front ++ reverse other)
  ≡⟨ multitilt abs (back ++ [ x ]) front other  ⟩
    inj ((back ++ [ x ]) ++ other) front
  ≡⟨ cong (λ hole → inj hole front) (List.++-assoc back [ x ] other) ⟩
    inj (back ++ x ∷ other) front
  ∎



batched-prequeue' : PreQueue
batched-prequeue' .Q = Batch
batched-prequeue' .empty = inj [] []
batched-prequeue' .enqueue n =
  Batch-rec squash
    (λ back front → inj (n ∷ back) front)
    λ abs n' back front → tilt abs n' (n ∷ back) front
batched-prequeue' .dequeue =
  Batch-rec (isSet× isSetℕ squash)
    (λ { back [] → dequeue-help (reverse back)
       ; back (x ∷ front) → x , inj back front })
    (λ { abs n back [] →
            dequeue-help (reverse (back ++ [ n ]))
          ≡⟨ cong dequeue-help (List.rev-++ back [ n ]) ⟩
            n , inj [] ([] ++ reverse back)
          ≡⟨ cong (n ,_) (multitilt abs [] [] back) ⟩
            n , inj ([] ++ back) []
          ∎
       ; abs n back (x ∷ front) → cong (x ,_) (tilt abs n back front) })
batched-prequeue' .isEmpty =
  Batch-rec isSetBool
    (λ { [] [] → true
       ; [] (x ∷ front) → false
       ; (x ∷ back) front → false })
    (λ { abs n [] [] → refl
       ; abs n [] (x ∷ front) → refl
       ; abs n (x ∷ back) front → refl })


batched-queue' : Queue
batched-queue' .fst = batched-prequeue'
batched-queue' .snd abs =
  PreQueue-path
    (isoToEquiv (iso fwd bwd fwd∘bwd bwd∘fwd))
    refl
    enqueue-path
    (Batch-ind-prop (λ _ → isSetℕ _ _) dequeue-fst-path)
    (Batch-ind-prop (λ _ → isSetList isSetℕ _ _) dequeue-snd-path)
    (Batch-ind-prop (λ _ → isSetBool _ _) isEmpty-path)
  where
    fwd : Batch → List ℕ
    fwd =
      Batch-rec (isSetList isSetℕ)
        (λ back front → front ++ reverse back)
        λ abs n back front →
          front ++ reverse (back ++ [ n ])
        ≡⟨ cong (front ++_) (List.rev-++ back [ n ]) ⟩
          front ++ [ n ] ++ reverse back
        ≡⟨ (sym $ List.++-assoc front [ n ] (reverse back)) ⟩
          (front ++ [ n ]) ++ reverse back
        ∎

    bwd : List ℕ → Batch
    bwd = inj []

    fwd∘bwd : (l : List ℕ) → (fwd ∘ bwd) l ≡ l
    fwd∘bwd = List.++-unit-r

    bwd∘fwd : (b : Batch) → (bwd ∘ fwd) b ≡ b
    bwd∘fwd = Batch-ind-prop (λ _ → squash _ _) λ back front →
        (bwd ∘ fwd) (inj back front)
      ≡⟨ multitilt abs [] front back ⟩
        inj back front
      ∎

    enqueue-path : (n : ℕ) (b : Batch) →
      fwd (batched-prequeue' .enqueue n b) ≡
      enqueueᴸ n (fwd b)
    enqueue-path n = Batch-ind-prop (λ _ → isSetList isSetℕ _ _) λ back front →
      sym $ List.++-assoc front (reverse back) [ n ]

    dequeue-fst-path : (back front : List ℕ) →
      let b = inj back front in
      batched-prequeue' .dequeue b .proj₁ ≡ dequeueᴸ (fwd b) .proj₁
    dequeue-fst-path back [] with reverse back
    ... | [] = refl
    ... | x ∷ xs = refl
    dequeue-fst-path back (x ∷ front) = refl

    dequeue-snd-path : (back front : List ℕ) →
      let b = inj back front in
      fwd (batched-prequeue' .dequeue b .proj₂) ≡ dequeueᴸ (fwd b) .proj₂
    dequeue-snd-path back [] with reverse back
    ... | [] = refl
    ... | x ∷ b = List.++-unit-r b
    dequeue-snd-path back (x ∷ front) = refl

    isEmpty-path : (back front : List ℕ) →
      let b = inj back front in
      batched-prequeue' .isEmpty b ≡ isEmptyᴸ (fwd b)
    isEmpty-path [] [] = refl
    isEmpty-path [] (x ∷ front) = refl
    isEmpty-path (x ∷ back) front =
        batched-prequeue' .isEmpty (inj (x ∷ back) front)
      ≡⟨ (sym (non-empty (front ++ reverse back) x)) ⟩
        isEmptyᴸ ((front ++ reverse back) ++ [ x ])
      ≡⟨ cong isEmptyᴸ (List.++-assoc front (reverse back) [ x ]) ⟩
        isEmptyᴸ (fwd (inj (x ∷ back) front))
      ∎
      where
        non-empty : (l : List ℕ) (n : ℕ) → isEmptyᴸ (l ++ [ n ]) ≡ false
        non-empty [] n = refl
        non-empty (x ∷ l) n = refl
