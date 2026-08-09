module Examples.Queue where

open import Calf.Core.Abstract
open import Calf.Core.Cost
open import Calf.Core.Monad using (M)
open import Cubical.HITs.SetTruncation using (∣_∣₂)
open import Calf.Value hiding (empty)
open import Calf.Value.List
open import Calf.Value.Nat
open import Calf.Value.Product
open import Calf.Computation
open import Calf.Computation.Copower
open import Calf.Computation.Free
open import Calf.Computation.Power
import Cubical.Data.List.Properties as List
import Cubical.Data.Nat.Properties as Nat


record PreQueue : 𝒱₁ where
  field
    Q : 𝒞
    empty : U Q
    enqueue : ℕ → Q ⊸ Q
    dequeue : Q ⊸ ℕₛ ⋊ Q
open PreQueue

LQ : 𝒞
LQ = F (List ℕ)

emptyᴸ : U LQ
emptyᴸ = ret []

enqueueᴸ : ℕ → LQ ⊸ LQ
enqueueᴸ e = bind' λ l → LQ .charge 1 (ret (l ++ [ e ]))

dequeueᴸ : LQ ⊸ (ℕₛ ⋊ LQ)
dequeueᴸ = bind' λ
  { []      → 0 , ret []
  ; (x ∷ l) → x , ret l }

list-prequeue : PreQueue
list-prequeue .Q = LQ
list-prequeue .empty = emptyᴸ
list-prequeue .enqueue = enqueueᴸ
list-prequeue .dequeue = dequeueᴸ

BQ : 𝒞
BQ = F (List ℕ × List ℕ)

emptyᴮ : U BQ
emptyᴮ = ret ([] , [])

enqueueᴮ : ℕ → BQ ⊸ BQ
enqueueᴮ e = bind' λ (back , front) → ret (e ∷ back , front)

reverse-front : List ℕ → U (ℕₛ ⋊ BQ)
reverse-front back with reverse back
... | []    = 0 , BQ .charge (` length back) (ret ([] , []))
... | x ∷ l = x , BQ .charge (` length back) (ret ([] , l))

dequeueᴮ : BQ ⊸ (ℕₛ ⋊ BQ)
dequeueᴮ = bind' λ
  { (back , x ∷ front) → x , ret (back , front)
  ; (back , [])        → reverse-front back }

batched-prequeue : PreQueue
batched-prequeue .Q = BQ
batched-prequeue .empty = emptyᴮ
batched-prequeue .enqueue = enqueueᴮ
batched-prequeue .dequeue = dequeueᴮ


record Queue : 𝒱₁ where
  field
    prequeue : PreQueue
    spec : ⟨ ABS ⟩ → prequeue ≡ list-prequeue
open Queue

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence using (ua→; ua-gluePath)
open import Calf.Value.Open as ◯
open import Calf.Value.Closed as ●
open import Calf.Value.Glue
open import Calf.Value.Abstraction using (square')
open import Calf.Computation.Open as ◯ᶜ
open import Calf.Computation.Closed as ●ᶜ hiding (law)
open import Calf.Computation.Abstraction

α : BQ ⊸ LQ
α = bind' λ (l₁ , l₂) → LQ .charge (` length l₁) (ret (l₂ ++ reverse l₁))


opaque
  unfolding ℂ

  empty-coherent : α .U emptyᴮ ≡ emptyᴸ
  empty-coherent = bind'/β ∙ F _ .charge/0

  enqueue-coherent :
    (e : ℕ) (q : U BQ)
    → α .U (enqueueᴮ e .U q) ≡ enqueueᴸ e .U (α .U q)
  enqueue-coherent e q =
      α .U (enqueueᴮ e .U q)
    ≡⟨ refl ⟩
      bind' {A = LQ} (λ (l₁ , l₂) → LQ .charge (` length l₁) (ret (l₂ ++ reverse l₁))) .U (
      bind' {A = BQ} (λ (back , front) → ret (e ∷ back , front)) .U q)
    ≡⟨ bind'-assoc {A = LQ}
        (λ (back , front) → ret (e ∷ back , front))
        (λ (l₁ , l₂) → LQ .charge (` length l₁) (ret (l₂ ++ reverse l₁)))
        q ⟩
      bind' {A = LQ} (λ (x : List ℕ × List ℕ) →
        bind' {A = LQ} (λ (l₁ , l₂) → LQ .charge (` length l₁) (ret (l₂ ++ reverse l₁))) .U
          ((λ ((back , front) : List ℕ × List ℕ) → ret (e ∷ back , front)) x)) .U q
    ≡⟨ cong (λ (f : List ℕ × List ℕ → U LQ) → bind' {A = LQ} f .U q) (funExt enqueue-lemma) ⟩
      bind' {A = LQ} (λ (x : List ℕ × List ℕ) →
        bind' {A = LQ} (λ l → LQ .charge 1 (ret (l ++ [ e ]))) .U
          ((λ ((l₁ , l₂) : List ℕ × List ℕ) → LQ .charge (` length l₁) (ret (l₂ ++ reverse l₁))) x)) .U q
    ≡⟨ sym (bind'-assoc {A = LQ}
        (λ (l₁ , l₂) → LQ .charge (` length l₁) (ret (l₂ ++ reverse l₁)))
        (λ l → LQ .charge 1 (ret (l ++ [ e ])))
        q) ⟩
      bind' {A = LQ} (λ l → LQ .charge 1 (ret (l ++ [ e ]))) .U (
      (bind' {A = LQ} (λ (l₁ , l₂) → LQ .charge (` length l₁) (ret (l₂ ++ reverse l₁))) .U q))
    ≡⟨ refl ⟩
      enqueueᴸ e .U (α .U q)
    ∎
    where
      enqueue-cost : (c n : ℕ) → c + 0 + suc (n + 0) ≡ c + (n + 0) + 1
      enqueue-cost c n =
        cong (_+ suc (n + 0)) (Nat.+-zero c)
        ∙ Nat.+-suc c (n + 0)
        ∙ Nat.+-comm 1 ((c + (n + 0)))

      enqueue-lemma : (x : List ℕ × List ℕ)
        → bind' {X = List ℕ × List ℕ} {A = LQ}
            (λ (l₁ , l₂) → LQ .charge (` length l₁) (ret (l₂ ++ reverse l₁))) .U
            ((λ ((back , front) : List ℕ × List ℕ) → ret (e ∷ back , front)) x)
          ≡ bind' {X = List ℕ} {A = LQ}
            (λ l → LQ .charge 1 (ret (l ++ [ e ]))) .U
            ((λ ((l₁ , l₂) : List ℕ × List ℕ) → LQ .charge (` length l₁) (ret (l₂ ++ reverse l₁))) x)
      enqueue-lemma (back , front) =
          bind' {A = LQ} (λ (l₁ , l₂) → LQ .charge (` length l₁) (ret (l₂ ++ reverse l₁))) .U
            (ret (e ∷ back , front))
        ≡⟨ bind'/β {A = LQ} ⟩
          LQ .charge (` length (e ∷ back)) (ret (front ++ reverse (e ∷ back)))
        ≡⟨ cong (λ w → LQ .charge (` length (e ∷ back)) (ret w))
              (sym (List.++-assoc front (reverse back) [ e ])) ⟩
          LQ .charge (` length (e ∷ back)) (ret ((front ++ reverse back) ++ [ e ]))
        ≡⟨ cong (λ c → LQ .charge c (ret ((front ++ reverse back) ++ [ e ])))
              (sym (Nat.+-comm (length back) 1)) ⟩
          LQ .charge ((` length back) +ℂ 1) (ret ((front ++ reverse back) ++ [ e ]))
        ≡⟨ LQ .charge/+ ⟩
          LQ .charge (` length back) (LQ .charge 1 (ret ((front ++ reverse back) ++ [ e ])))
        ≡⟨ cong (LQ .charge (` length back)) (sym (bind'/β {A = LQ})) ⟩
          LQ .charge (` length back)
            (bind' {A = LQ} (λ l → LQ .charge 1 (ret (l ++ [ e ]))) .U (ret (front ++ reverse back)))
        ≡⟨ sym (bind' {A = LQ} (λ l → LQ .charge 1 (ret (l ++ [ e ]))) .charge
                  (` length back) (ret (front ++ reverse back))) ⟩
          bind' {A = LQ} (λ l → LQ .charge 1 (ret (l ++ [ e ]))) .U
            (LQ .charge (` length back) (ret (front ++ reverse back)))
        ∎

module Dequeue where
  BLQ = Abstractionᶜ BQ LQ α

  mapφ : (ℕₛ ⋊ BQ) ⊸ (ℕₛ ⋊ LQ)
  mapφ .U (x , q) = x , α .U q
  mapφ .charge c (x , q) i .fst = x
  mapφ .charge c (x , q) i .snd = α .charge c q i

  dequeueᴮ-snd : BQ ⊸ BQ
  dequeueᴮ-snd .U q = snd (dequeueᴮ .U q)
  dequeueᴮ-snd .charge c q = cong snd (dequeueᴮ .charge c q)

  dequeueᴸ-snd : LQ ⊸ LQ
  dequeueᴸ-snd .U q = snd (dequeueᴸ .U q)
  dequeueᴸ-snd .charge c q = cong snd (dequeueᴸ .charge c q)

  opaque
    unfolding ℂ

    dequeue-front-cost : (c n : ℕ) → c + 0 + (n + 0) ≡ c + (n + 0) + 0
    dequeue-front-cost c n =
      cong (_+ (n + 0)) (Nat.+-zero c)
      ∙ sym (Nat.+-zero (c + (n + 0)))

  opaque
    unfolding ℂ

    dequeue-coherent :
      (q : U BQ)
      → mapφ .U (dequeueᴮ .U q) ≡ dequeueᴸ .U (α .U q)
    dequeue-coherent q =
      cong (λ f → f .U q)
        (bind'-path
          (dequeueᴮ ⨾ᶜ mapφ)
          (α ⨾ᶜ dequeueᴸ)
          (funExt dequeue-lemma))
      where
        dequeue-lemma : (x : List ℕ × List ℕ)
          → (dequeueᴮ ⨾ᶜ mapφ) .U (ret x) ≡ (α ⨾ᶜ dequeueᴸ) .U (ret x)
        dequeue-lemma (back , x ∷ front) =
            dequeueᴮ .U (ret (back , x ∷ front)) .proj₁ ,
            α .U (dequeueᴮ .U (ret (back , x ∷ front)) .proj₂)
          ≡⟨ cong (λ e → e .proj₁ , α .U (e .proj₂)) bind'/β ⟩
            x , α .U (ret (back , front))
          ≡⟨ cong (x ,_) bind'/β ⟩
            x , LQ .charge (` length back) (ret (front ++ reverse back))
          ≡⟨ refl ⟩
            (ℕₛ ⋊ LQ) .charge (` length back) (x , ret (front ++ reverse back))
          ≡⟨ sym (cong ((ℕₛ ⋊ LQ) .charge (` length back)) bind'/β) ⟩
            (ℕₛ ⋊ LQ) .charge (` length back) (dequeueᴸ .U (ret (x ∷ front ++ reverse back)))
          ≡⟨ sym (dequeueᴸ .charge (` length back) (ret _)) ⟩
            dequeueᴸ .U (LQ .charge (` length back) (ret ((x ∷ front) ++ reverse back)))
          ≡⟨ sym (cong (dequeueᴸ .U) bind'/β) ⟩
            dequeueᴸ .U (α .U (ret (back , x ∷ front)))
          ∎
        dequeue-lemma (back , []) =
            dequeueᴮ .U (ret (back , [])) .proj₁ ,
            α .U (dequeueᴮ .U (ret (back , [])) .proj₂)
          ≡⟨ cong (λ e → e .proj₁ , α .U (e .proj₂)) bind'/β ⟩
            reverse-front back .proj₁ , α .U (reverse-front back .proj₂)
          ≡⟨ lemma ⟩
            dequeueᴸ .U (LQ .charge (` length back) (ret (reverse back)))
          ≡⟨ sym (cong (dequeueᴸ .U) bind'/β) ⟩
            dequeueᴸ .U (α .U (ret (back , [])))
          ∎
          where
            length-reverse : (l : List X) → length l ≡ length (reverse l)
            length-reverse [] = refl
            length-reverse (x ∷ l) =
                suc (length l)
              ≡⟨ cong suc (length-reverse l) ⟩
                suc (length (reverse l))
              ≡⟨ Nat.+-comm 1 (length (reverse l)) ⟩
                length (reverse l) + 1
              ≡⟨ refl ⟩
                length (reverse l) + length [ x ]
              ≡⟨ sym (List.length++ (reverse l) [ x ]) ⟩
                length (reverse l ++ [ x ])
              ∎

            lemma :
              (reverse-front back .proj₁ , α .U (reverse-front back .proj₂))
              ≡ dequeueᴸ .U (LQ .charge (` length back) (ret (reverse back)))
            lemma with reverse back | length-reverse back
            ... | [] | h =
                0 , α .U (BQ .charge (length back) (ret ([] , [])))
              ≡⟨ cong (λ c → _,_ {B = const _} 0 $ α .U (BQ .charge c (ret ([] , [])))) h ⟩
                0 , α .U (BQ .charge 0 (ret ([] , [])))
              ≡⟨ cong (λ e → 0 , α .U e) (BQ .charge/0) ⟩
                0 , α .U (ret ([] , []))
              ≡⟨ cong (0 ,_) bind'/β ⟩
                0 , LQ .charge 0 (ret [])
              ≡⟨ cong (0 ,_) (LQ .charge/0) ⟩
                0 , ret []
              ≡⟨ sym bind'/β ⟩
                dequeueᴸ .U (ret [])
              ≡⟨ sym (cong (dequeueᴸ .U) (LQ .charge/0)) ⟩
                dequeueᴸ .U (LQ .charge 0 (ret []))
              ≡⟨ sym (cong (λ c → dequeueᴸ .U (LQ .charge c (ret []))) h) ⟩
                dequeueᴸ .U (LQ .charge (length back) (ret []))
              ∎
            ... | x ∷ front | _ =
                x , α .U (BQ .charge (length back) (ret ([] , front)))
              ≡⟨ cong (x ,_) (α .charge (length back) _) ⟩
                x , F _ .charge (length back) (α .U (ret ([] , front)))
              ≡⟨ cong (λ e → x , F _ .charge (length back) e) bind'/β ⟩
                x , F _ .charge (length back) (LQ .charge 0 (ret (front ++ [])))
              ≡⟨ cong (λ e → x , F _ .charge (length back) e) (LQ .charge/0) ⟩
                x , F _ .charge (length back) (ret (front ++ []))
              ≡⟨ cong (λ l → x , F _ .charge (length back) (ret l)) (List.++-unit-r front) ⟩
                x , F _ .charge (length back) (ret front)
              ≡⟨ refl ⟩
                (ℕₛ ⋊ LQ) .charge (length back) (x , ret front)
              ≡⟨ sym (cong ((ℕₛ ⋊ LQ) .charge (length back)) bind'/β) ⟩
                (ℕₛ ⋊ LQ) .charge (length back) (dequeueᴸ .U (ret (x ∷ front)))
              ≡⟨ sym (dequeueᴸ .charge (length back) _) ⟩
                dequeueᴸ .U (LQ .charge (length back) (ret (x ∷ front)))
              ∎

  opaque
    dequeue'-fst-glue : U BLQ → FractureGlue ℕ
    dequeue'-fst-glue =
      square'
        (λ bq → fst (dequeueᴮ .U bq))
        (λ lq → fst (dequeueᴸ .U lq))
        (λ q → cong fst (dequeue-coherent q))

    dequeue'-snd : BLQ ⊸ BLQ
    dequeue'-snd = squareᶜ' dequeueᴮ-snd dequeueᴸ-snd (λ q → cong snd (dequeue-coherent q))

    dequeueᴮ-fst-●-charge
      : (c : ℂ) (q• : (●ᶜ BQ .U))
      → ●.map (λ bq → fst (dequeueᴮ .U bq)) (●ᶜ BQ .charge c q•)
        ≡ ●.map (λ bq → fst (dequeueᴮ .U bq)) q•
    dequeueᴮ-fst-●-charge c =
      ●.elim (λ _ → ●-≡-isModal _ _)
        (λ bq → cong (λ w → η• (fst w)) (dequeueᴮ .charge c bq))

    dequeueᴸ-fst-◯-charge
      : (c : ℂ) (q◦ : (◯ᶜ LQ .U))
      → ◯.map (λ lq → fst (dequeueᴸ .U lq)) (◯ᶜ LQ .charge c q◦)
        ≡ ◯.map (λ lq → fst (dequeueᴸ .U lq)) q◦
    dequeueᴸ-fst-◯-charge c q◦ i p = cong fst (dequeueᴸ .charge c (q◦ p)) i

    dequeue'-fst-glue-charge
      : (c : ℂ) (q : U BLQ)
      → dequeue'-fst-glue (BLQ .charge c q) ≡ dequeue'-fst-glue q
    dequeue'-fst-glue-charge c q =
      Glue-path (isSet◯ isSetℕ)
        (dequeueᴮ-fst-●-charge c (q .•))
        (dequeueᴸ-fst-◯-charge c (q .◦))

    open import Cubical.Data.Sigma using (ΣPathP)

    dequeue'-fst-charge
      : (c : ℂ) (q : U BLQ)
      → invIsEq fracture-isEquiv (dequeue'-fst-glue (BLQ .charge c q))
      ≡ invIsEq fracture-isEquiv (dequeue'-fst-glue q)
    dequeue'-fst-charge c q =
      cong (invIsEq fracture-isEquiv) (dequeue'-fst-glue-charge c q)

  opaque
    dequeue' : BLQ ⊸ (ℕₛ ⋊ BLQ)
    dequeue' .U q .fst =
      invIsEq fracture-isEquiv (dequeue'-fst-glue q)
    dequeue' .U q .snd = dequeue'-snd .U q
    dequeue' .charge c q =
      ΣPathP
        ( dequeue'-fst-charge c q
        , dequeue'-snd .charge c q
        )



batched-queue : Queue
batched-queue .prequeue .Q = Abstractionᶜ BQ LQ α
batched-queue .prequeue .empty = triangleᶜ' {β = α} emptyᴮ emptyᴸ empty-coherent
batched-queue .prequeue .enqueue e = squareᶜ' (enqueueᴮ e) (enqueueᴸ e) (enqueue-coherent e)
batched-queue .prequeue .dequeue = Dequeue.dequeue'
batched-queue .spec abs i .Q =
  ◯[Abstractionᶜ≡A-abs] {BQ} {LQ} {α} abs i
batched-queue .spec abs i .empty =
  ◯[triangleᶜ'≡b-abs] {b-⊤ = emptyᴮ} {emptyᴸ} {empty-coherent} abs i
batched-queue .spec abs i .enqueue e =
  ◯[squareᶜ'≡f-abs] {f-⊤ = enqueueᴮ e} {enqueueᴸ e} {enqueue-coherent e} abs i
batched-queue .spec abs i .dequeue =
  dequeue'≡dequeueᴸ i
  where
    opaque
      unfolding Dequeue.dequeue'-snd

      dequeue'-snd≡dequeueᴸ-snd
        : PathP
            (λ i →
              ◯[Abstractionᶜ≡A-abs] {BQ} {LQ} {α} abs i
                ⊸ ◯[Abstractionᶜ≡A-abs] {BQ} {LQ} {α} abs i)
            Dequeue.dequeue'-snd
            Dequeue.dequeueᴸ-snd
      dequeue'-snd≡dequeueᴸ-snd =
        ◯[squareᶜ'≡f-abs]
          {f-⊤ = Dequeue.dequeueᴮ-snd}
          {Dequeue.dequeueᴸ-snd}
          {λ q → cong snd (Dequeue.dequeue-coherent q)}
          abs

    opaque
      unfolding
        Dequeue.dequeue'-fst-glue
        Dequeue.dequeue'
        ◯[Abstractionᶜ≡A-abs]

      dequeue'-fst≡dequeueᴸ-fst
        : (q : U Dequeue.BLQ)
        → Dequeue.dequeue' .U q .fst
          ≡ dequeueᴸ .U (◯[Abstractionᶜ≃A-abs] {BQ} {LQ} {α} abs .fst .U q) .fst
      dequeue'-fst≡dequeueᴸ-fst q =
        cong
          (λ g → g .◦ abs)
          (secIsEq fracture-isEquiv (Dequeue.dequeue'-fst-glue q))

      dequeue'-point≡dequeueᴸ
        : (q : U Dequeue.BLQ)
        → PathP
            (λ i → U (ℕₛ ⋊ ◯[Abstractionᶜ≡A-abs] {BQ} {LQ} {α} abs i))
            (Dequeue.dequeue' .U q)
            (dequeueᴸ .U (◯[Abstractionᶜ≃A-abs] {BQ} {LQ} {α} abs .fst .U q))
      dequeue'-point≡dequeueᴸ q =
        ΣPathP
          {A = λ _ → ℕ}
          {B = λ i _ → U (◯[Abstractionᶜ≡A-abs] {BQ} {LQ} {α} abs i)}
          ( dequeue'-fst≡dequeueᴸ-fst q
          , λ i →
              dequeue'-snd≡dequeueᴸ-snd i .U
                (ua-gluePath
                  ( ◯[Abstractionᶜ≃A-abs] {BQ} {LQ} {α} abs .fst .U
                  , ◯[Abstractionᶜ≃A-abs] {BQ} {LQ} {α} abs .snd)
                  {x = q}
                  {y = ◯[Abstractionᶜ≃A-abs] {BQ} {LQ} {α} abs .fst .U q}
                  refl i)
          )

      dequeue'≡dequeueᴸ
        : PathP
            (λ i →
              ◯[Abstractionᶜ≡A-abs] {BQ} {LQ} {α} abs i
                ⊸ ℕₛ ⋊ ◯[Abstractionᶜ≡A-abs] {BQ} {LQ} {α} abs i)
            Dequeue.dequeue'
            dequeueᴸ
      dequeue'≡dequeueᴸ =
        ⊸-path
          (◯[Abstractionᶜ≡A-abs] {BQ} {LQ} {α} abs)
          (λ i → ℕₛ ⋊ ◯[Abstractionᶜ≡A-abs] {BQ} {LQ} {α} abs i)
          (ua→
            {e =
              ( ◯[Abstractionᶜ≃A-abs] {BQ} {LQ} {α} abs .fst .U
              , ◯[Abstractionᶜ≃A-abs] {BQ} {LQ} {α} abs .snd)}
            {B = λ i → U (ℕₛ ⋊ ◯[Abstractionᶜ≡A-abs] {BQ} {LQ} {α} abs i)}
            dequeue'-point≡dequeueᴸ)
