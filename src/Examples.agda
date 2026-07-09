module Examples where

open import Calf.Core.Cost
open import Calf.Core.Monad using (M)
open import Cubical.HITs.SetTruncation using (∣_∣₂)
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
φ = bind' λ (l₁ , l₂) → LQ .charge (` length l₁) (ret (l₂ ++ reverse l₁))

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

reverse-front : List ℕ → U (ℕₛ ⋊ BQ)
reverse-front back with reverse back
... | []     = 0 , BQ .charge (` length back) (ret ([] , []))
... | x ∷ l  = x , BQ .charge (` length back) (ret ([] , l))

dequeueᵗ : BQ ⊸ (ℕₛ ⋊ BQ)
dequeueᵗ = bind' λ
  { (back , x ∷ front) → x , ret (back , front)
  ; (back , [])        → reverse-front back }

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
  empty-coherent = bind'/β ∙ F _ .charge/0

  enqueue-coherent :
    (e : ℕ) (q : U BQ)
    → φ .U (enqueueᵗ e .U q) ≡ enqueue e .U (φ .U q)
  enqueue-coherent e q =
      φ .U (enqueueᵗ e .U q)
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
      enqueue e .U (φ .U q)
    ∎
    where
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

opaque
  unfolding ℂ M F

  dequeue-coherent :
    (q : U BQ)
    → mapφ .U (dequeueᵗ .U q) ≡ dequeue .U (φ .U q)
  dequeue-coherent q =
    cong (λ f → f .U q)
      (bind'-path
        (dequeueᵗ ⨾ᶜ mapφ)
        (φ ⨾ᶜ dequeue)
        (funExt dequeue-lemma))
    where
      dequeue-lemma : (x : List ℕ × List ℕ)
        → (dequeueᵗ ⨾ᶜ mapφ) .U (ret x) ≡ (φ ⨾ᶜ dequeue) .U (ret x)
      dequeue-lemma (back , x ∷ front) =
          mapφ .U (dequeueᵗ .U (ret (back , x ∷ front)))
        ≡⟨ cong (mapφ .U)
             (bind'/β {A = ℕₛ ⋊ BQ} {x = back , x ∷ front}
               {k = λ { (b , z ∷ f) → z , ret (b , f) ; (b , []) → reverse-front b }}) ⟩
          (x , φ .U (ret (back , front)))
        ≡⟨ cong (x ,_)
             (bind'/β {A = LQ} {x = back , front}
               {k = λ (l₁ , l₂) → LQ .charge (` length l₁) (ret (l₂ ++ reverse l₁))}) ⟩
          (x , LQ .charge (` length back) (ret (front ++ reverse back)))
        ≡⟨ sym (cong ((ℕₛ ⋊ LQ) .charge (` length back))
             (bind'/β {A = ℕₛ ⋊ LQ} {x = x ∷ (front ++ reverse back)}
               {k = λ { [] → 0 , ret [] ; (z ∷ l) → z , ret l }})) ⟩
          (ℕₛ ⋊ LQ) .charge (` length back) (dequeue .U (ret (x ∷ (front ++ reverse back))))
        ≡⟨ sym (dequeue .charge (` length back) (ret (x ∷ (front ++ reverse back)))) ⟩
          dequeue .U (LQ .charge (` length back) (ret (x ∷ (front ++ reverse back))))
        ≡⟨ sym (cong (dequeue .U)
             (bind'/β {A = LQ} {x = back , x ∷ front}
               {k = λ (l₁ , l₂) → LQ .charge (` length l₁) (ret (l₂ ++ reverse l₁))})) ⟩
          dequeue .U (φ .U (ret (back , x ∷ front)))
        ∎
      dequeue-lemma (back , []) with reverse back
      ... | []    = refl
      ... | y ∷ l = λ i → y , length back + 0 + 0 , ∣ List.++-unit-r l i ∣₂


open import Cubical.Foundations.Equiv
open import Calf.Value.Open as ◯
open import Calf.Value.Closed as ●
open import Calf.Value.Glue
open import Calf.Value.Abstraction using (square')
open import Calf.Computation.Open as ◯ᶜ
open import Calf.Computation.Closed as ●ᶜ hiding (law)
open import Calf.Computation.Abstraction

BLQ : 𝒞
BLQ = Abstractionᶜ BQ LQ φ

empty' : U BLQ
empty' = triangleᶜ' emptyᵗ emptyq empty-coherent

enqueue' : ℕ → BLQ ⊸ BLQ
enqueue' e = squareᶜ' (enqueueᵗ e) (enqueue e) (enqueue-coherent e)

opaque
  unfolding Abstractionᶜ

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
