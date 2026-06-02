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


open import Cubical.Foundations.Equiv
open import Calf.Computation.Open as ◯ᶜ
open import Calf.Computation.Closed as ●ᶜ hiding (law)
open import Calf.Computation.Glue
open import Calf.Value.Open as ◯ᵛ
open import Calf.Value.Closed as ●ᵛ

BLQ : 𝒞
BLQ = Glueᶜ (●ᶜ BQ , ●ᶜ-η•ᶜ-isEquiv {BQ}) (◯ᶜ LQ , ◯ᶜ-ηᶜ-isEquiv) (●ᶜ.map (φ ⨾⊸ η◦ᶜ))

empty' : cmp BLQ
empty' .• = η•ᵛ {U BQ} emptyᵗ
empty' .◦ = η◦ᵛ {U LQ} emptyq
empty' .•→◦ = cong (λ q → η•ᵛ {◯ᵛ (U LQ)} (η◦ᵛ {U LQ} q)) empty-coherent

enqueue' : val ℕᵛ → BLQ ⊸ BLQ
enqueue' e .U q .• = ●ᵛ.map (enqueueᵗ e .U) (q .•)
enqueue' e .U q .◦ = ◯ᵛ.map (enqueue e .U) (q .◦)
enqueue' e .U q .•→◦ =
    ●ᵛ.map (λ bq → η◦ᵛ {U LQ} (φ .U bq)) (●ᵛ.map (enqueueᵗ e .U) (q .•))
  ≡⟨ ●ᵛ.●-map-∘ (enqueueᵗ e .U) (λ bq → η◦ᵛ {U LQ} (φ .U bq)) (q .•) ⟩
    ●ᵛ.map (λ bq → η◦ᵛ {U LQ} (φ .U (enqueueᵗ e .U bq))) (q .•)
  ≡⟨ cong (λ h → ●ᵛ.map h (q .•)) (funExt λ bq → funExt λ _ → enqueue-coherent e bq) ⟩
    ●ᵛ.map (λ bq → ◯ᵛ.map (enqueue e .U) (η◦ᵛ {U LQ} (φ .U bq))) (q .•)
  ≡⟨ sym (●ᵛ.●-map-∘ (λ bq → η◦ᵛ {U LQ} (φ .U bq)) (◯ᵛ.map (enqueue e .U)) (q .•)) ⟩
    ●ᵛ.map (◯ᵛ.map (enqueue e .U)) (●ᵛ.map (λ bq → η◦ᵛ {U LQ} (φ .U bq)) (q .•))
  ≡⟨ cong (●ᵛ.map (◯ᵛ.map (enqueue e .U))) (q .•→◦) ⟩
    ●ᵛ.map (◯ᵛ.map (enqueue e .U)) (η•ᵛ {◯ᵛ (U LQ)} (q .◦))
  ≡⟨ refl ⟩
    η•ᵛ {◯ᵛ (U LQ)} (◯ᵛ.map (enqueue e .U) (q .◦))
  ∎
enqueue' e .charge c q i .• = ●ᶜ.map (enqueueᵗ e) .charge c (q .•) i
enqueue' e .charge c q i .◦ p = enqueue e .charge c (q .◦ p) i
enqueue' e .charge c q i .•→◦ =
  isProp→PathP
    (λ i → ●ᶜ (◯ᶜ LQ) .U .is-set
      (●ᵛ.map (λ bq → η◦ᵛ {U LQ} (φ .U bq))
        (●ᶜ.map (enqueueᵗ e) .charge c (q .•) i))
      (η•ᵛ {◯ᵛ (U LQ)} (λ p → enqueue e .charge c (q .◦ p) i)))
    (enqueue' e .U (BLQ .charge c q) .•→◦)
    (BLQ .charge c (enqueue' e .U q) .•→◦)
    i

dequeue'-fst-glue : cmp BLQ → val (𝒱-fromFRAC (𝒱-toFRAC ℕᵛ))
dequeue'-fst-glue q .• = ●ᵛ.map (λ bq → fst (dequeueᵗ .U bq)) (q .•)
dequeue'-fst-glue q .◦ = ◯ᵛ.map (λ lq → fst (dequeue .U lq)) (q .◦)
dequeue'-fst-glue q .•→◦ =
    ●ᵛ.map (η◦ᵛ {ℕᵛ}) (●ᵛ.map (λ bq → fst (dequeueᵗ .U bq)) (q .•))
  ≡⟨ ●ᵛ.●-map-∘ (λ bq → fst (dequeueᵗ .U bq)) (η◦ᵛ {ℕᵛ}) (q .•) ⟩
    ●ᵛ.map (λ bq → η◦ᵛ {ℕᵛ} (fst (dequeueᵗ .U bq))) (q .•)
  ≡⟨ cong (λ h → ●ᵛ.map h (q .•)) (funExt λ bq → funExt λ _ → cong fst (dequeue-coherent bq)) ⟩
    ●ᵛ.map (λ bq → η◦ᵛ {ℕᵛ} (fst (dequeue .U (φ .U bq)))) (q .•)
  ≡⟨ sym (●ᵛ.●-map-∘ (λ bq → η◦ᵛ {U LQ} (φ .U bq)) (◯ᵛ.map (λ lq → fst (dequeue .U lq))) (q .•)) ⟩
    ●ᵛ.map (◯ᵛ.map (λ lq → fst (dequeue .U lq))) (●ᵛ.map (λ bq → η◦ᵛ {U LQ} (φ .U bq)) (q .•))
  ≡⟨ cong (●ᵛ.map (◯ᵛ.map (λ lq → fst (dequeue .U lq)))) (q .•→◦) ⟩
    ●ᵛ.map (◯ᵛ.map (λ lq → fst (dequeue .U lq))) (η•ᵛ {◯ᵛ (U LQ)} (q .◦))
  ≡⟨ refl ⟩
    η•ᵛ {◯ᵛ ℕᵛ} (◯ᵛ.map (λ lq → fst (dequeue .U lq)) (q .◦))
  ∎

dequeue'-snd : cmp BLQ → cmp BLQ
dequeue'-snd q .• = ●ᵛ.map (λ bq → snd (dequeueᵗ .U bq)) (q .•)
dequeue'-snd q .◦ = ◯ᵛ.map (λ lq → snd (dequeue .U lq)) (q .◦)
dequeue'-snd q .•→◦ =
    ●ᵛ.map (λ bq → η◦ᵛ {U LQ} (φ .U bq)) (●ᵛ.map (λ bq → snd (dequeueᵗ .U bq)) (q .•))
  ≡⟨ ●ᵛ.●-map-∘ (λ bq → snd (dequeueᵗ .U bq)) (λ bq → η◦ᵛ {U LQ} (φ .U bq)) (q .•) ⟩
    ●ᵛ.map (λ bq → η◦ᵛ {U LQ} (φ .U (snd (dequeueᵗ .U bq)))) (q .•)
  ≡⟨ cong (λ h → ●ᵛ.map h (q .•)) (funExt λ bq → funExt λ _ → cong snd (dequeue-coherent bq)) ⟩
    ●ᵛ.map (λ bq → η◦ᵛ {U LQ} (snd (dequeue .U (φ .U bq)))) (q .•)
  ≡⟨ sym (●ᵛ.●-map-∘ (λ bq → η◦ᵛ {U LQ} (φ .U bq)) (◯ᵛ.map (λ lq → snd (dequeue .U lq))) (q .•)) ⟩
    ●ᵛ.map (◯ᵛ.map (λ lq → snd (dequeue .U lq))) (●ᵛ.map (λ bq → η◦ᵛ {U LQ} (φ .U bq)) (q .•))
  ≡⟨ cong (●ᵛ.map (◯ᵛ.map (λ lq → snd (dequeue .U lq)))) (q .•→◦) ⟩
    ●ᵛ.map (◯ᵛ.map (λ lq → snd (dequeue .U lq))) (η•ᵛ {◯ᵛ (U LQ)} (q .◦))
  ≡⟨ refl ⟩
    η•ᵛ {◯ᵛ (U LQ)} (◯ᵛ.map (λ lq → snd (dequeue .U lq)) (q .◦))
  ∎

dequeueᵗ-fst-●-charge
  : (c : val ℂ) (q• : val (●ᶜ BQ .U))
  → ●ᵛ.map (λ bq → fst (dequeueᵗ .U bq)) (●ᶜ BQ .charge c q•)
    ≡ ●ᵛ.map (λ bq → fst (dequeueᵗ .U bq)) q•
dequeueᵗ-fst-●-charge c (η• bq) = cong (η•ᵛ {ℕᵛ}) (cong fst (dequeueᵗ .charge c bq))
dequeueᵗ-fst-●-charge c (∗ p) = refl
dequeueᵗ-fst-●-charge c (law bq p i) =
  isProp→PathP
    (λ i → ●ᵛ ℕᵛ .is-set
      (●ᵛ.map (λ bq → fst (dequeueᵗ .U bq)) (●ᶜ BQ .charge c (law bq p i)))
      (●ᵛ.map (λ bq → fst (dequeueᵗ .U bq)) (law bq p i)))
    (cong (η•ᵛ {ℕᵛ}) (cong fst (dequeueᵗ .charge c bq)))
    refl
    i

dequeue-fst-◯-charge
  : (c : val ℂ) (q◦ : val (◯ᶜ LQ .U))
  → ◯ᵛ.map (λ lq → fst (dequeue .U lq)) (◯ᶜ LQ .charge c q◦)
    ≡ ◯ᵛ.map (λ lq → fst (dequeue .U lq)) q◦
dequeue-fst-◯-charge c q◦ i p = cong fst (dequeue .charge c (q◦ p)) i

dequeueᵗ-snd-●-charge
  : (c : val ℂ) (q• : val (●ᶜ BQ .U))
  → ●ᵛ.map (λ bq → snd (dequeueᵗ .U bq)) (●ᶜ BQ .charge c q•)
    ≡ ●ᶜ BQ .charge c (●ᵛ.map (λ bq → snd (dequeueᵗ .U bq)) q•)
dequeueᵗ-snd-●-charge c (η• bq) = cong (η•ᵛ {U BQ}) (cong snd (dequeueᵗ .charge c bq))
dequeueᵗ-snd-●-charge c (∗ p) = refl
dequeueᵗ-snd-●-charge c (law bq p i) =
  isProp→PathP
    (λ i → ●ᶜ BQ .U .is-set
      (●ᵛ.map (λ bq → snd (dequeueᵗ .U bq)) (●ᶜ BQ .charge c (law bq p i)))
      (●ᶜ BQ .charge c (●ᵛ.map (λ bq → snd (dequeueᵗ .U bq)) (law bq p i))))
    (cong (η•ᵛ {U BQ}) (cong snd (dequeueᵗ .charge c bq)))
    refl
    i

dequeue-snd-◯-charge
  : (c : val ℂ) (q◦ : val (◯ᶜ LQ .U))
  → ◯ᵛ.map (λ lq → snd (dequeue .U lq)) (◯ᶜ LQ .charge c q◦)
    ≡ ◯ᶜ LQ .charge c (◯ᵛ.map (λ lq → snd (dequeue .U lq)) q◦)
dequeue-snd-◯-charge c q◦ i p = cong snd (dequeue .charge c (q◦ p)) i

dequeue'-fst-glue-charge
  : (c : val ℂ) (q : cmp BLQ)
  → dequeue'-fst-glue (BLQ .charge c q) ≡ dequeue'-fst-glue q
dequeue'-fst-glue-charge c q i .• = dequeueᵗ-fst-●-charge c (q .•) i
dequeue'-fst-glue-charge c q i .◦ = dequeue-fst-◯-charge c (q .◦) i
dequeue'-fst-glue-charge c q i .•→◦ =
  isProp→PathP
    (λ i → ●ᵛ (◯ᵛ ℕᵛ) .is-set
      (●ᵛ.map (η◦ᵛ {ℕᵛ}) (dequeueᵗ-fst-●-charge c (q .•) i))
      (η•ᵛ {◯ᵛ ℕᵛ} (dequeue-fst-◯-charge c (q .◦) i)))
    (dequeue'-fst-glue (BLQ .charge c q) .•→◦)
    (dequeue'-fst-glue q .•→◦)
    i

dequeue'-snd-charge
  : (c : val ℂ) (q : cmp BLQ)
  → dequeue'-snd (BLQ .charge c q) ≡ BLQ .charge c (dequeue'-snd q)
dequeue'-snd-charge c q i .• = dequeueᵗ-snd-●-charge c (q .•) i
dequeue'-snd-charge c q i .◦ = dequeue-snd-◯-charge c (q .◦) i
dequeue'-snd-charge c q i .•→◦ =
  isProp→PathP
    (λ i → ●ᶜ (◯ᶜ LQ) .U .is-set
      (●ᵛ.map (λ bq → η◦ᵛ {U LQ} (φ .U bq)) (dequeueᵗ-snd-●-charge c (q .•) i))
      (η•ᵛ {◯ᵛ (U LQ)} (dequeue-snd-◯-charge c (q .◦) i)))
    (dequeue'-snd (BLQ .charge c q) .•→◦)
    (BLQ .charge c (dequeue'-snd q) .•→◦)
    i

dequeue' : BLQ ⊸ (ℕᵛ ⋊ BLQ)
dequeue' .U q .fst =
  invEq (fracture , fracture-isEquiv) (dequeue'-fst-glue q)
dequeue' .U q .snd = dequeue'-snd q
dequeue' .charge c q =
  ΣPathP
    ( cong (invEq (fracture , fracture-isEquiv)) (dequeue'-fst-glue-charge c q)
    , dequeue'-snd-charge c q
    )


open import Calf.Value.Unit
open import Calf.Computation.Potential
open import Calf.Computation.PList1
open import Calf.Computation.PList2
open import Cubical.Data.Nat

-- open import Cubical.Data.Nat.Order

-- open import Relation.Binary.PropositionalEquality as Eq using (refl)

-- (x ≡ᵛ x') .val = Eq._≡_ x x'
-- _≡ᵛ_ {X} x x' .is-set = {!   !} -- isProp→isSet (X .is-set x x')

-- _≤ᵛ_ : val ℂ → val ℂ → 𝒱
-- c ≤ᵛ c' = fromProp ((c ≤ c') , isProp≤)


opaque
  unfolding ℂ

  foo : F 1ᵛ ⊸ PList2 1 1 1ᵛ
  foo = bind' id⊸ (λ _ → pnil) ⨾⊸ pcons' tt ⨾⊸ pcons' tt ⨾⊸ pcons' tt

  id₁ : ∀ c → PList1 (c +ℂ 1) X ⊸ PList1 c X
  id₁ {X} c =
    pfoldr₁
      pnil₁
      (λ x → release-part 1 ⨾⊸ pcons₁ x)
    where
      release-part : ∀ c' → ▷'[ c + c' ] A ⊸ ▷'[ c ] A
      release-part = {!   !}

  id₂ : PList2 0 1 X ⊸ PList1 0 X
  id₂ {X} =
    pfoldr
      (λ c-lin → PList1 c-lin X)
      (λ c-lin → pnil₁)
      (λ c-lin x → ▷'-map (id₁ c-lin) ⨾⊸ pcons₁ x)
