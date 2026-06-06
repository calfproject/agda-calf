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
  bind (l₁ , l₂) ← idᶜ ⨾
  LQ .charge (` length l₁) (ret (l₂ ++ reverse l₁))

emptyq : cmp LQ
emptyq = ret []

enqueue : val ℕᵛ → LQ ⊸ LQ
enqueue e = bind' λ l → LQ .charge 1 (ret (l ++ [ e ]))

dequeue : LQ ⊸ (ℕᵛ ⋊ LQ)
dequeue = bind' λ
  { []      → 0 , ret []
  ; (x ∷ l) → x , ret l }

emptyᵗ : cmp BQ
emptyᵗ = ret ([] , [])

enqueueᵗ : val ℕᵛ → BQ ⊸ BQ
enqueueᵗ e = bind' λ (back , front) → ret (e ∷ back , front)

dequeueᵗ : BQ ⊸ (ℕᵛ ⋊ BQ)
dequeueᵗ = bind' λ
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
BLQ = Glueᶜ' BQ LQ φ

empty' : cmp BLQ
empty' = triangleᶜ' {B-⊤ = BQ} {B-abs = LQ} {β = φ} emptyᵗ emptyq empty-coherent

enqueue' : val ℕᵛ → BLQ ⊸ BLQ
enqueue' e = squareᶜ' (enqueueᵗ e) (enqueue e) (enqueue-coherent e)

opaque
  unfolding Glueᶜ'

  dequeue'-fst-glue : cmp BLQ → val (𝒱-fromFRAC (𝒱-toFRAC ℕᵛ))
  dequeue'-fst-glue =
    squareᵛ'
      {X-⊤ = U BQ} {X-abs = U LQ} {χ = φ .U}
      {Y-⊤ = ℕᵛ} {Y-abs = ℕᵛ} {ψ = λ n → n}
      (λ bq → fst (dequeueᵗ .U bq))
      (λ lq → fst (dequeue .U lq))
      (λ q → cong fst (dequeue-coherent q))

  dequeue'-snd : BLQ ⊸ BLQ
  dequeue'-snd = squareᶜ' dequeueᵗ-snd dequeue-snd (λ q → cong snd (dequeue-coherent q))

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

  dequeue' : BLQ ⊸ (ℕᵛ ⋊ BLQ)
  dequeue' .U q .fst =
    invEq (fracture , fracture-isEquiv) (dequeue'-fst-glue q)
  dequeue' .U q .snd = dequeue'-snd .U q
  dequeue' .charge c q =
    ΣPathP
      ( cong (invEq (fracture , fracture-isEquiv)) (dequeue'-fst-glue-charge c q)
      , dequeue'-snd .charge c q
      )


open import Calf.Value.Unit
open import Calf.Computation.Product
open import Calf.Computation.Cost
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

-- open import Cubical.Data.Bool
-- open import Cubical.Data.Nat.Order
-- open import Cubical.Relation.Nullary

-- _≤ᵇ_ : ℕ → ℕ → Bool
-- m ≤ᵇ n with ≤Dec m n
-- ... | yes p = true
-- ... | no ¬p = false

-- opaque
--   unfolding ℂ

--   foo : F 1ᵛ ⊸ PList₂ 1 1 1ᵛ
--   foo = bind' λ _ →
--     pcons₂ tt .U (store' .U
--       (pcons₂ tt .U (store' .U
--         (pcons₂ tt .U (store' .U pnil₂)))))

--   release-part : ∀ c c' → ▷'[ c +ℂ c' ] A ⊸ ▷'[ c ] A
--   release-part {A} c c' =
--     subst (_⊸ ▷'[ c ] A)
--       (sym (▷'/+ {c} {c'}))
--       (▷'-map release')

--   id₁ : ∀ c → PList₁ (c +ℂ 1) X ⊸ PList₁ c X
--   id₁ {X} c =
--     pfoldr₁
--       pnil₁
--       (λ x → release-part c 1 ⨾ᶜ pcons₁ x)

--   commute-linear₁
--     : (▷'[ c ] (PList₁ (c +ℂ 1) X) ⊸ PList₁ c X)
--     → (▷'[ c ] (PList₁ (1 +ℂ c) X) ⊸ PList₁ c X)
--   commute-linear₁ {c} {X} =
--     subst (λ A → ▷'[ c ] A ⊸ PList₁ c X)
--       (cong (λ c-lin → PList₁ c-lin X) (+ℂ-comm c 1))

--   id₂ : ∀ c → PList₂ c 1 X ⊸ PList₁ c X
--   id₂ {X} c =
--     pfoldr₂
--       (λ c-lin → PList₁ c-lin X)
--       (λ c-lin → pnil₁)
--       (λ c-lin x → commute-linear₁ (▷'-map (id₁ c-lin) ⨾ᶜ pcons₁ x))

--   snoc : val X → ▷'[ c ] (PList₁ (c +ℂ 1) X) ⊸ PList₁ c X
--   snoc {X} {c} x = transport pot-cost $
--     pfoldr₁
--       (▷'-map (bind' λ _ → pnil₁) ⨾ᶜ pcons₁ x)
--       (λ y → release-part c 1 ⨾ᶜ (pot-cost-counit ⨾ᶜ transport (sym pot-cost) (pcons₁ y)))

--   quadratic-reverse : PList₂ 0 1 X ⊸ PList₁ 0 X
--   quadratic-reverse {X} =
--     pfoldr₂
--       (λ c-lin → PList₁ c-lin X)
--       (λ c-lin → pnil₁)
--       (λ c-lin x → commute-linear₁ (snoc x))

--   insert : val ℕᵛ → ▷'[ c ] (PList₁ (c +ℂ 1) ℕᵛ) ⊸ PList₁ c ℕᵛ
--   insert {c} x = transport pot-cost $
--     pfoldr₁
--       (▷'-map (bind' λ _ → pnil₁) ⨾ᶜ pcons₁ x , pnil₁)
--       (λ y → release-part c 1 ⨾ᶜ
--         pairᶜ
--           (if x ≤ᵇ y
--             then ▷'-map proj₂ᶜ ⨾ᶜ transport (sym pot-cost) (▷'-map (pcons₁ y) ⨾ᶜ pcons₁ x)
--             else ▷'-map (proj₁ᶜ {B = PList₁ c ℕᵛ}) ⨾ᶜ pot-cost-counit ⨾ᶜ transport (sym pot-cost) (pcons₁ y)
--           )
--           (▷'-map proj₂ᶜ ⨾ᶜ pcons₁ y)
--       )
--     ⨾ᶜ proj₁ᶜ

--   isort : PList₂ 0 1 ℕᵛ ⊸ PList₁ 0 ℕᵛ
--   isort =
--     pfoldr₂
--       (λ c-lin → PList₁ c-lin ℕᵛ)
--       (λ c-lin → pnil₁)
--       (λ c-lin x → commute-linear₁ (insert x))
