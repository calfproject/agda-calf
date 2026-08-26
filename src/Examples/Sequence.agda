{-# OPTIONS --prop --rewriting #-}

module Examples.Sequence where

open import Algebra.Cost

parCostMonoid = ℕ²-ParCostMonoid
open ParCostMonoid parCostMonoid

open import Calf costMonoid
open import Calf.Parallel parCostMonoid

open import Calf.Data.Product
open import Calf.Data.Sum
open import Calf.Data.Bool
open import Calf.Data.Maybe
open import Calf.Data.Nat hiding (compare)
open import Calf.Data.List hiding (filter; find)

open import Level using (0ℓ)
open import Relation.Binary
open import Data.Nat as Nat using (_<_; _+_)
import Data.Nat.Properties as Nat
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Function using (case_of_; _$_)

open import Examples.Sequence.MSequence
open import Examples.Sequence.ListMSequence
open import Examples.Sequence.RedBlackMSequence
open import Examples.Sequence.DerivedFormsRBT


module Ex/FromList where
  open MSequence RedBlackMSequence

  fromList : cmp (Π (list nat) λ _ → F (seq nat))
  fromList [] = empty
  fromList (x ∷ l) =
    bind (F (seq nat)) empty λ s₁ →
    bind (F (seq nat)) (fromList l) λ s₂ →
    join s₁ x s₂

  example : cmp (F (seq nat))
  example = fromList (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [])


module BinarySearchTree
  (MSeq : MSequence)
  (Key : StrictTotalOrder 0ℓ 0ℓ 0ℓ)
  where

  open StrictTotalOrder Key

  𝕂 : tp⁺
  𝕂 = meta⁺ (StrictTotalOrder.Carrier Key)

  open MSequence MSeq public

  singleton : cmp (Π 𝕂 λ _ → F (seq 𝕂))
  singleton a =
    bind (F (seq 𝕂)) empty λ t →
    join t a t

  Split : tp⁻
  Split = F ((seq 𝕂) ×⁺ ((maybe 𝕂) ×⁺ (seq 𝕂)))

  split : cmp (Π (seq 𝕂) λ _ → Π 𝕂 λ _ → Split)
  split t a =
    rec
      {X = Split}
      (bind Split empty λ t →
        ret (t , nothing , t))
      (λ t₁ ih₁ a' t₂ ih₂ →
        case compare a a' of λ
          { (tri< a<a' ¬a≡a' ¬a>a') →
              bind Split ih₁ λ ( t₁₁ , a? , t₁₂ ) →
              bind Split (join t₁₂ a' t₂) λ t →
              ret (t₁₁ , a? , t)
          ; (tri≈ ¬a<a' a≡a' ¬a>a') → ret (t₁ , just a' , t₂)
          ; (tri> ¬a<a' ¬a≡a' a>a') →
              bind Split ih₂ λ ( t₂₁ , a? , t₂₂ ) →
              bind Split (join t₁ a' t₂₁) λ t →
              ret (t , a? , t₂₂)
          })
      t

  find : cmp (Π (seq 𝕂) λ _ → Π 𝕂 λ _ → F (maybe 𝕂))
  find t a = bind (F (maybe 𝕂)) (split t a) λ { (_ , a? , _) → ret a? }

  insert : cmp (Π (seq 𝕂) λ _ → Π 𝕂 λ _ → F (seq 𝕂))
  insert t a = bind (F (seq 𝕂)) (split t a) λ { (t₁ , _ , t₂) → join t₁ a t₂ }

  append : cmp (Π (seq 𝕂) λ _ → Π (seq 𝕂) λ _ → F (seq 𝕂))
  append t₁ t₂ =
    rec
      {X = F (seq 𝕂)}
      (ret t₂)
      (λ t'₁ ih₁ a' t'₂ ih₂ →
        bind (F (seq 𝕂)) ih₂ λ t' →
        join t'₁ a' t')
    t₁

  delete : cmp (Π (seq 𝕂) λ _ → Π 𝕂 λ _ → F (seq 𝕂))
  delete t a = bind (F (seq 𝕂)) (split t a) λ { (t₁ , _ , t₂) → append t₁ t₂ }

  union : cmp (Π (seq 𝕂) λ _ → Π (seq 𝕂) λ _ → F (seq 𝕂))
  union =
    rec
      {X = Π (seq 𝕂) λ _ → F (seq 𝕂)}
      ret
      λ t'₁ ih₁ a' t'₂ ih₂ t₂ →
        bind (F (seq 𝕂)) (split t₂ a') λ { (t₂₁ , a? , t₂₂) →
        bind (F (seq 𝕂)) ((ih₁ t₂₁) ∥ (ih₂ t₂₂)) λ (s₁ , s₂) →
        join s₁ a' s₂ }

  intersection : cmp (Π (seq 𝕂) λ _ → Π (seq 𝕂) λ _ → F (seq 𝕂))
  intersection =
    rec
      {X = Π (seq 𝕂) λ _ → F (seq 𝕂)}
      (λ t₂ → empty)
      λ t'₁ ih₁ a' t'₂ ih₂ t₂ →
        bind (F (seq 𝕂)) (split t₂ a') λ { (t₂₁ , a? , t₂₂) →
        bind (F (seq 𝕂)) ((ih₁ t₂₁) ∥ (ih₂ t₂₂)) λ (s₁ , s₂) →
          case a? of
            λ { (just a) → join s₁ a s₂
              ; nothing → append s₁ s₂ }
        }

  difference : cmp (Π (seq 𝕂) λ _ → Π (seq 𝕂) λ _ → F (seq 𝕂))
  difference t₁ t₂ = helper t₁
    where
      helper : cmp (Π (seq 𝕂) λ _ → F (seq 𝕂))
      helper =
        rec
          {X = Π (seq 𝕂) λ _ → F (seq 𝕂)}
          ret
          (λ t'₁ ih₁ a' t'₂ ih₂ t₁ →
            bind (F (seq 𝕂)) (split t₁ a') λ { (t₁₁ , a? , t₁₂) →
            bind (F (seq 𝕂)) ((ih₁ t₁₁) ∥ (ih₂ t₁₂)) λ (s₁ , s₂) →
            append s₁ s₂
            })
        t₂

  filter : cmp (Π (seq 𝕂) λ _ → Π (U (Π 𝕂 λ _ → F bool)) λ _ → F (seq 𝕂))
  filter t f =
    rec
      {X = F (seq 𝕂)}
      (bind (F (seq 𝕂)) empty ret)
      (λ t'₁ ih₁ a' t'₂ ih₂ →
        bind (F (seq 𝕂)) (ih₁ ∥ ih₂) (λ (s₁ , s₂) →
        bind (F (seq 𝕂)) (f a') λ b →
          if b then (join s₁ a' s₂) else (append s₁ s₂)))
    t

  mapreduce : {X : tp⁻} →
    cmp (
      Π (seq 𝕂) λ _ →
      Π (U (Π 𝕂 λ _ → X)) λ _ →
      Π (U (Π (U X) λ _ → Π (U X) λ _ → X)) λ _ →
      Π (U X) λ _ →
      X
    )
  mapreduce {X} t g f l =
    rec {X = X} l (λ t'₁ ih₁ a' t'₂ ih₂ → f ih₁ (f (g a') ih₂)) t


module Ex/NatSet where
  open BinarySearchTree RedBlackMSequence Nat.<-strictTotalOrder

  example : cmp Split
  example =
    bind Split (singleton 1) λ t₁ →
    bind Split (insert t₁ 2) λ t₁ →
    bind Split (singleton 4) λ t₂ →
    bind Split (join t₁ 3 t₂) λ t →
    split t 2

  sum/seq : cmp (Π (seq nat) λ _ → F (nat))
  sum/seq =
    rec
      {X = F (nat)}
      (ret 0)
      λ t'₁ ih₁ a' t'₂ ih₂ →
        step (F nat) (1 , 1) $
        bind (F (nat)) (ih₁ ∥ ih₂)
        (λ (s₁ , s₂) → ret (s₁ + a' + s₂))



module Ex/NatStringDict where
  strictTotalOrder : StrictTotalOrder 0ℓ 0ℓ 0ℓ
  strictTotalOrder =
    record
      { Carrier = ℕ × String
      ; _≈_ = λ (n₁ , _) (n₂ , _) → n₁ ≡ n₂
      ; _<_ = λ (n₁ , _) (n₂ , _) → n₁ Nat.< n₂
      ; isStrictTotalOrder =
          record
            { isStrictPartialOrder =
                record
                  { isEquivalence =
                      record
                        { refl = Eq.refl
                        ; sym = Eq.sym
                        ; trans = Eq.trans
                        }
                  ; irrefl = Nat.<-irrefl
                  ; trans = Nat.<-trans
                  ; <-resp-≈ = (λ { Eq.refl h → h }) , (λ { Eq.refl h → h })
                  }
            ; compare = λ (n₁ , _) (n₂ , _) → Nat.<-cmp n₁ n₂
            }
      }

  open BinarySearchTree RedBlackMSequence strictTotalOrder

  example : cmp Split
  example =
    bind Split (singleton (1 , "red")) λ t₁ →
    bind Split (insert t₁ (2 , "orange")) λ t₁ →
    bind Split (singleton (4 , "green")) λ t₂ →
    bind Split (join t₁ (3 , "yellow") t₂) λ t →
    split t (2 , "")
