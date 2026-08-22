module Examples.Giralf.Reverse where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Calf.Core.Cost
open import Calf.Value
open import Calf.Value.List
open import Calf.Computation
open import Calf.Computation.Lolli
open import Calf.Computation.CList1
open import Calf.Computation.CList2
open import Calf.Giralf
open import Calf.Solver.Nat using (solveNat0)

module _ (impl : Giralf) where
  open Giralf impl

  opaque
    unfolding ℂ

    snoc : ∀ p → A ∷ [ CList₁ᴳ (1 +ℂ p) A ] ⨾ p ⊢ CList₁ᴳ p A
    snoc {A} p =
      ⊸-appᴳ (left all-right) (+ℂ-identityʳ p)
        (storeᴳ p (+ℂ-identityʳ p) (idᴳ refl)) $
        foldr₁ᴳ
          {B = ▷ᴳ[ p ] A ⊸ᶜ CList₁ᴳ p A}
          (
            ⊸-lamᴳ $ releaseᴳ all-left (+ℂ-identityˡ _) (idᴳ refl) $
            cons₁ᴳ all-left arith (idᴳ refl) (nil₁ᴳ refl)
          )
          (
            spendᴳ 1 refl $
            ⊸-lamᴳ $ cons₁ᴳ (right (left all-right)) arith (idᴳ refl) $
            ⊸-appᴳ (left all-right) refl (idᴳ refl) (idᴳ refl)
          )
          (idᴳ refl)
      where
        arith : p ⋎₂ (p , (0ℂ +ℂ (0ℂ +ℂ 0ℂ)))
        arith = solveNat0


    qreverse : [ CList₂ᴳ 0 1 A ] ⨾ 0ℂ ⊢ CList₁ᴳ 0 A
    qreverse {A} =
      foldr₂ᴳ
        (λ r → CList₁ᴳ r A)
        (λ r → nil₁ᴳ refl)
        snoc
        (idᴳ refl)
