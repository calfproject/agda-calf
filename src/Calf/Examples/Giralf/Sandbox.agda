module Calf.Examples.Giralf.Sandbox where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Calf.Core.Cost
open import Calf.Value
open import Calf.Value.Nat
open import Calf.Computation.PList1
open import Calf.Computation.PList2
open import Calf.Computation.Debit
open import Calf.Computation.Power
open import Calf.Computation.Product
open import Calf.Giralf

open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order using (_≤_)
open import Cubical.Data.Vec
open import Calf.Computation


open import Cubical.Data.Bool
import Cubical.Data.Nat.Properties as Nat
open import Cubical.Data.Nat.Order
open import Cubical.Relation.Nullary

_≤ᵇ_ : ℕ → ℕ → Bool
m ≤ᵇ n with ≤Dec m n
... | yes p = true
... | no ¬p = false

opaque
  unfolding ℂ

  snoc : ∀ {l1 q2 : ℕ} → (val (1 + q2 ≤ᵛ l1)) → val X → PList₂ (` (l1)) (` (q2)) (X) , (` (((l1 ∸ 1) ∸ q2) + 0)) ⊢ PList₂ (` ((l1 ∸ 1) ∸ q2)) (` (q2)) (X)
  snoc {X} {l1} {q2} cs x1 =
    payᴳ refl $
    powappᴳ {X = 1 + q2 ≤ᵛ l1} {!   !} $
    foldr₂ᴳ (λ p5 → (1 + q2 ≤ᵛ p5) ⇀ (◁'[ (p5 ∸ 1) ∸ q2 ] (PList₂ ((p5 ∸ 1) ∸ q2) (q2) (X))))
      (λ p5 →
        powlamᴳ {X = 1 + q2 ≤ᵛ p5} $ λ cs4 →
        getᴳ ((p5 ∸ 1) ∸ q2) refl $
        cons₂ᴳ {q' = (((p5 ∸ 1) ∸ q2) + 0) ∸ ((p5 ∸ 1) ∸ q2)} {!   !} (x1) $ nil₂ᴳ {!   !})
      (λ p5 → λ xh3 →
        powlamᴳ {X = 1 + q2 ≤ᵛ p5} $ λ cs3 →
        getᴳ ((p5 ∸ 1) ∸ q2) refl $
        chargeᴳ {q' = (((p5 ∸ 1) ∸ q2) + p5) ∸ 1} 1 {!   !} $
        cons₂ᴳ {q' = ((((p5 ∸ 1) ∸ q2) + p5) ∸ 1) ∸ ((p5 ∸ 1) ∸ q2)} {!   !} (xh3) $
        substᵐᴳ {!   !} $
        subst2ᴳ (λ l q → PList₂ l q X) {!  !} {!   !} $
        payᴳ refl $
        powappᴳ {X = 1 + q2 ≤ᵛ q2 + p5} {!   !} $ idᴳ refl)
      (idᴳ refl)

  insert : ∀ {l1 q2 : ℕ} → (val (1 ≤ᵛ l1 ×ᵛ 1 + q2 ≤ᵛ l1)) → val ℕᵛ → PList₂ (` (l1)) (` (q2)) (ℕᵛ) , (` (((l1 ∸ 1) ∸ q2) + 0)) ⊢ PList₂ (` ((l1 ∸ 1) ∸ q2)) (` (q2)) (ℕᵛ)
  insert {l1} {q2} cs x1 =
    payᴳ {p = (l1 ∸ 1) ∸ q2} {q' = 0} refl $ proj₁ᴳ {B = ◁'[ 0 ] (PList₂ (l1 ∸ 1) (q2) (ℕᵛ))} $
    powappᴳ {X = 1 ≤ᵛ l1 ×ᵛ 1 + q2 ≤ᵛ l1} cs $
    foldr₂ᴳ (λ p5 → (1 ≤ᵛ p5 ×ᵛ 1 + q2 ≤ᵛ p5) ⇀ ((◁'[ (p5 ∸ 1) ∸ q2 ] (PList₂ ((p5 ∸ 1) ∸ q2) (q2) (ℕᵛ))) ×ᶜ (◁'[ 0 ] (PList₂ (p5 ∸ 1) (q2) (ℕᵛ)))))
      (λ p5 →
        powlamᴳ {X = 1 ≤ᵛ p5 ×ᵛ 1 + q2 ≤ᵛ p5} $ λ cs6 →
        pairᴳ (
          getᴳ {q' = ((p5 ∸ 1) ∸ q2) + 0} ((p5 ∸ 1) ∸ q2) refl $
          cons₂ᴳ {q' = (((p5 ∸ 1) ∸ q2) + 0) ∸ ((p5 ∸ 1) ∸ q2)} {!   !} (x1) $ nil₂ᴳ {!   !}
        ) (
          getᴳ {q' = 0 + 0} (0) refl $ nil₂ᴳ refl
        )
      )
      (λ p5 → λ xh3 →
        powlamᴳ {X = 1 ≤ᵛ p5 ×ᵛ 1 + q2 ≤ᵛ p5} $ λ cs5 →
        chargeᴳ {q' = p5 ∸ 1} 1 {!   !} $
        pairᴳ (
          getᴳ {q' = ((p5 ∸ 1) ∸ q2) + (p5 ∸ 1)} ((p5 ∸ 1) ∸ q2) refl $
          if ((x1) ≤ᵇ (xh3)) then (
            cons₂ᴳ {q' = (((p5 ∸ 1) ∸ q2) + (p5 ∸ 1)) ∸ ((p5 ∸ 1) ∸ q2)} {!   !} (x1) $
            cons₂ᴳ {q' = ((((p5 ∸ 1) ∸ q2) + (p5 ∸ 1)) ∸ ((p5 ∸ 1) ∸ q2)) ∸ (((p5 ∸ 1) ∸ q2) + q2)} {!   !} (xh3) $
            substᵐᴳ {!   !} $ subst2ᴳ (λ p23 p22 → PList₂ (p23) (p22) (ℕᵛ)) {!   !} {!   !} $
            payᴳ {p = 0} {q' = 0} refl $ proj₂ᴳ {A = ◁'[ ((q2 + p5) ∸ 1) ∸ q2 ] (PList₂ (((q2 + p5) ∸ 1) ∸ q2) (q2) (ℕᵛ))} $
            powappᴳ {X = 1 ≤ᵛ q2 + p5 ×ᵛ 1 + q2 ≤ᵛ q2 + p5} {!   !} $ idᴳ refl
          ) else (
            cons₂ᴳ {q' = (((p5 ∸ 1) ∸ q2) + (p5 ∸ 1)) ∸ ((p5 ∸ 1) ∸ q2)} {!   !} (xh3) $
            substᵐᴳ {!   !} $ subst2ᴳ (λ p21 p20 → PList₂ (p21) (p20) (ℕᵛ)) {!   !} {!   !} $
            payᴳ {p = ((q2 + p5) ∸ 1) ∸ q2} {q' = 0} refl $ proj₁ᴳ {B = ◁'[ 0 ] (PList₂ ((q2 + p5) ∸ 1) (q2) (ℕᵛ))} $
            powappᴳ {X = 1 ≤ᵛ q2 + p5 ×ᵛ 1 + q2 ≤ᵛ q2 + p5} {!   !} $ idᴳ refl
          )
        ) (
          getᴳ {q' = 0 + (p5 ∸ 1)} (0) refl $
          cons₂ᴳ {q' = (0 + (p5 ∸ 1)) ∸ (p5 ∸ 1)} {!   !} (xh3) $
          substᵐᴳ {!   !} $ subst2ᴳ (λ p19 p18 → PList₂ (p19) (p18) (ℕᵛ)) {!   !} {!   !} $
          payᴳ {p = 0} {q' = 0} refl $ proj₂ᴳ {A = ◁'[ ((q2 + p5) ∸ 1) ∸ q2 ] (PList₂ (((q2 + p5) ∸ 1) ∸ q2) (q2) (ℕᵛ))} $
          powappᴳ {X = 1 ≤ᵛ q2 + p5 ×ᵛ 1 + q2 ≤ᵛ q2 + p5} {!   !} $ idᴳ refl
        )
      )
      (idᴳ refl)


  reverse : ∀ {l1 q2 : ℕ} → (val (1 ≤ᵛ q2)) → PList₂ (` (l1)) (` (q2)) (X) , (` (0 + 0)) ⊢ PList₂ (` (l1)) (` (q2 ∸ 1)) (X)
  reverse {X} {l1} {q2} cs =
    payᴳ {p = 0} {q' = 0} refl $
    powappᴳ {X = 1 ≤ᵛ q2} {!   !} $
    foldr₂ᴳ (λ p17 → (1 ≤ᵛ q2) ⇀ (◁'[ 0 ] (PList₂ (p17) (q2 ∸ 1) (X))))
      (λ p17 →
        powlamᴳ {X = 1 ≤ᵛ q2} $ λ cs10 →
        getᴳ {q' = 0 + 0} (0) refl $ nil₂ᴳ {!   !}
      )
      (λ p17 → λ yh4 →
        powlamᴳ {X = 1 ≤ᵛ q2} $ λ cs7 →
        getᴳ {q' = 0 + p17} (0) refl $
        substᵐᴳ {!   !} $ subst2ᴳ (λ p28 p27 → PList₂ (p28) (p27) (X)) {!   !} {!   !} $
        payᴳ {p = ((q2 + p17) ∸ 1) ∸ (q2 ∸ 1)} {q' = 0 + 0} refl $
        powappᴳ {X = 1 + (q2 ∸ 1) ≤ᵛ q2 + p17} {!   !} $
        foldr₂ᴳ (λ p20 → (1 + (q2 ∸ 1) ≤ᵛ p20) ⇀ (◁'[ (p20 ∸ 1) ∸ (q2 ∸ 1) ] (PList₂ ((p20 ∸ 1) ∸ (q2 ∸ 1)) (q2 ∸ 1) (X))))
          (λ p20 →
            powlamᴳ {X = 1 + (q2 ∸ 1) ≤ᵛ p20} $ λ cs9 →
            getᴳ {q' = ((p20 ∸ 1) ∸ (q2 ∸ 1)) + 0} ((p20 ∸ 1) ∸ (q2 ∸ 1)) refl $
            cons₂ᴳ {q' = (((p20 ∸ 1) ∸ (q2 ∸ 1)) + 0) ∸ ((p20 ∸ 1) ∸ (q2 ∸ 1))} {!   !} (yh4) $ nil₂ᴳ {!   !}
          )
          (λ p20 → λ xh2 →
            powlamᴳ {X = 1 + (q2 ∸ 1) ≤ᵛ p20} $ λ cs8 →
            getᴳ {q' = ((p20 ∸ 1) ∸ (q2 ∸ 1)) + p20} ((p20 ∸ 1) ∸ (q2 ∸ 1)) refl $
            chargeᴳ {q' = (((p20 ∸ 1) ∸ (q2 ∸ 1)) + p20) ∸ 1} 1 {!   !} $
            cons₂ᴳ {q' = ((((p20 ∸ 1) ∸ (q2 ∸ 1)) + p20) ∸ 1) ∸ ((p20 ∸ 1) ∸ (q2 ∸ 1))} {!   !} (xh2) $
            substᵐᴳ {!   !} $ subst2ᴳ (λ p30 p29 → PList₂ (p30) (p29) (X)) {!   !} {!   !} $
            payᴳ {p = (((q2 ∸ 1) + p20) ∸ 1) ∸ (q2 ∸ 1)} {q' = 0} refl $
            powappᴳ {X = 1 + (q2 ∸ 1) ≤ᵛ (q2 ∸ 1) + p20} {!   !} $ idᴳ refl
          )
          (
            payᴳ {p = 0} {q' = 0} refl $
            powappᴳ {X = 1 ≤ᵛ q2} {!   !} $ idᴳ refl)
      )
      (idᴳ refl)


  isort : ∀ {l1 q2 : ℕ} → val (1 ≤ᵛ q2) → PList₂ (` (l1)) (` (q2)) (ℕᵛ) , (` (0 + 0)) ⊢ PList₂ (` (l1)) (` (q2 ∸ 1)) (ℕᵛ)
  isort {l1} {q2} cs =
    payᴳ {p = 0} {q' = 0} refl $
    powappᴳ {X = 1 ≤ᵛ q2} {!   !} $
    foldr₂ᴳ (λ p17 → (1 ≤ᵛ q2) ⇀ (◁'[ 0 ] (PList₂ (p17) (q2 ∸ 1) (ℕᵛ))))
      (λ p17 →
        powlamᴳ {X = 1 ≤ᵛ q2} $ λ cs12 →
        getᴳ {q' = 0 + 0} (0) refl $ nil₂ᴳ {!   !}
      )
      (λ p17 → λ yh4 →
        powlamᴳ {X = 1 ≤ᵛ q2} $ λ cs9 →
        getᴳ {q' = 0 + p17} (0) refl $
        substᵐᴳ {!   !} $ subst2ᴳ (λ p42 p41 → PList₂ (p42) (p41) (ℕᵛ)) {!   !} {!   !} $
        payᴳ {p = ((q2 + p17) ∸ 1) ∸ (q2 ∸ 1)} {q' = 0 + 0} refl $ proj₁ᴳ {B = ◁'[ 0 ] (PList₂ ((q2 + p17) ∸ 1) (q2 ∸ 1) (ℕᵛ))} $
        powappᴳ {X = 1 ≤ᵛ q2 + p17 ×ᵛ 1 + (q2 ∸ 1) ≤ᵛ q2 + p17} {!   !} $
        foldr₂ᴳ (λ p20 → (1 ≤ᵛ p20 ×ᵛ 1 + (q2 ∸ 1) ≤ᵛ p20) ⇀ ((◁'[ (p20 ∸ 1) ∸ (q2 ∸ 1) ] (PList₂ ((p20 ∸ 1) ∸ (q2 ∸ 1)) (q2 ∸ 1) (ℕᵛ))) ×ᶜ (◁'[ 0 ] (PList₂ (p20 ∸ 1) (q2 ∸ 1) (ℕᵛ)))))
          (λ p20 →
            powlamᴳ {X = 1 ≤ᵛ p20 ×ᵛ 1 + (q2 ∸ 1) ≤ᵛ p20} $ λ cs11 →
            pairᴳ (
              getᴳ {q' = ((p20 ∸ 1) ∸ (q2 ∸ 1)) + 0} ((p20 ∸ 1) ∸ (q2 ∸ 1)) refl $
              cons₂ᴳ {q' = (((p20 ∸ 1) ∸ (q2 ∸ 1)) + 0) ∸ ((p20 ∸ 1) ∸ (q2 ∸ 1))} {!   !} (yh4) $ nil₂ᴳ {!   !}
            ) (
              getᴳ {q' = 0 + 0} (0) refl $ nil₂ᴳ {!   !}
            )
          )
          (λ p20 → λ xh2 →
            powlamᴳ {X = 1 ≤ᵛ p20 ×ᵛ 1 + (q2 ∸ 1) ≤ᵛ p20} $ λ cs10 →
            chargeᴳ {q' = p20 ∸ 1} 1 {!   !} $
            pairᴳ (
              getᴳ {q' = ((p20 ∸ 1) ∸ (q2 ∸ 1)) + (p20 ∸ 1)} ((p20 ∸ 1) ∸ (q2 ∸ 1)) refl $
              if ((yh4) ≤ᵇ (xh2)) then (
                cons₂ᴳ {q' = (((p20 ∸ 1) ∸ (q2 ∸ 1)) + (p20 ∸ 1)) ∸ ((p20 ∸ 1) ∸ (q2 ∸ 1))} {!   !} (yh4) $
                cons₂ᴳ {q' = ((((p20 ∸ 1) ∸ (q2 ∸ 1)) + (p20 ∸ 1)) ∸ ((p20 ∸ 1) ∸ (q2 ∸ 1))) ∸ (((p20 ∸ 1) ∸ (q2 ∸ 1)) + (q2 ∸ 1))} {!   !} (xh2) $
                substᵐᴳ {!   !} $ subst2ᴳ (λ p48 p47 → PList₂ (p48) (p47) (ℕᵛ)) {!   !} {!   !} $
                payᴳ {p = 0} {q' = 0} refl $ proj₂ᴳ {A = ◁'[ (((q2 ∸ 1) + p20) ∸ 1) ∸ (q2 ∸ 1) ] (PList₂ ((((q2 ∸ 1) + p20) ∸ 1) ∸ (q2 ∸ 1)) (q2 ∸ 1) (ℕᵛ))} $
                powappᴳ {X = 1 ≤ᵛ (q2 ∸ 1) + p20 ×ᵛ 1 + (q2 ∸ 1) ≤ᵛ (q2 ∸ 1) + p20} {!   !} $ idᴳ refl
              ) else (
                cons₂ᴳ {q' = (((p20 ∸ 1) ∸ (q2 ∸ 1)) + (p20 ∸ 1)) ∸ ((p20 ∸ 1) ∸ (q2 ∸ 1))} {!   !} (xh2) $
                substᵐᴳ {!   !} $ subst2ᴳ (λ p46 p45 → PList₂ (p46) (p45) (ℕᵛ)) {!   !} {!   !} $
                payᴳ {p = (((q2 ∸ 1) + p20) ∸ 1) ∸ (q2 ∸ 1)} {q' = 0} refl $ proj₁ᴳ {B = ◁'[ 0 ] (PList₂ (((q2 ∸ 1) + p20) ∸ 1) (q2 ∸ 1) (ℕᵛ))} $
                powappᴳ {X = 1 ≤ᵛ (q2 ∸ 1) + p20 ×ᵛ 1 + (q2 ∸ 1) ≤ᵛ (q2 ∸ 1) + p20} {!   !} $ idᴳ refl
              )
            ) (
              getᴳ {q' = 0 + (p20 ∸ 1)} (0) refl $
              cons₂ᴳ {q' = (0 + (p20 ∸ 1)) ∸ (p20 ∸ 1)} {!   !} (xh2) $
              substᵐᴳ {!   !} $ subst2ᴳ (λ p44 p43 → PList₂ (p44) (p43) (ℕᵛ)) {!   !} {!   !} $
              payᴳ {p = 0} {q' = 0} refl $ proj₂ᴳ {A = ◁'[ (((q2 ∸ 1) + p20) ∸ 1) ∸ (q2 ∸ 1) ] (PList₂ ((((q2 ∸ 1) + p20) ∸ 1) ∸ (q2 ∸ 1)) (q2 ∸ 1) (ℕᵛ))} $
              powappᴳ {X = 1 ≤ᵛ (q2 ∸ 1) + p20 ×ᵛ 1 + (q2 ∸ 1) ≤ᵛ (q2 ∸ 1) + p20} {!   !} $ idᴳ refl
            )
          )
          (
            payᴳ {p = 0} {q' = 0} refl $
            powappᴳ {X = 1 ≤ᵛ q2} {!   !} $ idᴳ refl)
      )
      (idᴳ refl)