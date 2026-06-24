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
open import Calf.Giralf

open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order using (_≤_)
open import Calf.Computation

opaque
  unfolding ℂ

  snoc : ∀ {l1 q2 : ℕ} → (val (1 + q2 ≤ᵛ l1)) → val X → PList₂ (` (l1)) (` (q2)) (X) , (` (l1 ∸ ( 1 + q2 ))) ⊢ PList₂ (` (l1 ∸ ( 1 + q2 ))) (` (q2)) (X)
  snoc {X} {l1} {q2} cs x1 = payᴳ {p = l1 ∸ ( 1 + q2 )} {q' = 0} {!   !} $ powappᴳ {X = 1 + q2 ≤ᵛ l1} cs $
    foldr₂ᴳ
      (λ p5 → (1 + q2 ≤ᵛ p5) ⇀ (◁'[ p5 ∸ ( 1 + q2 ) ] (PList₂ (p5 ∸ ( 1 + q2 )) (q2) (X))))
      (λ p5 → powlamᴳ {X = 1 + q2 ≤ᵛ p5} $ λ _ → getᴳ {q' = p5 ∸ ( 1 + q2 )} (p5 ∸ ( 1 + q2 )) {!   !} $ cons₂ᴳ {q' = 0} {!   !} (x1) (nil₂ᴳ))
      (λ p5 → λ xh3 → powlamᴳ {X = 1 + q2 ≤ᵛ p5} $ λ cs' → getᴳ {q' = 2 · p5 ∸ ( 1 + q2 )} (p5 ∸ ( 1 + q2 )) {!   !} $
        chargeᴳ {q' = 2 · p5 ∸ ( 2 + q2 )} 1 {!   !} $ cons₂ᴳ {q' = p5 ∸ ( 1 )} {!   !} xh3 $
          subst2ᴳ (λ l q → PList₂ l q X) {!   !} {!   !} $
          payᴳ {p = q2 + p5 ∸ ( 1 + q2 )} {q' = 0} {!   !} $ powappᴳ  {X = 1 + q2 ≤ᵛ q2 + p5} {!   !} $
            (idᴳ {A = (1 + q2 ≤ᵛ q2 + p5) ⇀ (◁'[ q2 + p5 ∸ ( 1 + q2 ) ] (PList₂ (q2 + p5 ∸ ( 1 + q2 )) q2 X))} refl)
      )
      (idᴳ refl)
