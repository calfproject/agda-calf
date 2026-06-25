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
open import Calf.Solver.Nat using (solveNat; solveNat0)

opaque
  unfolding ℂ
  unfolding _+ℂ_
  
  arithmetic1 : ∀ {n : ℕ} → n + 0 ≡ n
  arithmetic1 = solveNat0
  
  arithmetic2 : ∀ {q2 p5 : ℕ}
    → 1 + q2 ≤ p5
    → p5 ∸ suc q2 + p5 ≡ p5 + (p5 + 0) ∸ suc q2
  arithmetic2 h = solveNat h
  
  arithmetic3 : ∀ {q2 p5 : ℕ}
    → 1 + q2 ≤ p5
    → 1 + (2 · p5 ∸ (2 + q2)) ≡ 2 · p5 ∸ (1 + q2)
  arithmetic3 h = solveNat h
  
  arithmetic4 : ∀ {q2 p5 : ℕ}
    → 1 + q2 ≤ p5
    → (p5 ∸ (1 + q2)) + (p5 ∸ 1) ≡ 2 · p5 ∸ (2 + q2)
  arithmetic4 h = solveNat h

  arithmetic5 : ∀ {q2 p5 : ℕ}
    → 1 + q2 ≤ p5
    → q2 + p5 ∸ (1 + q2) ≡ q2 + (p5 ∸ (1 + q2))
  arithmetic5 h = solveNat h
  
  arithmetic6 : ∀ {q2 : ℕ} → q2 ≡ q2
  arithmetic6 = solveNat0
  
  arithmetic7 : ∀ {q2 p5 : ℕ}
    → 1 + q2 ≤ p5
    → (q2 + p5 ∸ (1 + q2)) + 0 ≡ p5 ∸ 1
  arithmetic7 h = solveNat h
  
  arithmetic8 : ∀ {q2 p5 : ℕ}
    → 1 + q2 ≤ p5
    → 1 + q2 ≤ q2 + p5
  arithmetic8 h = solveNat h

  snoc : ∀ {l1 q2 : ℕ} → (val (1 + q2 ≤ᵛ l1)) → val X → PList₂ (` (l1)) (` (q2)) (X) , (` (l1 ∸ ( 1 + q2 ))) ⊢ PList₂ (` (l1 ∸ ( 1 + q2 ))) (` (q2)) (X)
  snoc {X} {l1} {q2} cs x1 = payᴳ {p = l1 ∸ ( 1 + q2 )} {q' = 0} arithmetic1 $ powappᴳ {X = 1 + q2 ≤ᵛ l1} cs $
    foldr₂ᴳ
      (λ p5 → (1 + q2 ≤ᵛ p5) ⇀ (◁'[ p5 ∸ ( 1 + q2 ) ] (PList₂ (p5 ∸ ( 1 + q2 )) (q2) (X))))
      (λ p5 → powlamᴳ {X = 1 + q2 ≤ᵛ p5} $ λ _ → getᴳ {q' = p5 ∸ ( 1 + q2 )} (p5 ∸ ( 1 + q2 )) arithmetic1 $ cons₂ᴳ {q' = 0} arithmetic1 (x1) (nil₂ᴳ))
      (λ p5 → λ xh3 → powlamᴳ {X = 1 + q2 ≤ᵛ p5} $ λ cs' → getᴳ {q' = 2 · p5 ∸ ( 1 + q2 )} (p5 ∸ ( 1 + q2 )) (arithmetic2 cs') $
        chargeᴳ {q' = 2 · p5 ∸ ( 2 + q2 )} 1 (arithmetic3 cs') $ cons₂ᴳ {q' = p5 ∸ (suc zero)} (arithmetic4 cs') xh3 $
          subst2ᴳ (λ l q → PList₂ l q X) (arithmetic5 cs') arithmetic6 $
          payᴳ {p = q2 + p5 ∸ ( 1 + q2 )} {q' = 0} (arithmetic7 cs') $ powappᴳ  {X = 1 + q2 ≤ᵛ q2 + p5} (arithmetic8 cs') $
            (idᴳ {A = (1 + q2 ≤ᵛ q2 + p5) ⇀ (◁'[ q2 + p5 ∸ ( 1 + q2 ) ] (PList₂ (q2 + p5 ∸ ( 1 + q2 )) q2 X))} refl)
      )
      (idᴳ refl)
