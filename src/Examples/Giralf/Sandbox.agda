module Examples.Giralf.Sandbox where

open import Calf.Core.Cost
open import Calf.Value
open import Calf.Value.Nat
open import Calf.Value.Product
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


open import Cubical.Data.Bool hiding (_≤_)
import Cubical.Data.Nat.Properties as Nat
open import Cubical.Data.Nat.Order
open import Cubical.Relation.Nullary

_≤ᵇ_ : ℕ → ℕ → Bool
m ≤ᵇ n with ≤Dec m n
... | yes p = true
... | no ¬p = false

opaque
  unfolding ℂ

  snoc : ∀ {l1 q2 : ℕ} → (1 + q2 ≤ l1) → X → CList₂ (` (l1)) (` (q2)) (X) , (` (((l1 ∸ 1) ∸ q2) + 0)) ⊢ CList₂ (` ((l1 ∸ 1) ∸ q2)) (` (q2)) (X)
  snoc {X} {l1} {q2} cs x1 =
    payᴳ refl $
    powappᴳ {X = 1 + q2 ≤ l1} {!   !} $
    foldr₂ᴳ (λ p5 → (1 + q2 ≤ p5) ⇀ (◁[ (p5 ∸ 1) ∸ q2 ] (CList₂ ((p5 ∸ 1) ∸ q2) (q2) (X))))
      (λ p5 →
        powlamᴳ {X = 1 + q2 ≤ p5} $ λ cs4 →
        getᴳ ((p5 ∸ 1) ∸ q2) refl $
        cons₂ᴳ {q' = (((p5 ∸ 1) ∸ q2) + 0) ∸ ((p5 ∸ 1) ∸ q2)} {!   !} (x1) $ nil₂ᴳ {!   !})
      (λ p5 → λ xh3 →
        powlamᴳ {X = 1 + q2 ≤ p5} $ λ cs3 →
        getᴳ ((p5 ∸ 1) ∸ q2) refl $
        spendᴳ {q' = (((p5 ∸ 1) ∸ q2) + p5) ∸ 1} 1 {!   !} $
        cons₂ᴳ {q' = ((((p5 ∸ 1) ∸ q2) + p5) ∸ 1) ∸ ((p5 ∸ 1) ∸ q2)} {!   !} (xh3) $
        substᵐᴳ {!   !} $
        subst2ᴳ (λ l q → CList₂ l q X) {!  !} {!   !} $
        payᴳ refl $
        powappᴳ {X = (1 + q2 ≤ q2 + p5)} {!   !} $ idᴳ refl)
      (idᴳ refl)

  insert : ∀ {l1 q2 : ℕ} → (1 ≤ l1) × (1 + q2 ≤ l1) → ℕ → CList₂ (` (l1)) (` (q2)) ℕ , (` (((l1 ∸ 1) ∸ q2) + 0)) ⊢ CList₂ (` ((l1 ∸ 1) ∸ q2)) (` (q2)) (ℕ)
  insert {l1} {q2} cs x1 =
    payᴳ {p = (l1 ∸ 1) ∸ q2} {q' = 0} refl $ proj₁ᴳ {B = ◁[ 0 ] (CList₂ (l1 ∸ 1) (q2) (ℕ))} $
    powappᴳ {X = (1 ≤ l1) × (1 + q2 ≤ l1)} cs $
    foldr₂ᴳ (λ p5 → ((1 ≤ p5) × (1 + q2 ≤ p5)) ⇀ ((◁[ (p5 ∸ 1) ∸ q2 ] (CList₂ ((p5 ∸ 1) ∸ q2) (q2) (ℕ))) ×ᶜ (◁[ 0 ] (CList₂ (p5 ∸ 1) (q2) (ℕ)))))
      (λ p5 →
        powlamᴳ {X = (1 ≤ p5) × (1 + q2 ≤ p5)} $ λ cs6 →
        pairᴳ (
          getᴳ {q' = ((p5 ∸ 1) ∸ q2) + 0} ((p5 ∸ 1) ∸ q2) refl $
          cons₂ᴳ {q' = (((p5 ∸ 1) ∸ q2) + 0) ∸ ((p5 ∸ 1) ∸ q2)} {!   !} (x1) $ nil₂ᴳ {!   !}
        ) (
          getᴳ {q' = 0 + 0} (0) refl $ nil₂ᴳ refl
        )
      )
      (λ p5 → λ xh3 →
        powlamᴳ {X = (1 ≤ p5) × (1 + q2 ≤ p5)} $ λ cs5 →
        spendᴳ {q' = p5 ∸ 1} 1 {!   !} $
        pairᴳ (
          getᴳ {q' = ((p5 ∸ 1) ∸ q2) + (p5 ∸ 1)} ((p5 ∸ 1) ∸ q2) refl $
          if ((x1) ≤ᵇ (xh3)) then (
            cons₂ᴳ {q' = (((p5 ∸ 1) ∸ q2) + (p5 ∸ 1)) ∸ ((p5 ∸ 1) ∸ q2)} {!   !} (x1) $
            cons₂ᴳ {q' = ((((p5 ∸ 1) ∸ q2) + (p5 ∸ 1)) ∸ ((p5 ∸ 1) ∸ q2)) ∸ (((p5 ∸ 1) ∸ q2) + q2)} {!   !} (xh3) $
            substᵐᴳ {!   !} $ subst2ᴳ (λ p23 p22 → CList₂ (p23) (p22) (ℕ)) {!   !} {!   !} $
            payᴳ {p = 0} {q' = 0} refl $ proj₂ᴳ {A = ◁[ ((q2 + p5) ∸ 1) ∸ q2 ] (CList₂ (((q2 + p5) ∸ 1) ∸ q2) (q2) (ℕ))} $
            powappᴳ {X = (1 ≤ q2 + p5) × (1 + q2 ≤ q2 + p5)} {!   !} $ idᴳ refl
          ) else (
            cons₂ᴳ {q' = (((p5 ∸ 1) ∸ q2) + (p5 ∸ 1)) ∸ ((p5 ∸ 1) ∸ q2)} {!   !} (xh3) $
            substᵐᴳ {!   !} $ subst2ᴳ (λ p21 p20 → CList₂ (p21) (p20) (ℕ)) {!   !} {!   !} $
            payᴳ {p = ((q2 + p5) ∸ 1) ∸ q2} {q' = 0} refl $ proj₁ᴳ {B = ◁[ 0 ] (CList₂ ((q2 + p5) ∸ 1) (q2) (ℕ))} $
            powappᴳ {X = (1 ≤ q2 + p5) × (1 + q2 ≤ q2 + p5)} {!   !} $ idᴳ refl
          )
        ) (
          getᴳ {q' = 0 + (p5 ∸ 1)} (0) refl $
          cons₂ᴳ {q' = (0 + (p5 ∸ 1)) ∸ (p5 ∸ 1)} {!   !} (xh3) $
          substᵐᴳ {!   !} $ subst2ᴳ (λ p19 p18 → CList₂ (p19) (p18) (ℕ)) {!   !} {!   !} $
          payᴳ {p = 0} {q' = 0} refl $ proj₂ᴳ {A = ◁[ ((q2 + p5) ∸ 1) ∸ q2 ] (CList₂ (((q2 + p5) ∸ 1) ∸ q2) (q2) (ℕ))} $
          powappᴳ {X = (1 ≤ q2 + p5) × (1 + q2 ≤ q2 + p5)} {!   !} $ idᴳ refl
        )
      )
      (idᴳ refl)


  reverse : ∀ {l1 q2 : ℕ} → (1 ≤ q2) → CList₂ (` (l1)) (` (q2)) (X) , (` (0 + 0)) ⊢ CList₂ (` (l1)) (` (q2 ∸ 1)) (X)
  reverse {X} {l1} {q2} cs =
    payᴳ {p = 0} {q' = 0} refl $
    powappᴳ {X = 1 ≤ q2} {!   !} $
    foldr₂ᴳ (λ p17 → (1 ≤ q2) ⇀ (◁[ 0 ] (CList₂ (p17) (q2 ∸ 1) (X))))
      (λ p17 →
        powlamᴳ {X = 1 ≤ q2} $ λ cs10 →
        getᴳ {q' = 0 + 0} (0) refl $ nil₂ᴳ {!   !}
      )
      (λ p17 → λ yh4 →
        powlamᴳ {X = 1 ≤ q2} $ λ cs7 →
        getᴳ {q' = 0 + p17} (0) refl $
        substᵐᴳ {!   !} $ subst2ᴳ (λ p28 p27 → CList₂ (p28) (p27) (X)) {!   !} {!   !} $
        payᴳ {p = ((q2 + p17) ∸ 1) ∸ (q2 ∸ 1)} {q' = 0 + 0} refl $
        powappᴳ {X = 1 + (q2 ∸ 1) ≤ q2 + p17} {!   !} $
        foldr₂ᴳ (λ p20 → (1 + (q2 ∸ 1) ≤ p20) ⇀ (◁[ (p20 ∸ 1) ∸ (q2 ∸ 1) ] (CList₂ ((p20 ∸ 1) ∸ (q2 ∸ 1)) (q2 ∸ 1) (X))))
          (λ p20 →
            powlamᴳ {X = 1 + (q2 ∸ 1) ≤ p20} $ λ cs9 →
            getᴳ {q' = ((p20 ∸ 1) ∸ (q2 ∸ 1)) + 0} ((p20 ∸ 1) ∸ (q2 ∸ 1)) refl $
            cons₂ᴳ {q' = (((p20 ∸ 1) ∸ (q2 ∸ 1)) + 0) ∸ ((p20 ∸ 1) ∸ (q2 ∸ 1))} {!   !} (yh4) $ nil₂ᴳ {!   !}
          )
          (λ p20 → λ xh2 →
            powlamᴳ {X = 1 + (q2 ∸ 1) ≤ p20} $ λ cs8 →
            getᴳ {q' = ((p20 ∸ 1) ∸ (q2 ∸ 1)) + p20} ((p20 ∸ 1) ∸ (q2 ∸ 1)) refl $
            spendᴳ {q' = (((p20 ∸ 1) ∸ (q2 ∸ 1)) + p20) ∸ 1} 1 {!   !} $
            cons₂ᴳ {q' = ((((p20 ∸ 1) ∸ (q2 ∸ 1)) + p20) ∸ 1) ∸ ((p20 ∸ 1) ∸ (q2 ∸ 1))} {!   !} (xh2) $
            substᵐᴳ {!   !} $ subst2ᴳ (λ p30 p29 → CList₂ (p30) (p29) (X)) {!   !} {!   !} $
            payᴳ {p = (((q2 ∸ 1) + p20) ∸ 1) ∸ (q2 ∸ 1)} {q' = 0} refl $
            powappᴳ {X = 1 + (q2 ∸ 1) ≤ (q2 ∸ 1) + p20} {!   !} $ idᴳ refl
          )
          (
            payᴳ {p = 0} {q' = 0} refl $
            powappᴳ {X = 1 ≤ q2} {!   !} $ idᴳ refl)
      )
      (idᴳ refl)


  isort : ∀ {l1 q2 : ℕ} → (1 ≤ q2) → CList₂ (` (l1)) (` (q2)) (ℕ) , (` (0 + 0)) ⊢ CList₂ (` (l1)) (` (q2 ∸ 1)) (ℕ)
  isort {l1} {q2} cs =
    payᴳ {p = 0} {q' = 0} refl $
    powappᴳ {X = 1 ≤ q2} {!   !} $
    foldr₂ᴳ (λ p17 → (1 ≤ q2) ⇀ (◁[ 0 ] (CList₂ (p17) (q2 ∸ 1) (ℕ))))
      (λ p17 →
        powlamᴳ {X = 1 ≤ q2} $ λ cs12 →
        getᴳ {q' = 0 + 0} (0) refl $ nil₂ᴳ {!   !}
      )
      (λ p17 → λ yh4 →
        powlamᴳ {X = 1 ≤ q2} $ λ cs9 →
        getᴳ {q' = 0 + p17} (0) refl $
        substᵐᴳ {!   !} $ subst2ᴳ (λ p42 p41 → CList₂ (p42) (p41) (ℕ)) {!   !} {!   !} $
        payᴳ {p = ((q2 + p17) ∸ 1) ∸ (q2 ∸ 1)} {q' = 0 + 0} refl $ proj₁ᴳ {B = ◁[ 0 ] (CList₂ ((q2 + p17) ∸ 1) (q2 ∸ 1) (ℕ))} $
        powappᴳ {X = (1 ≤ q2 + p17) × (1 + (q2 ∸ 1) ≤ q2 + p17)} {!   !} $
        foldr₂ᴳ (λ p20 → ((1 ≤ p20) × (1 + (q2 ∸ 1) ≤ p20)) ⇀ ((◁[ (p20 ∸ 1) ∸ (q2 ∸ 1) ] (CList₂ ((p20 ∸ 1) ∸ (q2 ∸ 1)) (q2 ∸ 1) (ℕ))) ×ᶜ (◁[ 0 ] (CList₂ (p20 ∸ 1) (q2 ∸ 1) (ℕ)))))
          (λ p20 →
            powlamᴳ {X = (1 ≤ p20) × (1 + (q2 ∸ 1) ≤ p20)} $ λ cs11 →
            pairᴳ (
              getᴳ {q' = ((p20 ∸ 1) ∸ (q2 ∸ 1)) + 0} ((p20 ∸ 1) ∸ (q2 ∸ 1)) refl $
              cons₂ᴳ {q' = (((p20 ∸ 1) ∸ (q2 ∸ 1)) + 0) ∸ ((p20 ∸ 1) ∸ (q2 ∸ 1))} {!   !} (yh4) $ nil₂ᴳ {!   !}
            ) (
              getᴳ {q' = 0 + 0} (0) refl $ nil₂ᴳ {!   !}
            )
          )
          (λ p20 → λ xh2 →
            powlamᴳ {X = (1 ≤ p20) × (1 + (q2 ∸ 1) ≤ p20)} $ λ cs10 →
            spendᴳ {q' = p20 ∸ 1} 1 {!   !} $
            pairᴳ (
              getᴳ {q' = ((p20 ∸ 1) ∸ (q2 ∸ 1)) + (p20 ∸ 1)} ((p20 ∸ 1) ∸ (q2 ∸ 1)) refl $
              if ((yh4) ≤ᵇ (xh2)) then (
                cons₂ᴳ {q' = (((p20 ∸ 1) ∸ (q2 ∸ 1)) + (p20 ∸ 1)) ∸ ((p20 ∸ 1) ∸ (q2 ∸ 1))} {!   !} (yh4) $
                cons₂ᴳ {q' = ((((p20 ∸ 1) ∸ (q2 ∸ 1)) + (p20 ∸ 1)) ∸ ((p20 ∸ 1) ∸ (q2 ∸ 1))) ∸ (((p20 ∸ 1) ∸ (q2 ∸ 1)) + (q2 ∸ 1))} {!   !} (xh2) $
                substᵐᴳ {!   !} $ subst2ᴳ (λ p48 p47 → CList₂ (p48) (p47) (ℕ)) {!   !} {!   !} $
                payᴳ {p = 0} {q' = 0} refl $ proj₂ᴳ {A = ◁[ (((q2 ∸ 1) + p20) ∸ 1) ∸ (q2 ∸ 1) ] (CList₂ ((((q2 ∸ 1) + p20) ∸ 1) ∸ (q2 ∸ 1)) (q2 ∸ 1) (ℕ))} $
                powappᴳ {X = (1 ≤ (q2 ∸ 1) + p20) × (1 + (q2 ∸ 1) ≤ (q2 ∸ 1) + p20)} {!   !} $ idᴳ refl
              ) else (
                cons₂ᴳ {q' = (((p20 ∸ 1) ∸ (q2 ∸ 1)) + (p20 ∸ 1)) ∸ ((p20 ∸ 1) ∸ (q2 ∸ 1))} {!   !} (xh2) $
                substᵐᴳ {!   !} $ subst2ᴳ (λ p46 p45 → CList₂ (p46) (p45) (ℕ)) {!   !} {!   !} $
                payᴳ {p = (((q2 ∸ 1) + p20) ∸ 1) ∸ (q2 ∸ 1)} {q' = 0} refl $ proj₁ᴳ {B = ◁[ 0 ] (CList₂ (((q2 ∸ 1) + p20) ∸ 1) (q2 ∸ 1) (ℕ))} $
                powappᴳ {X = (1 ≤ (q2 ∸ 1) + p20) × (1 + (q2 ∸ 1) ≤ (q2 ∸ 1) + p20)} {!   !} $ idᴳ refl
              )
            ) (
              getᴳ {q' = 0 + (p20 ∸ 1)} (0) refl $
              cons₂ᴳ {q' = (0 + (p20 ∸ 1)) ∸ (p20 ∸ 1)} {!   !} (xh2) $
              substᵐᴳ {!   !} $ subst2ᴳ (λ p44 p43 → CList₂ (p44) (p43) (ℕ)) {!   !} {!   !} $
              payᴳ {p = 0} {q' = 0} refl $ proj₂ᴳ {A = ◁[ (((q2 ∸ 1) + p20) ∸ 1) ∸ (q2 ∸ 1) ] (CList₂ ((((q2 ∸ 1) + p20) ∸ 1) ∸ (q2 ∸ 1)) (q2 ∸ 1) (ℕ))} $
              powappᴳ {X = (1 ≤ (q2 ∸ 1) + p20) × (1 + (q2 ∸ 1) ≤ (q2 ∸ 1) + p20)} {!   !} $ idᴳ refl
            )
          )
          (
            payᴳ {p = 0} {q' = 0} refl $
            powappᴳ {X = 1 ≤ q2} {!   !} $ idᴳ refl)
      )
      (idᴳ refl)
