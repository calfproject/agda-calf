module Calf.Solver.Nat.Regression where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; suc; _+_; _∸_; _·_)
open import Cubical.Data.Nat.Order using (_≤_)

open import Calf.Solver.Nat using (solveNat; solveNat0; debugSolveNat; debugSolveNat0)

-- Regression facts for the supported surface of Calf.Solver.Nat.

+-identityʳ : ∀ {n : ℕ} → n + 0 ≡ n
+-identityʳ = solveNat0

+-identityˡ : ∀ {n : ℕ} → 0 + n ≡ n
+-identityˡ = solveNat0

+-comm : ∀ {m n : ℕ} → m + n ≡ n + m
+-comm = solveNat0

+-assoc : ∀ {l m n : ℕ} → (l + m) + n ≡ l + (m + n)
+-assoc = solveNat0

·-identityʳ : ∀ {n : ℕ} → n · 1 ≡ n
·-identityʳ = solveNat0

·-identityˡ : ∀ {n : ℕ} → 1 · n ≡ n
·-identityˡ = solveNat0

·-zeroʳ : ∀ {n : ℕ} → n · 0 ≡ 0
·-zeroʳ = solveNat0

·-zeroˡ : ∀ {n : ℕ} → 0 · n ≡ 0
·-zeroˡ = solveNat0

·-comm : ∀ {m n : ℕ} → m · n ≡ n · m
·-comm = solveNat0

·-assoc : ∀ {l m n : ℕ} → (l · m) · n ≡ l · (m · n)
·-assoc = solveNat0

·-distribˡ-+ : ∀ {l m n : ℕ} → l · (m + n) ≡ l · m + l · n
·-distribˡ-+ = solveNat0

·-distribʳ-+ : ∀ {l m n : ℕ} → (l + m) · n ≡ l · n + m · n
·-distribʳ-+ = solveNat0

suc-+-commute : ∀ {m n : ℕ} → suc (m + n) ≡ m + suc n
suc-+-commute = solveNat0

literal-expand₃ : ∀ {n : ℕ} → 3 · n ≡ n + (n + (n + 0))
literal-expand₃ = solveNat0

polynomial-square :
  ∀ {m n : ℕ}
  → (m + n) · (m + n) ≡ m · m + 2 · m · n + n · n
polynomial-square = solveNat0

polynomial-crazy :
  ∀ {a b c d e : ℕ}
  → ((2 · (a + b) + 3 · (c + d) + suc e)
      · (suc (a + c) + 4 · (b + d))
      + (a + b + c + d + e) · (a + c + e)
      + 7 · (b + d))
    ≡
    ((1 + e + 3 · d + 3 · c + 2 · b + 2 · a)
      · (4 · d + 4 · b + 1 + c + a)
      + 7 · d + 7 · b
      + (e + d + c + b + a) · (e + c + a))
polynomial-crazy = solveNat0

∸-zeroʳ : ∀ {n : ℕ} → n ∸ 0 ≡ n
∸-zeroʳ = solveNat0

∸-self : ∀ {n : ℕ} → n ∸ n ≡ 0
∸-self = solveNat0

∸-cancelʳ : ∀ {m n : ℕ} → m ≤ n → n ∸ m + m ≡ n
∸-cancelʳ h = solveNat h

∸-cancelˡ : ∀ {m n : ℕ} → m ≤ n → m + (n ∸ m) ≡ n
∸-cancelˡ h = solveNat h

∸-+-pullʳ :
  ∀ {k m n : ℕ}
  → m ≤ n
  → (n + k) ∸ m ≡ (n ∸ m) + k
∸-+-pullʳ h = solveNat h

∸-+-pullˡ :
  ∀ {k m n : ℕ}
  → m ≤ n
  → (k + n) ∸ m ≡ k + (n ∸ m)
∸-+-pullˡ h = solveNat h

guarded-sub-shift :
  ∀ {q p : ℕ}
  → 1 + q ≤ p
  → q + p ∸ (1 + q) ≡ q + (p ∸ (1 + q))
guarded-sub-shift h = solveNat h

guarded-sub-step :
  ∀ {q p : ℕ}
  → 1 + q ≤ p
  → 1 + (2 · p ∸ (2 + q)) ≡ 2 · p ∸ (1 + q)
guarded-sub-step h = solveNat h

guarded-sub-split :
  ∀ {q p : ℕ}
  → 1 + q ≤ p
  → (p ∸ (1 + q)) + (p ∸ 1) ≡ 2 · p ∸ (2 + q)
guarded-sub-split h = solveNat h

guarded-sub-crazy :
  ∀ {a b c d e f x y : ℕ}
  → a ≤ b
  → c ≤ d
  → e ≤ f
  → suc
      (5 · ((b + d + f) ∸ (a + c + e))
       + 3 · ((b ∸ a) + (d ∸ c))
       + ((f ∸ e) + x) · (y + 2)
       + (a + c + e)
       + 7 · x)
    ≡
      (5 · ((b ∸ a) + ((d ∸ c) + (f ∸ e)))
       + 3 · ((d + b) ∸ (c + a))
       + ((f + x) ∸ e) · (2 + y)
       + e + c + a
       + x + 6 · x) + 1
guarded-sub-crazy h₁ h₂ h₃ = solveNat (h₁ , h₂ , h₃)

≤-refl-regression : ∀ {n : ℕ} → n ≤ n
≤-refl-regression = solveNat0

≤-zeroˡ : ∀ {n : ℕ} → 0 ≤ n
≤-zeroˡ = solveNat0

≤-sum-left : ∀ {m n : ℕ} → m ≤ m + n
≤-sum-left = solveNat0

≤-sum-right : ∀ {m n : ℕ} → n ≤ m + n
≤-sum-right = solveNat0

≤-literal-mul₂ : ∀ {n : ℕ} → n ≤ 2 · n
≤-literal-mul₂ = solveNat0

≤-literal-mul₃ : ∀ {n : ℕ} → n ≤ 3 · n
≤-literal-mul₃ = solveNat0

≤-literal-mul₂-suc : ∀ {n : ℕ} → suc n ≤ 2 · suc n
≤-literal-mul₂-suc = solveNat0

≤-assumption : ∀ {m n : ℕ} → m ≤ n → m ≤ n
≤-assumption h = solveNat h

≤-assumption-direct : ∀ {m n : ℕ} → m ≤ n → m ≤ n
≤-assumption-direct h = solveNat h

≤-suc-assumption : ∀ {m n : ℕ} → m ≤ n → suc m ≤ suc n
≤-suc-assumption h = solveNat h

≤-+-right : ∀ {k m n : ℕ} → m ≤ n → m + k ≤ n + k
≤-+-right h = solveNat h

≤-+-left : ∀ {k m n : ℕ} → m ≤ n → k + m ≤ k + n
≤-+-left h = solveNat h

≤-trans-sum-left : ∀ {k m n : ℕ} → m ≤ n → m ≤ n + k
≤-trans-sum-left h = solveNat h

≤-trans-sum-right : ∀ {k m n : ℕ} → m ≤ n → m ≤ k + n
≤-trans-sum-right h = solveNat h

≤-+-with-extra :
  ∀ {k l m n : ℕ}
  → m ≤ n
  → m + k ≤ n + (k + l)
≤-+-with-extra h = solveNat h

≤-crazy :
  ∀ {a b c d e f g x y z : ℕ}
  → a ≤ b
  → b ≤ c
  → d ≤ e
  → f ≤ g
  → suc (suc ((a + (d + f)) + ((x + y) + z)))
    ≤ suc (suc ((c + (e + g)) + (3 · (x + y) + z)))
≤-crazy h₁ h₂ h₃ h₄ = solveNat (h₁ , h₂ , h₃ , h₄)

≤-subtraction-crazy :
  ∀ {a b c d e f g h x y z : ℕ}
  → a ≤ b
  → h ≤ g
  → c ≤ d
  → e ≤ f
  → x ≤ y
  → suc
      (suc
        (((b ∸ a) + (c + e))
         + ((g ∸ h) + x)))
    ≤ suc
      (suc
        (((b ∸ a) + (d + f))
         + ((g ∸ h) + (y + z))))
≤-subtraction-crazy h₁ h₂ h₃ h₄ h₅ =
  solveNat (h₁ , h₂ , h₃ , h₄ , h₅)

≤-subtraction-nontrivial :
  ∀ {a b c d x : ℕ}
  → a ≤ b
  → c ≤ d
  → (b + d) ∸ (a + c) ≤ (b ∸ a) + (d ∸ c) + x
≤-subtraction-nontrivial h₁ h₂ = solveNat (h₁ , h₂)

≤-suc-with-extra :
  ∀ {k m n : ℕ}
  → m ≤ n
  → suc m ≤ suc (n + k)
≤-suc-with-extra h = solveNat h

≤-guarded-sum :
  ∀ {q p : ℕ}
  → 1 + q ≤ p
  → 1 + q ≤ q + p
≤-guarded-sum h = solveNat h

≤-sub-one-from-suc-guard :
  ∀ {q p : ℕ}
  → 1 + q ≤ p
  → q ≤ p ∸ 1
≤-sub-one-from-suc-guard h = solveNat h

≤-one-sum-from-guard :
  ∀ {q p : ℕ}
  → 1 + q ≤ p
  → 1 ≤ q + p
≤-one-sum-from-guard h = solveNat h

∸-nested-plus-zero-self :
  ∀ {q p : ℕ}
  → 1 + q ≤ p
  → 0 ≡ (((p ∸ 1) ∸ q) + 0) ∸ ((p ∸ 1) ∸ q)
∸-nested-plus-zero-self h = solveNat h

≤-trans-two-assumptions :
  ∀ {l m n : ℕ}
  → l ≤ m
  → m ≤ n
  → l ≤ n
≤-trans-two-assumptions h₁ h₂ = solveNat (h₁ , h₂)

≤-+-two-assumptions :
  ∀ {l m n k : ℕ}
  → l ≤ m
  → n ≤ k
  → l + n ≤ m + k
≤-+-two-assumptions h₁ h₂ = solveNat (h₁ , h₂)

≤-trans-three-assumptions :
  ∀ {k l m n : ℕ}
  → k ≤ l
  → l ≤ m
  → m ≤ n
  → k ≤ n
≤-trans-three-assumptions h₁ h₂ h₃ = solveNat (h₁ , h₂ , h₃)

≤-trans-four-assumptions :
  ∀ {j k l m n : ℕ}
  → j ≤ k
  → k ≤ l
  → l ≤ m
  → m ≤ n
  → j ≤ n
≤-trans-four-assumptions h₁ h₂ h₃ h₄ = solveNat (h₁ , h₂ , h₃ , h₄)

≤-+-trans-two-assumptions :
  ∀ {k l m n p : ℕ}
  → k ≤ l
  → m ≤ n
  → k + m ≤ l + (n + p)
≤-+-trans-two-assumptions h₁ h₂ = solveNat (h₁ , h₂)

∸-two-guards-cancel :
  ∀ {k l m n : ℕ}
  → k ≤ l
  → m ≤ n
  → (l ∸ k) + (n ∸ m) + k + m ≡ l + n
∸-two-guards-cancel h₁ h₂ = solveNat (h₁ , h₂)

∸-sum-two-guards :
  ∀ {k l m n : ℕ}
  → k ≤ l
  → m ≤ n
  → (l + n) ∸ (k + m) ≡ (l ∸ k) + (n ∸ m)
∸-sum-two-guards h₁ h₂ = solveNat (h₁ , h₂)

twoFacts :
  ∀ {a b c : ℕ}
  → a ≤ b
  → b ≤ c
  → a ≤ c
twoFacts h₁ h₂ = solveNat (h₁ , h₂)

≤-additive-diff-suc :
  ∀ {x p : ℕ}
  → suc x ≤ x + 1 + p
≤-additive-diff-suc = solveNat0

≤-minus-l-diff :
  ∀ {l q p : ℕ}
  → l ≤ q
  → l + (q ∸ l) ≤ q + p
≤-minus-l-diff h = solveNat h

≤-minus-l-diff' :
  ∀ {l q p : ℕ}
  → l ≤ q
  → (q ∸ l) + l ≤ q + p
≤-minus-l-diff' h = solveNat h
