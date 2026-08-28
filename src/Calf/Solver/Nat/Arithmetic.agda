module Calf.Solver.Nat.Arithmetic where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_; _∸_; _·_)
import Cubical.Data.Nat.Properties as Nat
open import Cubical.Data.Nat.Order using
  (_≤_; isProp≤; zero-≤; ≤-refl; suc-≤-suc; ≤-trans; ≤-+-≤; ≤SumLeft; ≤SumRight;
   ≤-∸-+-cancel; ≤-∸-≤; ≤-∸-k)
open import Cubical.Data.Sigma using (fst; snd)

∸-witness : ∀ {m n : ℕ} → (h : m ≤ n) → n ∸ m ≡ fst h
∸-witness {m} {n} h =
  cong fst (isProp≤ ((n ∸ m) , ≤-∸-+-cancel h) h)

natRefl : (x : ℕ) → x ≡ x
natRefl x = refl

natCongSuc : (x y : ℕ) → x ≡ y → suc x ≡ suc y
natCongSuc x y p = cong suc p

natCong₂+ :
  (a a' b b' : ℕ)
  → a ≡ a'
  → b ≡ b'
  → a + b ≡ a' + b'
natCong₂+ a a' b b' p q = cong₂ _+_ p q

natCong₂· :
  (a a' b b' : ℕ)
  → a ≡ a'
  → b ≡ b'
  → a · b ≡ a' · b'
natCong₂· a a' b b' p q = cong₂ _·_ p q

natCong₂∸ :
  (a a' b b' : ℕ)
  → a ≡ a'
  → b ≡ b'
  → a ∸ b ≡ a' ∸ b'
natCong₂∸ a a' b b' p q = cong₂ _∸_ p q

natComp :
  (x y z : ℕ)
  → x ≡ y
  → y ≡ z
  → x ≡ z
natComp x y z p q = p ∙ q

finishNatExplicit :
  (lhs lhs' rhs rhs' : ℕ)
  → lhs ≡ lhs'
  → lhs' ≡ rhs'
  → rhs ≡ rhs'
  → lhs ≡ rhs
finishNatExplicit lhs lhs' rhs rhs' lhs-step middle rhs-step =
  lhs-step ∙ middle ∙ sym rhs-step

finishLeExplicit :
  (lower lower' upper upper' : ℕ)
  → lower ≡ lower'
  → lower' ≤ upper'
  → upper ≡ upper'
  → lower ≤ upper
finishLeExplicit lower lower' upper upper' lower-step middle upper-step =
  subst (λ n → lower ≤ n) (sym upper-step)
    (subst (λ n → n ≤ upper') (sym lower-step) middle)

leRefl : (m : ℕ) → m ≤ m
leRefl m = ≤-refl

leZero : (n : ℕ) → 0 ≤ n
leZero n = zero-≤

leSuc : (m n : ℕ) → m ≤ n → suc m ≤ suc n
leSuc m n p = suc-≤-suc p

leTrans : (k m n : ℕ) → k ≤ m → m ≤ n → k ≤ n
leTrans k m n p q = ≤-trans p q

lePlus :
  (m n l k : ℕ)
  → m ≤ n
  → l ≤ k
  → m + l ≤ n + k
lePlus m n l k p q = ≤-+-≤ p q

leSumLeft : (n k : ℕ) → n ≤ n + k
leSumLeft n k = ≤SumLeft

leSumRight : (n k : ℕ) → n ≤ k + n
leSumRight n k = ≤SumRight

leMulRight : (m n k : ℕ) → m ≤ n → m ≤ suc k · n
leMulRight m n k h = ≤-trans h (≤SumLeft {n} {k · n})

leWitnessEq : (lower upper : ℕ) → (p : lower ≤ upper) → upper ≡ fst p + lower
leWitnessEq lower upper p = sym (snd p)

leMinusPlusEq : (lower upper : ℕ) → (p : lower ≤ upper) → upper ≡ (upper ∸ lower) + lower
leMinusPlusEq lower upper p = sym (≤-∸-+-cancel p)

minusZeroRight : (x : ℕ) → x ∸ 0 ≡ x
minusZeroRight x = refl

minusZeroLeft : (x : ℕ) → 0 ∸ x ≡ 0
minusZeroLeft x = Nat.zero∸ x

minusSelf : (x : ℕ) → x ∸ x ≡ 0
minusSelf x = Nat.n∸n x

minusPullLeft :
  (m n k : ℕ)
  → m ≤ n
  → (k + n) ∸ m ≡ k + (n ∸ m)
minusPullLeft m n k p = sym (≤-∸-k p)

minusPullRight :
  (m n k : ℕ)
  → m ≤ n
  → (n + k) ∸ m ≡ (n ∸ m) + k
minusPullRight m n k p =
  cong (_∸ m) (Nat.+-comm n k)
  ∙ minusPullLeft m n k p
  ∙ Nat.+-comm k (n ∸ m)

minusPlusRight : (x k : ℕ) → (x + k) ∸ x ≡ k
minusPlusRight x k = Nat.∸+ k x

minusPlusLeft : (k x : ℕ) → (k + x) ∸ x ≡ k
minusPlusLeft k x = Nat.+∸ k x

leMinusRight : (a b c : ℕ) → a + c ≤ b → a ≤ b ∸ c
leMinusRight a b c p =
  subst (λ x → x ≤ b ∸ c) (Nat.+∸ a c) (≤-∸-≤ (a + c) b c p)

leMinusRightComm : (a b c : ℕ) → c + a ≤ b → a ≤ b ∸ c
leMinusRightComm a b c p =
  leMinusRight a b c (subst (_≤ b) (Nat.+-comm c a) p)

leWitnessLower : (a c b : ℕ) → a + c ≤ b → (p : c ≤ b) → a ≤ fst p
leWitnessLower a c b h p =
  subst (a ≤_) (∸-witness p) (leMinusRight a b c h)

leWitnessLowerComm : (a c b : ℕ) → c + a ≤ b → (p : c ≤ b) → a ≤ fst p
leWitnessLowerComm a c b h p =
  subst (a ≤_) (∸-witness p) (leMinusRightComm a b c h)
