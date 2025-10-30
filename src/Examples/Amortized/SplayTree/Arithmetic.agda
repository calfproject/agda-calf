{-# OPTIONS --rewriting #-}

module Examples.Amortized.SplayTree.Arithmetic where
    
open import Algebra.Cost

costMonoid = ℕ-CostMonoid
open CostMonoid costMonoid renaming (_+_ to _⊕_)

open import Calf costMonoid 
open import Calf.Data.Nat 

open import Data.Nat as Nat using (ℕ; _<_; _≤?_; _<?_; zero)
open import Data.Nat.Properties as Nat using (module ≤-Reasoning; _≟_)

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; module ≡-Reasoning)

open import Data.Nat.Tactic.RingSolver

arithmetic₁ : (a b c d : val nat) → a + b + c + d ≡ (a + d) + b + c
arithmetic₁ = solve-∀

arithmetic₂ : (a b c d : val nat) → a + b + c + d ≡ a + b + (c + d)
arithmetic₂ = solve-∀

arithmetic₃ : (a b c d : val nat) → a + b + (c + d) ≡ c + (a + b + d)
arithmetic₃ = solve-∀

arithmetic₄ : (a b c d : val nat) → (a + b) + (c + d) ≡ (a + c) + (b + d)
arithmetic₄ = solve-∀ 

arithmetic₅ : (a b c d e f g : val nat) → (a + b + c + d) + ((e + f) + g) ≡ a + g + ((b + f + c) + e + d)
arithmetic₅ = solve-∀

arithmetic₆ : (a b c d e f : val nat) → a + b + c + (d + e + f) ≡ (a + b + d + f) + (c + e)
arithmetic₆ = solve-∀

arithmetic₇ : (a b c d e f g : val nat) → (a + b + c + d) + ((e + f) + g) ≡ (a + g) + (b + e + (c + f + d))
arithmetic₇ = solve-∀

arithmetic₈ : (a b c d e : val nat) → (a + b + c) + (d + e) ≡ a + b + (c + d + e)
arithmetic₈ = solve-∀

arithmetic₉ : (a b c d e : val nat) → (a + b) + (c + d + e) ≡ a + b + (c + d + e)
arithmetic₉ = solve-∀

arithmetic₁₀ : (a b c d e : val nat) → a + b + (c + d + e) ≡ (a + b + c) + d + e 
arithmetic₁₀ = solve-∀

arithmetic₁₁ : (a b c d e f : val nat) → a + (b + c + d + e + f) ≡ (a + b + d + f) + (c + e)
arithmetic₁₁ = solve-∀

arithmetic₁₂ : (a b c d e : val nat) → (a + b) + ((c + d) + e) ≡ ((a + b) + c) + d + e 
arithmetic₁₂ = solve-∀

arithmetic-manual : (a b : val nat) → b Nat.≤ a → a + a ≡ (a + b) + (a ∸ b)
arithmetic-manual a b p = 
  let open ≡-Reasoning in 
  begin
      a + a
  ≡⟨ Nat.m+n∸n≡m (a + a) b ⟨
    ((a + a) + b) ∸ b
  ≡⟨ Eq.cong (λ e → e ∸ b) (+-assoc a a b) ⟩
    (a + (a + b)) ∸ b
  ≡⟨ Eq.cong (λ e → (a + e) ∸ b) (Nat.+-comm a b) ⟩
    (a + (b + a)) ∸ b
  ≡⟨ Eq.cong (λ e → e ∸ b) (+-assoc a b a) ⟨
    ((a + b) + a) ∸ b
  ≡⟨ Nat.+-∸-assoc (a + b) p ⟩
    (a + b) + (a ∸ b)
  ∎

arithmetic-manual₁ : (a b : val nat) → b Nat.≤ a → (a + a) + (a ∸ b) ∸ (a ∸ b) ≡ (a + b) + (a ∸ b)
arithmetic-manual₁ a b p = 
  let open ≡-Reasoning in 
  begin
    (a + a) + (a ∸ b) ∸ (a ∸ b)
  ≡⟨ Nat.m+n∸n≡m (a + a) (a ∸ b) ⟩
    a + a
  ≡⟨ Nat.m+n∸n≡m (a + a) b ⟨
    ((a + a) + b) ∸ b
  ≡⟨ Eq.cong (λ e → e ∸ b) (+-assoc a a b) ⟩
    (a + (a + b)) ∸ b
  ≡⟨ Eq.cong (λ e → (a + e) ∸ b) (Nat.+-comm a b) ⟩
    (a + (b + a)) ∸ b
  ≡⟨ Eq.cong (λ e → e ∸ b) (+-assoc a b a) ⟨
    ((a + b) + a) ∸ b
  ≡⟨ Nat.+-∸-assoc (a + b) p ⟩
    (a + b) + (a ∸ b)
  ∎

