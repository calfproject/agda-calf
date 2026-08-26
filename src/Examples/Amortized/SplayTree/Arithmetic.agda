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

arithmetic₁₃ : (a b c d e f g : val nat) → a + e + (b + f + (c + g + d)) ≡ (a + b + c + d) + e + f + g
arithmetic₁₃ = solve-∀

arithmetic₁₄ : (a b c d e f g h : val nat) → (a + b + c + d) + e + f + g + h ≡ h + (a + g + b + f + c + e + d)
arithmetic₁₄ = solve-∀

arithmetic₁₅ : (a b c d e : val nat) → (e + e) + (a + b + c + d + e) ≡ a + e + (b + e + (c + e + d))
arithmetic₁₅ = solve-∀

arithmetic₁₆ : (a b c d e f g h : val nat) → a + e + (b + f + (c + g + d)) + h ≡ (a + b + c + d) + e + f + (g + h)
arithmetic₁₆ = solve-∀

arithmetic₁₇ : (a b c d e f g : val nat) → (a + b + c + d) + e + f + g ≡ a + e + b + f + c + g + d
arithmetic₁₇ = solve-∀

arithmetic₁₈ : (a b c d e : val nat) → (a + e + b) + (c + e + d + e) ≡ a + e + (b + e + (c + e + d))
arithmetic₁₈ = solve-∀

arithmetic₁₉ : (a b c d e f g : val nat) → a + b + c + d + (e + f + g) ≡ a + b + (c + d + e) + f + g
arithmetic₁₉ = solve-∀

arithmetic₂₀ : (a b c d e f g : val nat) → (a + b + c) + d + (e + f + g) ≡ (a + b + (c + d + e)) + f + g
arithmetic₂₀ = solve-∀

arithmetic₂₁ : (a b c d e f g : val nat) → (a + b + c) + d + (e + f + g) ≡ (a + c + e + g) + b + d + f
arithmetic₂₁ = solve-∀

arithmetic₂₂ : (a b c d e f g h : val nat) → (a + c + e + g) + f + b + d + h ≡ h + (a + b + (c + d + e) + f + g)
arithmetic₂₂ = solve-∀

arithmetic₂₃ : (a b c d e : val nat) → (e + e) + (a + b + c + d + e) ≡ (a + e + (b + e + c)) + e + d
arithmetic₂₃ = solve-∀

arithmetic₂₄ : (a b c d e : val nat) → (d + b + e) + (a + b + c + b) ≡ (a + b + (c + b + d)) + b + e
arithmetic₂₄ = solve-∀

arithmetic₂₅ : (a b c d : val nat) → (a + d + b) + (c + d) ≡ (a + d + (b + d + c))
arithmetic₂₅ = solve-∀

arithmetic₂₆ : (a b c d e f g : val nat) → a + b + c + d + (e + f + g) ≡ a + b + (c + d + e) + f + g
arithmetic₂₆ = solve-∀

arithmetic₂₇ : (a b c d : val nat) → a + b + c + d ≡ (a + c) + (d + b)
arithmetic₂₇ = solve-∀

arithmetic₂₈ : (a b c d e f g h : val nat) → ((a + b + c) + d + (e + f + g)) + h ≡ (a + c + e + g) + (b + h) + d + f
arithmetic₂₈ = solve-∀

arithmetic₂₉ : (a b c d e f g : val nat) → a + b + (c + d + e) + f + g ≡ (a + c + e + g) + b + f + d
arithmetic₂₉ = solve-∀

arithmetic₃₀ : (a b c d e f g : val nat) → (a + b + c) + d + (e + f + g) ≡ (a + b + (c + d + e)) + f + g
arithmetic₃₀ = solve-∀

arithmetic₃₁ : (a b c d e f g h : val nat) → ((a + b + c) + d + (e + f + g) + h) ≡ (a + c + e + g) + b + d + (f + h)
arithmetic₃₁ = solve-∀

arithmetic₃₂ : (a b c d e f g : val nat) → (a + c + e + g) + b + f + d ≡ a + b + (c + d + e) + f + g
arithmetic₃₂ = solve-∀

arithmetic₃₃ : (a b c d e f g : val nat) → (a + b + c) + d + (e + f + g) ≡ (a + b + (c + d + e)) + f + g
arithmetic₃₃ = solve-∀

arithmetic₃₄ : (a b c d e f g : val nat) → (a + b + c) + (d + e + f + g) ≡ (a + b + c) + d + (e + f + g)
arithmetic₃₄ = solve-∀

arithmetic₃₅ : (a b c d e f g : val nat) → (c + d + e) + (b + a + f + g) ≡ (a + b + c) + d + (e + f + g)
arithmetic₃₅ = solve-∀

arithmetic₃₆ : (a b c d e : val nat) → a + e + b + e + (c + e + d) ≡ a + e + (b + e + c + e + d)
arithmetic₃₆ = solve-∀

arithmetic₃₇ : (a b c d e f g : val nat) → (a + b + c) + d + (e + f + g) ≡ (a + c + e + g) + f + d + b
arithmetic₃₇ = solve-∀ 

arithmetic₃₈ : (a b c d e f g h : val nat) → (a + b + c + d) + e + f + g + h ≡ h + (a + e + (b + g + c + f + d))
arithmetic₃₈ = solve-∀

arithmetic₃₉ : (a b c d e : val nat) → (a + e + b) + e + (c + e + d) ≡ a + e + ((b + e + c) + e + d)
arithmetic₃₉ = solve-∀

arithmetic₄₀ : (a b c d e : val nat) → ((a + e + b) + (c + e + d + e)) ≡ a + e + ((b + e + c) + e + d)
arithmetic₄₀ = solve-∀

arithmetic₄₁ : (b c d e : val nat) → (c + e + d) + (b + e) ≡ ((b + e + c) + e + d)
arithmetic₄₁ = solve-∀

arithmetic₄₂ : (a b c d e : val nat) → (e + e) + (a + b + c + d + e) ≡ a + e + ((b + e + c) + e + d)
arithmetic₄₂ = solve-∀

arithmetic₄₃ : (a b c d e f g h : val nat) → ((a + b + c) + d + (e + f + g)) + h ≡ (a + c + e + g) + (f + h) + d + b
arithmetic₄₃ = solve-∀

arithmetic₄₄ : (a b c d e f g : val nat) → (a + b + c + d) + e + f + g ≡ (a + f + (b + g + c + e + d))
arithmetic₄₄ = solve-∀

arithmetic₄₅ : (a b c d e : val nat) → ((a + e + b) + e + (c + e + d)) ≡ a + e + ((b + e + c) + e + d)
arithmetic₄₅ = solve-∀

arithmetic₄₆ : (a b c d e f g h : val nat) → ((a + g + b) + f + (c + e + d)) + h ≡ (a + b + c + d) + e + f + (g + h)
arithmetic₄₆ = solve-∀

arithmetic₄₈ : (a b c d e : val nat) → (b + e + c) + (a + e + d + e) ≡ ((a + e + b) + e + (c + e + d))
arithmetic₄₈ = solve-∀

arithmetic₄₉ : (a b c d e : val nat) → (((a + e + b) + e + c) + e + d) ≡ a + e + (b + e + (c + e + d))
arithmetic₄₉ = solve-∀

arithmetic₅₀ : (a b c d e f g : val nat) → (((a + e + b) + f + c) + g + d) ≡ (a + b + c + d) + e + f + g
arithmetic₅₀ = solve-∀

arithmetic₅₁ : (a b c d e f g h : val nat) → (a + b + c + d) + e + f + g + h ≡ h + (a + e + (b + f + (c + g + d)))
arithmetic₅₁ = solve-∀

arithmetic₅₂ : (a b c d e : val nat) → (e + e) + (a + b + c + d + e) ≡ (((a + e + b) + e + c) + e + d)
arithmetic₅₂ = solve-∀

arithmetic₅₃ : (a b c : val nat) → a + a + b + c ≡ (a + b) + (c + a)
arithmetic₅₃ = solve-∀

arithmetic₅₄ : (a b c d e f g h : val nat) → (((a + e + b) + f + c) + g + d) + h ≡ (a + b + c + d) + g + f + (e + h)
arithmetic₅₄ = solve-∀

arithmetic₅₅ : (a b c d e f g : val nat) → (a + b + c + d) + e + f + g ≡ a + g + (b + f + (c + e + d))
arithmetic₅₅ = solve-∀

arithmetic₅₆ : (a b c d e : val nat) → ((a + e + b) + e + (c + e + d)) ≡ (a + e + (b + e + (c + e + d)))
arithmetic₅₆ = solve-∀

arithmetic₅₇ : (a b c d e : val nat) → ((a + e + b) + (e + c + e + d)) ≡ ((a + e + b) + e + (c + e + d))
arithmetic₅₇ = solve-∀

arithmetic₅₈ : (a b c d e : val nat) → (a + e + b + e) + (c + e + d) ≡ (((a + e + b) + e + c) + e + d)
arithmetic₅₈ = solve-∀

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

arithmetic-manual₂ : (a b c d : val nat) → a Nat.≤ c → a + a + b + ((c ∸ a) + d) ≡ (a ∸ a) + a + (b + c) + d
arithmetic-manual₂ a b c d a≤c =
  let open ≡-Reasoning in
  begin
    a + a + b + ((c ∸ a) + d)
  ≡⟨ Eq.cong (λ e → a + a + b + e) (Nat.+-∸-comm d a≤c) ⟨ 
    (((a + a) + b) + ((c + d) ∸ a))
  ≡⟨ Nat.+-assoc (a + a) b ((c + d) ∸ a) ⟩
    a + a + (b + ((c + d) ∸ a))
  ≡⟨ Eq.cong (λ e → a + a + e) (Nat.+-∸-assoc b (Nat.≤-trans a≤c (Nat.m≤m+n c d))) ⟨
    a + a + ((b + (c + d)) ∸ a)
  ≡⟨ Eq.cong (λ e → a + a + (e ∸ a)) (Nat.+-assoc b c d) ⟨ 
    a + a + (((b + c) + d) ∸ a)
  ≡⟨ Nat.+-assoc a a (((b + c) + d) ∸ a) ⟩
    a + (a + (((b + c) + d) ∸ a))
  ≡⟨ Eq.cong (λ e → a + e) (Nat.+-∸-assoc a 
      (Nat.≤-trans a≤c (Nat.≤-trans (Nat.m≤n+m c b) (Nat.m≤m+n (b + c) d)))) ⟨ 
    a + ((a + ((b + c) + d)) ∸ a)
  ≡⟨ Eq.cong (λ e → a + (e ∸ a)) (Nat.+-comm a ((b + c) + d)) ⟩
    a + ((((b + c) + d) + a) ∸ a)
  ≡⟨ Eq.cong (λ e → a + e) (Nat.+-∸-assoc ((b + c) + d) {a} {a} Nat.≤-refl) ⟩
    a + (((b + c) + d) + (a ∸ a))
  ≡⟨ Eq.cong (λ e → a + e) (Nat.+-comm ((b + c) + d) (a ∸ a)) ⟩
    a + ((a ∸ a) + ((b + c) + d))
  ≡⟨ Nat.+-assoc a (a ∸ a) ((b + c) + d) ⟨
    a + (a ∸ a) + ((b + c) + d)
  ≡⟨ Eq.cong (λ e → e + ((b + c) + d)) (Nat.+-comm a (a ∸ a)) ⟩
    (a ∸ a) + a + ((b + c) + d)
  ≡⟨ Nat.+-assoc ((a ∸ a) + a) (b + c) d ⟨
    (a ∸ a) + a + (b + c) + d
  ∎

arithmetic-manual₃ : (a b c : val nat) → b Nat.≤ a → c Nat.≤ b → (3 * (a ∸ b)) + (3 * (b ∸ c)) ≡ (3 * (a ∸ c))
arithmetic-manual₃ a b c b≤a c≤b = 
  let open ≡-Reasoning in
  begin
    (3 * (a ∸ b)) + (3 * (b ∸ c))
  ≡⟨ Nat.*-distribˡ-+ 3 (a ∸ b) (b ∸ c) ⟨
    3 * ((a ∸ b) + (b ∸ c))
  ≡⟨ Eq.cong (λ e → 3 * e) (Nat.+-∸-assoc (a ∸ b) c≤b) ⟨  
    3 * (((a ∸ b) + b) ∸ c) 
  ≡⟨ Eq.cong (λ e → 3 * (e ∸ c)) (Nat.+-∸-comm b b≤a) ⟨
    3 * (((a + b) ∸ b) ∸ c)
  ≡⟨ Eq.cong (λ e → 3 * (e ∸ c)) (Nat.+-∸-assoc a {b} {b} Nat.≤-refl) ⟩ 
    3 * ((a + (b ∸ b)) ∸ c)
  ≡⟨ Eq.cong (λ e → 3 * ((a + e) ∸ c)) (Nat.n∸n≡0 b) ⟩
    3 * ((a + 0) ∸ c)
  ≡⟨ Eq.cong (λ e → 3 * (e ∸ c)) (Nat.+-comm a 0) ⟩
    3 * (a ∸ c) 
  ∎

arithmetic-manual₄ : (a b c d : val nat) → d < c → 1 Nat.≤ c → 
  a + b + c + c + (2 * (d ∸ d)) Nat.≤ a + (1 + d) + b + d + ((3 * (c ∸ d)) ∸ 1)
arithmetic-manual₄ a b c d d<c 1≤c = 
  let open Nat.≤-Reasoning in
  begin
    a + b + c + c + (2 * (d ∸ d))
  ≡⟨ Eq.cong (λ e → e + (2 * (d ∸ d))) (Nat.+-assoc (a + b) c c) ⟩
    a + b + (c + c) + (2 * (d ∸ d))
  ≡⟨ Eq.cong (λ e → a + b + e + (2 * (d ∸ d))) (Eq.cong (λ e → c + e) (Nat.+-identityʳ c)) ⟨
    a + b + (2 * c) + (2 * (d ∸ d)) 
  ≡⟨ Nat.+-assoc (a + b) (2 * c) (2 * (d ∸ d)) ⟩
    a + b + ((2 * c) + (2 * (d ∸ d)))
  ≡⟨ Eq.cong (λ e → a + b + e) (Nat.*-distribˡ-+ 2 c (d ∸ d)) ⟨
    a + b + (2 * (c + (d ∸ d)))
  ≡⟨ Eq.cong (λ e → a + b + (2 * e)) (Nat.+-∸-assoc c {d} {d} Nat.≤-refl) ⟨
    a + b + (2 * ((c + d) ∸ d))
  ≡⟨ Eq.cong (λ e → a + b + (2 * (e ∸ d))) (Nat.+-comm c d) ⟩
    a + b + (2 * ((d + c) ∸ d))
  ≡⟨ Eq.cong (λ e → a + b + (2 * e)) (Nat.+-∸-assoc d {c} {d} (Nat.<⇒≤ d<c)) ⟩
    a + b + (2 * (d + (c ∸ d)))
  ≡⟨ Eq.cong (λ e → a + b + e) (Nat.+-identityʳ (2 * (d + (c ∸ d)))) ⟨
    a + b + ((2 * (d + (c ∸ d))) + (1 ∸ 1))
  ≡⟨ Eq.cong (λ e → a + b + e) (Nat.+-∸-assoc (2 * (d + (c ∸ d))) {1} {1} Nat.≤-refl) ⟨
    a + b + (((2 * (d + (c ∸ d))) + 1) ∸ 1)
  ≡⟨ Eq.cong (λ e → a + b + (e ∸ 1)) (Nat.+-comm (2 * (d + (c ∸ d))) 1) ⟩
    a + b + ((1 + (2 * (d + (c ∸ d)))) ∸ 1)
  ≡⟨ Eq.cong (λ e → a + b + e) (Nat.+-∸-assoc 1 {2 * (d + (c ∸ d))} {1} 1≤arith1) ⟩
    a + b + (1 + ((2 * (d + (c ∸ d))) ∸ 1))
  ≡⟨ Nat.+-assoc (a + b) 1 ((2 * (d + (c ∸ d))) ∸ 1) ⟨
    a + b + 1 + ((2 * (d + (c ∸ d))) ∸ 1)
  ≡⟨ Eq.cong (λ e → a + b + 1 + (e ∸ 1)) (Nat.*-distribˡ-+ 2 d (c ∸ d)) ⟩
    a + b + 1 + (((2 * d) + (2 * (c ∸ d))) ∸ 1)
  ≡⟨ Eq.cong (λ e → a + b + 1 + e) (Nat.+-∸-assoc (2 * d) {2 * (c ∸ d)} {1} 1≤arith2) ⟩
    a + b + 1 + ((2 * d) + ((2 * (c ∸ d)) ∸ 1))
  ≡⟨ Nat.+-assoc (a + b + 1) (2 * d) ((2 * (c ∸ d)) ∸ 1) ⟨
    a + b + 1 + (2 * d) + ((2 * (c ∸ d)) ∸ 1)
  ≡⟨ Eq.cong (λ e → a + b + 1 + e + ((2 * (c ∸ d)) ∸ 1)) 
      (Eq.cong (λ e → d + e) (Nat.+-identityʳ d)) ⟩
    a + b + 1 + (d + d) + ((2 * (c ∸ d)) ∸ 1)
  ≡⟨ Eq.cong (λ e → e + ((2 * (c ∸ d)) ∸ 1)) (Nat.+-assoc (a + b + 1) d d) ⟨
    a + b + 1 + d + d + ((2 * (c ∸ d)) ∸ 1)
  ≡⟨ Eq.cong (λ e → e + d + ((2 * (c ∸ d)) ∸ 1)) (Nat.+-assoc (a + b) 1 d) ⟩
    a + b + (1 + d) + d + ((2 * (c ∸ d)) ∸ 1)
  ≡⟨ Eq.cong (λ e → e + d + ((2 * (c ∸ d)) ∸ 1)) (Nat.+-assoc a b (1 + d)) ⟩
    a + (b + (1 + d)) + d + ((2 * (c ∸ d)) ∸ 1)
  ≡⟨ Eq.cong (λ e → a + e + d + ((2 * (c ∸ d)) ∸ 1)) (Nat.+-comm b (1 + d)) ⟩
    a + ((1 + d) + b) + d + ((2 * (c ∸ d)) ∸ 1)
  ≡⟨ Eq.cong (λ e → e + d + ((2 * (c ∸ d)) ∸ 1)) (Nat.+-assoc a (1 + d) b) ⟨
    a + (1 + d) + b + d + ((2 * (c ∸ d)) ∸ 1)
  ≤⟨ +-monoʳ-≤ (a + (1 + d) + b + d) 
      (Nat.∸-monoˡ-≤ 1 (Nat.*-monoˡ-≤ (c ∸ d) {2} {3} (s≤s (s≤s z≤n)))) ⟩
    a + (1 + d) + b + d + ((3 * (c ∸ d)) ∸ 1)
  ∎
  where
    1≤arith1 : 1 Nat.≤ 2 * (d + (c ∸ d))
    1≤arith1 = 
      let open Nat.≤-Reasoning in
      begin
        1
      ≤⟨ 1≤c ⟩
        c
      ≤⟨ Nat.m≤n*m c 2 ⟩
        2 * c
      ≡⟨ Eq.cong (λ e → 2 * e) (Nat.m+n∸m≡n d c) ⟨ 
        2 * (d + c ∸ d)
      ≡⟨ Eq.cong (λ e → 2 * e) (Nat.+-∸-assoc d {c} {d} (Nat.<⇒≤ d<c)) ⟩
        2 * (d + (c ∸ d))
      ∎
    1≤arith2 : 1 Nat.≤ 2 * (c ∸ d)
    1≤arith2 = 
      let open Nat.≤-Reasoning in
      begin
        1
      ≤⟨ Nat.m<n⇒0<n∸m d<c ⟩ 
        c ∸ d
      ≤⟨ Nat.m≤n*m (c ∸ d) 2 ⟩
        2 * (c ∸ d)
      ∎

arithmetic-manual₅ : (a b c : val nat) → c < b → 1 Nat.≤ b → 
  a + b + b + b + (3 * (c ∸ c)) ≡ a + (1 + c) + c + c + ((3 * (b ∸ c)) ∸ 1)
arithmetic-manual₅ a b c c<b 1≤b = 
  let open ≡-Reasoning in
  begin
    a + b + b + b + (3 * (c ∸ c))
  ≡⟨ Eq.cong (λ e → e + (3 * (c ∸ c))) (Nat.+-assoc (a + b) b b) ⟩
    a + b + (b + b) + (3 * (c ∸ c))
  ≡⟨ Eq.cong (λ e → e + (3 * (c ∸ c))) (Nat.+-assoc a b (b + b)) ⟩
    a + (b + (b + b)) + (3 * (c ∸ c))
  ≡⟨ Eq.cong (λ e → a + e + (3 * (c ∸ c))) (Eq.cong (λ e → b + (b + e)) (Nat.+-identityʳ b)) ⟨
    a + (3 * b) + (3 * (c ∸ c))
  ≡⟨ Nat.+-assoc a (3 * b) (3 * (c ∸ c)) ⟩
    a + ((3 * b) + (3 * (c ∸ c)))
  ≡⟨ Eq.cong (λ e → a + e) (Nat.*-distribˡ-+ 3 b (c ∸ c)) ⟨
    a + (3 * (b + (c ∸ c)))
  ≡⟨ Eq.cong (λ e → a + (3 * e)) (Nat.+-∸-assoc b {c} {c} Nat.≤-refl) ⟨
    a + (3 * ((b + c) ∸ c))
  ≡⟨ Eq.cong (λ e → a + (3 * (e ∸ c))) (Nat.+-comm b c) ⟩
    a + (3 * ((c + b) ∸ c))
  ≡⟨ Eq.cong (λ e → a + (3 * e)) (Nat.+-∸-assoc c {b} {c} (Nat.<⇒≤ c<b)) ⟩
    a + (3 * (c + (b ∸ c)))
  ≡⟨ Eq.cong (λ e → a + e) (Nat.+-identityʳ (3 * (c + (b ∸ c)))) ⟨
    a + ((3 * (c + (b ∸ c))) + (1 ∸ 1))
  ≡⟨ Eq.cong (λ e → a + e) (Nat.+-∸-assoc (3 * (c + (b ∸ c))) {1} {1} Nat.≤-refl) ⟨ 
    a + (((3 * (c + (b ∸ c))) + 1) ∸ 1)
  ≡⟨ Eq.cong (λ e → a + (e ∸ 1)) (Nat.+-comm (3 * (c + (b ∸ c))) 1) ⟩
    a + ((1 + (3 * (c + (b ∸ c)))) ∸ 1)
  ≡⟨ Eq.cong (λ e → a + e) (Nat.+-∸-assoc 1 {3 * (c + (b ∸ c))} {1} 1≤arith1) ⟩
    a + (1 + ((3 * (c + (b ∸ c))) ∸ 1))
  ≡⟨ Nat.+-assoc a 1 ((3 * (c + (b ∸ c))) ∸ 1) ⟨
    a + 1 + ((3 * (c + (b ∸ c))) ∸ 1)
  ≡⟨ Eq.cong (λ e → a + 1 + (e ∸ 1)) (Nat.*-distribˡ-+ 3 c (b ∸ c)) ⟩
    a + 1 + (((3 * c) + (3 * (b ∸ c))) ∸ 1)
  ≡⟨ Eq.cong (λ e → a + 1 + e) (Nat.+-∸-assoc (3 * c) {3 * (b ∸ c)} {1} 1≤arith2) ⟩
    a + 1 + ((3 * c) + ((3 * (b ∸ c)) ∸ 1))
  ≡⟨ Nat.+-assoc (a + 1) (3 * c) ((3 * (b ∸ c)) ∸ 1) ⟨
    a + 1 + (3 * c) + ((3 * (b ∸ c)) ∸ 1)
  ≡⟨ Eq.cong (λ e → a + 1 + e + ((3 * (b ∸ c)) ∸ 1)) (Eq.cong (λ e → c + (c + e)) (Nat.+-identityʳ c)) ⟩
    a + 1 + (c + (c + c)) + ((3 * (b ∸ c)) ∸ 1)
  ≡⟨ Eq.cong (λ e → e + ((3 * (b ∸ c)) ∸ 1)) (Nat.+-assoc (a + 1) c (c + c)) ⟨
    a + 1 + c + (c + c) + ((3 * (b ∸ c)) ∸ 1)
  ≡⟨ Eq.cong (λ e → e + ((3 * (b ∸ c)) ∸ 1)) (Nat.+-assoc (a + 1 + c) c c) ⟨
    a + 1 + c + c + c + ((3 * (b ∸ c)) ∸ 1)
  ≡⟨ Eq.cong (λ e → e + c + c + ((3 * (b ∸ c)) ∸ 1)) (Nat.+-assoc a 1 c) ⟩
    a + (1 + c) + c + c + ((3 * (b ∸ c)) ∸ 1)
  ∎
  where
    1≤arith1 : 1 Nat.≤ 3 * (c + (b ∸ c))
    1≤arith1 = 
      let open Nat.≤-Reasoning in
      begin
        1
      ≤⟨ 1≤b ⟩
        b
      ≤⟨ Nat.m≤n*m b 3 ⟩
        3 * b
      ≡⟨ Eq.cong (λ e → 3 * e) (Nat.m+n∸m≡n c b) ⟨ 
        3 * (c + b ∸ c)
      ≡⟨ Eq.cong (λ e → 3 * e) (Nat.+-∸-assoc c {b} {c} (Nat.<⇒≤ c<b)) ⟩
        3 * (c + (b ∸ c))
      ∎
    1≤arith2 : 1 Nat.≤ 3 * (b ∸ c)
    1≤arith2 = 
      let open Nat.≤-Reasoning in
      begin
        1
      ≤⟨ Nat.m<n⇒0<n∸m c<b ⟩ 
        b ∸ c
      ≤⟨ Nat.m≤n*m (b ∸ c) 3 ⟩
        3 * (b ∸ c)
      ∎