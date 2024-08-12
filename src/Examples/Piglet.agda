{-# OPTIONS --rewriting #-}

module Examples.Piglet where

open import Relation.Binary.PropositionalEquality as Eq
open import Data.Rational as ℚ
open import Data.Integer.Base as ℤ using (ℤ; +_; +0; +[1+_]; -[1+_])

open import Data.Interval as 𝕀
open import Calf.Data.Nat as Nat

open import Function using (_$_)

open import Piglet


postulate
  flip : (X : tp⁻) → 𝕀 → cmp X → cmp X → cmp X

  flip/0 : {e₀ e₁ : cmp X} →
    flip X 0𝕀 e₀ e₁ ≡ e₀
  flip/same : (X : tp⁻) (e : cmp X) {p : 𝕀} →
    flip X p e e ≡ e

  flip/sym : (X : tp⁻) (p : 𝕀) (e₀ e₁ : cmp X) →
    flip X p e₀ e₁ ≡ flip X (1- p) e₁ e₀
  flip/assocʳ : (X : tp⁻) (e₀ e₁ e₂ : cmp X) {p q r : 𝕀} → p ≡ (p ∨ q) ∧ r →
    flip X p (flip X q e₀ e₁) e₂ ≡ flip X (p ∨ q) e₀ (flip X r e₁ e₂)

flip/1 : {e₀ e₁ : cmp X} → flip X 1𝕀 e₀ e₁ ≡ e₁
flip/1 {X} {e₀} {e₁} =
  let open ≡-Reasoning in
  begin
    flip X 1𝕀 e₀ e₁
  ≡⟨ flip/sym X 1𝕀 e₀ e₁ ⟩
    flip X 0𝕀 e₁ e₀
  ≡⟨ flip/0 ⟩
    e₁
  ∎

flip/assocˡ : (X : tp⁻) (e₀ e₁ e₂ : cmp X) {p q r : 𝕀} → p ≡ (p ∧ q) ∨ r →
  flip X p e₀ (flip X q e₁ e₂) ≡ flip X (p ∧ q) (flip X r e₀ e₁) e₂
flip/assocˡ X e₀ e₁ e₂ {p} {q} {r} h =
  let open ≡-Reasoning in
  begin
    flip X p e₀ (flip X q e₁ e₂)
  ≡⟨ Eq.cong (λ p → flip X p e₀ (flip X q e₁ e₂)) h ⟩
    flip X (p ∧ q ∨ r) e₀ (flip X q e₁ e₂)
  ≡˘⟨ flip/assocʳ X e₀ e₁ e₂ (Eq.cong (_∧ q) h) ⟩
    flip X (p ∧ q) (flip X r e₀ e₁) e₂
  ∎

postulate
  bind/flip : {f : val A → cmp X} {p : 𝕀} {e₀ e₁ : cmp (F A)} →
    bind {A = A} X (flip (F A) p e₀ e₁) f ≡ flip X p (bind X e₀ f) (bind X e₁ f)
  {-# REWRITE bind/flip #-}


postulate
  convex : 𝕀 → tp⁻ → tp⁻ → tp⁻

_⊗[_]_ : tp⁻ → 𝕀 → tp⁻ → tp⁻
X ⊗[ p ] Y = convex p X Y

postulate
  ℚ⁻ : tp⁻

  ℚ/decode : val (U ℚ⁻) ≡ ℚ
  {-# REWRITE ℚ/decode #-}


die : cmp (F nat)
die =
  flip (F nat) (1 𝕀./ 6) (ret 1) $
  flip (F nat) (1 𝕀./ 5) (ret 2) $
  {!   !}

nat-to-real : ℕ → ℚ
nat-to-real = {! ...from stdlib...  !}

𝔼 : cmp (F nat) → cmp ℚ⁻
𝔼 e = bind ℚ⁻ e nat-to-real

_ : 𝔼 die ≡ + 7 ℚ./ 2
_ = {!   !}

-- ℙ P = bind

-- _ : (bind ? die λ x → F (x Nat.> 1)) ≡ flip ? (F ⊤) (F ⊥)
