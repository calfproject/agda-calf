module Calf.Computation.Free where

open import Calf.Core.Monad
open import Calf.Value
open import Calf.Computation
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

opaque
  unfolding M

  F : 𝒱 → 𝒞
  F X .U = M X
  F X .charge c (c' , x) = c +ℂ c' , x
  F X .charge/0 {c , x} = cong (_, x) (+ℂ-identityˡ c)
  F X .charge/+ {c , x} {c₁} {c₂} = cong (_, x) (+ℂ-assoc c₁ c₂ c)

  ret : val X → cmp (F X)
  ret {X} = retᴹ {X}

  bind : cmp (F X) → (val X → cmp A) → cmp A
  bind {A = A} (c , x) k = A .charge c (k x)

  bind/charge : ∀ {c e k} → bind {A = A} (F X .charge c e) k ≡ A .charge c (bind {A = A} e k)
  bind/charge {A = A} = A .charge/+

  F/η : ∀ {x k} → bind {A = A} (ret {X} x) k ≡ k x
  F/η {A = A} = A .charge/0

  syntax bind {A = A} e (λ x → k) = bind[ A ] x ← e ⨾ k

  variable
    Δ : 𝒞

  bind' : (val X → cmp A) → (F X ⊸ A)
  bind' {A = A} k .U (c , x) = A .charge c (k x)
  bind' {A = A} _ .charge _ _ = A .charge/+

  bind'/β : {x : val X} {k : val X → cmp A} → bind' {A = A} k .U (ret {X} x) ≡ k x
  bind'/β {A = A} = A .charge/0

  bind'/η : bind' (ret {X}) ≡ idᶜ
  bind'/η = ⊸-path refl refl (funExt λ (c , x) → cong (_, x) (+ℂ-identityʳ c))

  bind'-assoc :
      (h : val X → cmp (F Y))
    → (k : val Y → cmp A)
    → (e : cmp (F X))
    → bind' {A = A} k .U (bind' {A = F Y} h .U e)
      ≡ bind' {A = A} (λ x → bind' {A = A} k .U (h x)) .U e
  bind'-assoc {Y = Y} {A = A} h k (c , x) = bind' {X = Y} {A = A} k .charge c (h x)

  bind'-charge :
      (h : val X → cmp A)
    → (c : val ℂ)
    → (e : cmp (F X))
    → bind' {A = A} (λ x → A .charge c (h x)) .U e
      ≡ bind' {A = A} h .U (F X .charge c e)
  bind'-charge {A = A} h c (c' , x) =
    sym (A .charge/+) ∙ cong (λ d → A .charge d (h x)) (+ℂ-comm c' c)

  bind'-map :
      (f : A ⊸ B)
    → (h : val X → cmp A)
    → (e : cmp (F X))
    → f .U (bind' {A = A} h .U e) ≡ bind' {A = B} (λ x → f .U (h x)) .U e
  bind'-map f h (c , x) = f .charge c (h x)

ret' : (F X ⊸ A) → (val X → cmp A)
ret' e x = e .U (ret x)

bindᶜ : (Δ ⊸ F X) → (val X → cmp A) → (Δ ⊸ A)
bindᶜ e k = e ⨾ᶜ bind' k

syntax bindᶜ e (λ x → k) = bind x ← e ⨾ k

map : (val X → val Y) → (F X ⊸ F Y)
map f = bind' (ret ∘ f)
