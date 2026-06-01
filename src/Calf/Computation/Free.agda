module Calf.Computation.Free where

open import Calf.Core.Monad
open import Calf.Value
open import Calf.Computation
open import Cubical.Foundations.Prelude

opaque
  unfolding M

  F : 𝒱 → 𝒞
  F X .U = M X
  F X .charge c (c' , x) = c +ℂ c' , x
  F X .charge/0 {c , x} = cong (_, x) (+ℂ-identityˡ c)
  F X .charge/+ {c , x} {c₁} {c₂} = cong (_, x) (+ℂ-assoc c₁ c₂ c)

  ret : val X → cmp (F X)
  ret {X} = ?

  bind : cmp (F X) → (val X → cmp A) → cmp A
  bind {A = A} (c , x) k = A .charge c (k x)

  bind/charge : ∀ {c e k} → bind {A = A} (F X .charge c e) k ≡ A .charge c (bind {A = A} e k)
  bind/charge {A = A} = A .charge/+

  F/η : ∀ {x k} → bind {A = A} (ret {X} x) k ≡ k x
  F/η {A = A} = A .charge/0

  syntax bind {A = A} e (λ x → k) = bind[ A ] x ← e ⨾ k

  variable
    Δ : 𝒞

  bind' : (Δ ⊸ F X) → (val X → cmp A) → (Δ ⊸ A)
  bind' {A = A} e k .U δ = let (c , x) = e .U δ in A .charge c (k x)
  bind' {Δ} {A = A} e k .charge c δ =
      A .charge (e .U (Δ .charge c δ) .fst) (k (e .U (Δ .charge c δ) .snd))
    ≡⟨ cong (λ hole → A .charge (hole .fst) (k (hole .snd))) (e .charge c δ) ⟩
      A .charge (c +ℂ e .U δ .fst) (k (e .U δ .snd))
    ≡⟨ A .charge/+ ⟩
      A .charge c (A .charge (e .U δ .fst) (k (e .U δ .snd)))
    ∎
  syntax bind' e (λ x → k) = bind x ← e ⨾ k
