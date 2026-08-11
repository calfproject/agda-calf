module Calf.Computation.Free where

open import Calf.Core.Monad
open import Calf.Value
open import Calf.Computation
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.HITs.SetTruncation using (∥_∥₂; ∣_∣₂; squash₂; rec; elim)

opaque
  unfolding M

  F : 𝒱 → 𝒞
  F X .U = M ∥ X ∥₂
  F X .is-set = isSet× isSetℂ squash₂
  F X .charge c (c' , x) = c +ℂ c' , x
  F X .charge/0 {c , x} = cong (_, x) (+ℂ-identityˡ c)
  F X .charge/+ {c , x} {c₁} {c₂} = cong (_, x) (+ℂ-assoc c₁ c₂ c)

  ret : X → U (F X)
  ret x = retᴹ ∣ x ∣₂

  bind : U (F X) → (X → U A) → U A
  bind {A = A} (c , x) k = rec (A .is-set) (A .charge c ∘ k) x

  bind/charge : ∀ {c e k} → bind {A = A} (F X .charge c e) k ≡ A .charge c (bind {A = A} e k)
  bind/charge {A = A} {e = e} =
    elim
      (λ ∣x∣ →
        isProp→isSet $
        A .is-set
          (bind {A = A} (_ , ∣x∣) _)
          (A .charge _ (bind {A = A} (_ , ∣x∣) _)))
      (λ _ → A .charge/+)
      (e .snd)

  F/η : ∀ {x k} → bind {A = A} (ret {X} x) k ≡ k x
  F/η {A = A} = A .charge/0

  syntax bind {A = A} e (λ x → k) = bind[ A ] x ← e ⨾ k

  bind' : (X → U A) → (F X ⊸ A)
  bind' {A = A} k .U (c , x) = rec (A .is-set) (A .charge c ∘ k) x
  bind' {A = A} _ .charge _ (c , x) =
    elim
      (λ ∣x∣ →
        isProp→isSet $
        A .is-set
          (bind {A = A} (_ , ∣x∣) _)
          (A .charge _ (bind {A = A} (_ , ∣x∣) _)))
      (λ _ → A .charge/+)
      x

  bind'/β : {x : X} {k : X → U A} → bind' {A = A} k .U (ret {X} x) ≡ k x
  bind'/β {A = A} = A .charge/0

  bind'/η : bind' (ret {X}) ≡ idᶜ
  bind'/η =
    ⊸-path refl refl (funExt λ (c , x) →
      elim
        (λ x →
          isProp→isSet $
          F _ .is-set
            (bind' {A = F _} ret .U (c , x))
            (c , x))
        (λ x → cong (_, ∣ x ∣₂) (+ℂ-identityʳ c))
        x)

  bind'-assoc :
      (h : X → U (F Y))
    → (k : Y → U A)
    → (e : U (F X))
    → bind' {A = A} k .U (bind' {A = F Y} h .U e)
      ≡ bind' {A = A} (λ x → bind' {A = A} k .U (h x)) .U e
  bind'-assoc {Y = Y} {A = A} h k (c , x) =
    elim
      (λ x →
        isProp→isSet $
        A .is-set
          (bind' {A = A} k .U (bind' {A = F Y} h .U (c , x)))
          (bind' {A = A} (λ x → bind' {A = A} k .U (h x)) .U (c , x)))
      (λ x → bind' {A = A} k .charge c (h x))
      x

  bind'-charge :
      (h : X → U A)
    → (c : ℂ)
    → (e : U (F X))
    → bind' {A = A} (λ x → A .charge c (h x)) .U e
      ≡ bind' {A = A} h .U (F X .charge c e)
  bind'-charge {A = A} h c (c' , x) =
    cong (λ e → rec (A .is-set) e x) $
    funExt λ x →
    sym (A .charge/+) ∙ cong (λ d → A .charge d (h x)) (+ℂ-comm c' c)

  bind'-map :
      (f : A ⊸ B)
    → (h : X → U A)
    → (e : U (F X))
    → f .U (bind' {A = A} h .U e)
      ≡ bind' {A = B} (λ x → f .U (h x)) .U e
  bind'-map {A = A} {B = B} f h (c , x) =
    elim
      (λ x →
        isProp→isSet $
        B .is-set
          (f .U (bind' {A = A} h .U (c , x)))
          (bind' {A = B} (λ x → f .U (h x)) .U (c , x)))
      (λ x → f .charge c (h x))
      x

bind'-isEquiv : isEquiv (bind' {X} {A})
bind'-isEquiv {X} {A} = isoToIsEquiv $
  iso
    (bind' {X} {A})
    (λ f → f .U ∘ ret {X})
    (λ f → ⊸-path refl refl (funExt λ e → sym (bind'-map f ret e) ∙ cong (f .U) (cong ((_$ e) ∘ U) bind'/η)))
    (λ g → funExt λ x → bind'/β)

F-adjoint : (X → U A) ≃ (F X ⊸ A)
F-adjoint = bind' , bind'-isEquiv

ret' : (F X ⊸ A) → (X → U A)
ret' e x = e .U (ret x)

private variable Δ : 𝒞

bindᶜ : (Δ ⊸ F X) → (X → U A) → (Δ ⊸ A)
bindᶜ e k = e ⨾ᶜ bind' k

syntax bindᶜ e (λ x → k) = bind x ← e ⨾ k

map : (X → Y) → (F X ⊸ F Y)
map f = bind' (ret ∘ f)

bind'-path : (f g : F X ⊸ A) →
  (f .U ∘ ret ≡ g .U ∘ ret)
  → f ≡ g
bind'-path f g pf-ret = sym (secEq F-adjoint f) ∙ cong bind' pf-ret ∙ secEq F-adjoint g
