module Calf.Computation.Free where

open import Calf.Core.Monad
open import Calf.Value
open import Calf.Value.Product
open import Calf.Computation
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism

opaque
  unfolding M

  F : 𝒱 → 𝒞
  F X .U = M ∥ X ∥ᴾ
  F X .is-preorder = isPreorder× isPreorderℂ isPreorderP
  F X .charge c (c' , x) = c +ℂ c' , x
  F X .charge/0 {c , x} = cong (_, x) (+ℂ-identityˡ c)
  F X .charge/+ {c , x} {c₁} {c₂} = cong (_, x) (+ℂ-assoc c₁ c₂ c)

  ret : X → U (F X)
  ret x = retᴹ (ηᴾ x)

  bind : U (F X) → (X → U A) → U A
  bind {A = A} (c , x) k = rec (A .is-preorder) (A .charge c ∘ k) x

  bind/charge : ∀ {c e k} → bind {A = A} (F X .charge c e) k ≡ A .charge c (bind {A = A} e k)
  bind/charge {A = A} {e = e} =
    rec-unique
      (A .is-preorder)
      (λ z → bind {A = A} (_ , z) _)
      (λ z → A .charge _ (bind {A = A} (_ , z) _))
      (λ _ → A .charge/+)
      (e .snd)

  bind/β : ∀ {x k} → bind {A = A} (ret {X} x) k ≡ k x
  bind/β {A = A} = A .charge/0

  syntax bind {A = A} e (λ x → k) = bind[ A ] x ← e ⨾ k

  variable
    Δ : 𝒞

  bind' : (X → U A) → (F X ⊸ A)
  bind' {A = A} k .U (c , x) = rec (A .is-preorder) (A .charge c ∘ k) x
  bind' {A = A} _ .charge _ (c , x) =
    rec-unique
      (A .is-preorder)
      (λ z → bind {A = A} (_ , z) _)
      (λ z → A .charge _ (bind {A = A} (_ , z) _))
      (λ _ → A .charge/+)
      x

  bind'/β : {x : X} {k : X → U A} → bind' {A = A} k .U (ret {X} x) ≡ k x
  bind'/β {A = A} = A .charge/0

  bind'/η : bind' (ret {X}) ≡ idᶜ
  bind'/η =
    ⊸-path refl refl (funExt λ (c , x) →
      rec-unique
        (F _ .is-preorder)
        (λ z → bind' {A = F _} ret .U (c , z))
        (λ z → c , z)
        (λ x → cong (_, ηᴾ x) (+ℂ-identityʳ c))
        x)

  bind'-assoc :
      (h : X → U (F Y))
    → (k : Y → U A)
    → (e : U (F X))
    → bind' {A = A} k .U (bind' {A = F Y} h .U e)
      ≡ bind' {A = A} (λ x → bind' {A = A} k .U (h x)) .U e
  bind'-assoc {Y = Y} {A = A} h k (c , x) =
    rec-unique
      (A .is-preorder)
      (λ z → bind' {A = A} k .U (bind' {A = F Y} h .U (c , z)))
      (λ z → bind' {A = A} (λ x → bind' {A = A} k .U (h x)) .U (c , z))
      (λ x → bind' {A = A} k .charge c (h x))
      x

  bind'-charge :
      (h : X → U A)
    → (c : ℂ)
    → (e : U (F X))
    → bind' {A = A} (λ x → A .charge c (h x)) .U e
      ≡ bind' {A = A} h .U (F X .charge c e)
  bind'-charge {A = A} h c (c' , x) =
    cong (λ e → rec (A .is-preorder) e x) $
    funExt λ x →
    sym (A .charge/+) ∙ cong (λ d → A .charge d (h x)) (+ℂ-comm c' c)

  bind'-map :
      (f : A ⊸ B)
    → (h : X → U A)
    → (e : U (F X))
    → f .U (bind' {A = A} h .U e)
      ≡ bind' {A = B} (λ x → f .U (h x)) .U e
  bind'-map {A = A} {B = B} f h (c , x) =
    rec-unique
      (B .is-preorder)
      (λ z → f .U (bind' {A = A} h .U (c , z)))
      (λ z → bind' {A = B} (λ x → f .U (h x)) .U (c , z))
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

bindᶜ : (Δ ⊸ F X) → (X → U A) → (Δ ⊸ A)
bindᶜ e k = e ⨾ᶜ bind' k

-- syntax bindᶜ e (λ x → k) = bind x ← e ⨾ k

map : (X → Y) → (F X ⊸ F Y)
map f = bind' (ret ∘ f)

bind'-path : (f g : F X ⊸ A) →
  (f .U ∘ ret ≡ g .U ∘ ret)
  → f ≡ g
bind'-path f g pf-ret = sym (secEq F-adjoint f) ∙ cong bind' pf-ret ∙ secEq F-adjoint g

costed : (X → Y) → (X → ℂ) → (F X ⊸ F Y)
costed f Φ = bind' λ x → F _ .charge (Φ x) (ret (f x))

costed-≡ : {f g : X → Y} {Φ Ψ : X → ℂ}
  → (∀ x → f x ≡ g x) → (∀ x → Φ x ≡ Ψ x) → costed f Φ ≡ costed g Ψ
costed-≡ p q i = costed (λ x → p x i) (λ x → q x i)

costed-⨾ᶜ : (f : X → Y) (Φ : X → ℂ) (g : Y → Z) (Ψ : Y → ℂ)
  → costed f Φ ⨾ᶜ costed g Ψ ≡ costed (g ∘ f) (λ x → Φ x +ℂ Ψ (f x))
costed-⨾ᶜ f Φ g Ψ =
  bind'-path _ _ (funExt λ x →
      cong (costed g Ψ .U) bind'/β
    ∙ costed g Ψ .charge (Φ x) (ret (f x))
    ∙ cong (F _ .charge (Φ x)) bind'/β
    ∙ sym (F _ .charge/+)
    ∙ sym bind'/β)

map-costed : (f : X → Y) (g : Y → Z) (Ψ : Y → ℂ)
  → map f ⨾ᶜ costed g Ψ ≡ costed (g ∘ f) (Ψ ∘ f)
map-costed f g Ψ =
  bind'-path _ _ (funExt λ x → cong (costed g Ψ .U) bind'/β ∙ bind'/β ∙ sym bind'/β)
