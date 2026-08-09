module Calf.Computation.Copower where

open import Calf.Value
open import Calf.Value.Sigma public
open import Calf.Computation
open import Cubical.Foundations.Prelude using (cong)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

Σᶜ : (X : 𝒱ₛ) → (⟨ X ⟩ → 𝒞) → 𝒞
Σᶜ isSetX A .U = Σ[ x ∈ _ ] U (A x)
Σᶜ isSetX A .is-set = isSetΣ (str isSetX) λ x → A x .is-set
Σᶜ isSetX A .charge c (x , a) = x , A x .charge c a
Σᶜ isSetX A .charge/0 {x , a} = cong (x ,_) (A x .charge/0)
Σᶜ isSetX A .charge/+ {x , a} = cong (x ,_) (A x .charge/+)

syntax Σᶜ X (λ x → A) = [ x ∈ X ] ⋊ A

_⋊_ : 𝒱ₛ → 𝒞 → 𝒞
X ⋊ A = [ _ ∈ X ] ⋊ A

Σᶜ-map : ∀ {X A B} → ((x : ⟨ X ⟩) → A x ⊸ B x) → Σᶜ X A ⊸ Σᶜ X B
Σᶜ-map f .U (x , a) = x , f x .U a
Σᶜ-map f .charge c (x , a) = cong (x ,_) (f x .charge c a)

Σᶜ-map-idᶜ : ∀ {X : 𝒱ₛ} {A : ⟨ X ⟩ → 𝒞} →
  Σᶜ-map {X = X} (λ x → idᶜ {A = A x}) ≡ idᶜ
Σᶜ-map-idᶜ = ⊸-path refl refl refl

Σᶜ-map-⨾ᶜ :
  ∀ {X : 𝒱ₛ} {A B C : ⟨ X ⟩ → 𝒞}
  (f : (x : ⟨ X ⟩) → A x ⊸ B x)
  (g : (x : ⟨ X ⟩) → B x ⊸ C x) →
  Σᶜ-map {X = X} f ⨾ᶜ Σᶜ-map {X = X} g ≡
  Σᶜ-map {X = X} (λ x → f x ⨾ᶜ g x)
Σᶜ-map-⨾ᶜ f g = ⊸-path refl refl refl
