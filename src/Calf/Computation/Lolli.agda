open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence using (ua)
open import Cubical.HITs.SetTruncation using (∣_∣₂; rec)

module Calf.Computation.Lolli where

open import Calf.Core.Cost
open import Calf.Value
open import Calf.Computation
open import Calf.Computation.Tensor

infix 1 _⊸ᶜ_

_⊸ᶜ_ : 𝒞 → 𝒞 → 𝒞
(A ⊸ᶜ B) .U = A ⊸ B
(A ⊸ᶜ B) .is-set =
  isSetRetract
    (λ f → f .U , f .charge)
    (λ (U , charge) → record { U = U ; charge = charge })
    (λ _ → refl)
    (isSetΣSndProp
      (isSetΠ λ _ → B .is-set)
      (isProp⊸charge A B))
(A ⊸ᶜ B) .charge c f .U a = B .charge c (f .U a)
(A ⊸ᶜ B) .charge c f .charge c' a =
  cong (B .charge c) (f .charge c' a)
  ∙ cong ((_$ f .U a) ∘ U) (CHARGE-comm {B} c' c)
(A ⊸ᶜ B) .charge/0 = ⊸-path refl refl (funExt λ a → B .charge/0)
(A ⊸ᶜ B) .charge/+ = ⊸-path refl refl (funExt λ a → B .charge/+)

opaque
  unfolding _⊗_ _∥_

  lolli-currying : (A ⊗ B ⊸ C) ≡ (A ⊸ (B ⊸ᶜ C))
  lolli-currying {A} {B} {C} =
    ua (isoToEquiv (iso curryᶜ uncurryᶜ curryᶜ-uncurryᶜ uncurryᶜ-curryᶜ))
    where
      curryᶜ : (A ⊗ B ⊸ C) → (A ⊸ (B ⊸ᶜ C))
      curryᶜ f .U a .U b = f .U (a ∥ b)
      curryᶜ f .U a .charge c b =
          f .U (a ∥ (B .charge c b))
        ≡⟨ cong (f .U) (sym (cong ∣_∣₂ (law c a b))) ⟩
          f .U ((A .charge c a) ∥ b)
        ≡⟨ f .charge c (a ∥ b) ⟩
          C .charge c (f .U (a ∥ b))
        ∎
      curryᶜ f .charge c a =
        ⊸-path refl refl (funExt λ b → f .charge c (a ∥ b))

      uncurryᶜ-U : (A ⊸ (B ⊸ᶜ C)) → A ⊛ B → U C
      uncurryᶜ-U f (inj a b) = f .U a .U b
      uncurryᶜ-U f (law c a b i) =
        ( cong (λ g → g .U b) (f .charge c a)
        ∙ sym (f .U a .charge c b) ) i

      uncurryᶜ : (A ⊸ (B ⊸ᶜ C)) → (A ⊗ B ⊸ C)
      uncurryᶜ f .U = rec (C .is-set) (uncurryᶜ-U f)
      uncurryᶜ f .charge c =
        ⊛-≡ (C .is-set)
          (λ x → uncurryᶜ f .U ((A ⊗ B) .charge c x))
          (λ x → C .charge c (uncurryᶜ f .U x))
          (λ a b → cong (λ g → g .U b) (f .charge c a))

      curryᶜ-uncurryᶜ : (f : A ⊸ (B ⊸ᶜ C)) → curryᶜ (uncurryᶜ f) ≡ f
      curryᶜ-uncurryᶜ f =
        ⊸-path refl refl (funExt λ a → ⊸-path refl refl refl)

      uncurryᶜ-curryᶜ : (f : A ⊗ B ⊸ C) → uncurryᶜ (curryᶜ f) ≡ f
      uncurryᶜ-curryᶜ f =
        ⊸-path refl refl
          (funExt
            (⊛-≡ (C .is-set)
              (λ x → uncurryᶜ (curryᶜ f) .U x)
              (f .U)
              (λ a b → refl)))
