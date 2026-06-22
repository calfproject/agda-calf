open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence using (ua)

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

lolli-currying : (A ⊗ B ⊸ C) ≡ (A ⊸ (B ⊸ᶜ C))
lolli-currying {A} {B} {C} =
  ua (isoToEquiv (iso curryᶜ uncurryᶜ curryᶜ-uncurryᶜ uncurryᶜ-curryᶜ))
  where
    curryᶜ : (A ⊗ B ⊸ C) → (A ⊸ (B ⊸ᶜ C))
    curryᶜ f .U a .U b = f .U (inj a b 0ℂ)
    curryᶜ f .U a .charge c b =
        f .U (inj a (B .charge c b) 0ℂ)
      ≡⟨ cong (f .U) (law₂ 0ℂ c a b) ⟩
        f .U (inj a b (0ℂ +ℂ c))
      ≡⟨ cong (f .U ∘ inj a b) (+ℂ-identityˡ c) ⟩
        f .U (inj a b c)
      ≡⟨ cong (f .U ∘ inj a b) (sym (+ℂ-identityʳ c)) ⟩
        f .U (inj a b (c +ℂ 0ℂ))
      ≡⟨ f .charge c (inj a b 0ℂ) ⟩
        C .charge c (f .U (inj a b 0ℂ))
      ∎
    curryᶜ f .charge c a =
      ⊸-path refl refl (funExt λ b →
          f .U (inj (A .charge c a) b 0ℂ)
        ≡⟨ cong (f .U) (law₁ 0ℂ c a b) ⟩
          f .U (inj a b (0ℂ +ℂ c))
        ≡⟨ cong (f .U ∘ inj a b) (+ℂ-identityˡ c) ⟩
          f .U (inj a b c)
        ≡⟨ cong (f .U ∘ inj a b) (sym (+ℂ-identityʳ c)) ⟩
          f .U (inj a b (c +ℂ 0ℂ))
        ≡⟨ f .charge c (inj a b 0ℂ) ⟩
          C .charge c (f .U (inj a b 0ℂ))
        ∎)

    uncurryᶜ-U : (A ⊸ (B ⊸ᶜ C)) → A U⊗ B → U C
    uncurryᶜ-U f (inj a b c) = C .charge c (f .U a .U b)
    uncurryᶜ-U f (law₁ c c' a b i) =
      (  C .charge c (f .U (A .charge c' a) .U b)
       ≡⟨ cong (C .charge c) (cong (_$ b) (cong U (f .charge c' a))) ⟩
         C .charge c (C .charge c' (f .U a .U b))
       ≡⟨ sym (C .charge/+ {a = f .U a .U b} {c₁ = c} {c₂ = c'}) ⟩
         C .charge (c +ℂ c') (f .U a .U b)
       ∎) i
    uncurryᶜ-U f (law₂ c c' a b i) =
      (  C .charge c (f .U a .U (B .charge c' b))
       ≡⟨ cong (C .charge c) (f .U a .charge c' b) ⟩
         C .charge c (C .charge c' (f .U a .U b))
       ≡⟨ sym (C .charge/+ {a = f .U a .U b} {c₁ = c} {c₂ = c'}) ⟩
         C .charge (c +ℂ c') (f .U a .U b)
       ∎) i
    uncurryᶜ-U f (squash x y p q i j) =
      C .is-set
        (uncurryᶜ-U f x)
        (uncurryᶜ-U f y)
        (cong (uncurryᶜ-U f) p)
        (cong (uncurryᶜ-U f) q)
        i j

    uncurryᶜ-charge
      : (f : A ⊸ (B ⊸ᶜ C)) (c : ℂ) (x : U (A ⊗ B))
      → uncurryᶜ-U f ((A ⊗ B) .charge c x) ≡ C .charge c (uncurryᶜ-U f x)
    uncurryᶜ-charge f c (inj a b c') =
      C .charge/+ {a = f .U a .U b} {c₁ = c} {c₂ = c'}
    uncurryᶜ-charge f c (law₁ c₁ c' a b i) =
      isSet→isSet'
        (C .is-set)
        (C .charge/+ {a = f .U (A .charge c' a) .U b} {c₁ = c} {c₂ = c₁})
        (C .charge/+ {a = f .U a .U b} {c₁ = c} {c₂ = c₁ +ℂ c'})
        (λ k → uncurryᶜ-U f ((A ⊗ B) .charge c (law₁ c₁ c' a b k)))
        (λ k → C .charge c (uncurryᶜ-U f (law₁ c₁ c' a b k)))
        i
    uncurryᶜ-charge f c (law₂ c₁ c' a b i) =
      isSet→isSet'
        (C .is-set)
        (C .charge/+ {a = f .U a .U (B .charge c' b)} {c₁ = c} {c₂ = c₁})
        (C .charge/+ {a = f .U a .U b} {c₁ = c} {c₂ = c₁ +ℂ c'})
        (λ k → uncurryᶜ-U f ((A ⊗ B) .charge c (law₂ c₁ c' a b k)))
        (λ k → C .charge c (uncurryᶜ-U f (law₂ c₁ c' a b k)))
        i
    uncurryᶜ-charge f c (squash x y p q i j) =
      isSet→SquareP
        (λ k l → isProp→isSet
          (C .is-set
            (uncurryᶜ-U f ((A ⊗ B) .charge c (squash x y p q k l)))
            (C .charge c (uncurryᶜ-U f (squash x y p q k l)))))
        (cong (uncurryᶜ-charge f c) p)
        (cong (uncurryᶜ-charge f c) q)
        (λ _ → uncurryᶜ-charge f c x)
        (λ _ → uncurryᶜ-charge f c y)
        i j

    uncurryᶜ : (A ⊸ (B ⊸ᶜ C)) → (A ⊗ B ⊸ C)
    uncurryᶜ f .U = uncurryᶜ-U f
    uncurryᶜ f .charge = uncurryᶜ-charge f

    curryᶜ-uncurryᶜ : (f : A ⊸ (B ⊸ᶜ C)) → curryᶜ (uncurryᶜ f) ≡ f
    curryᶜ-uncurryᶜ f =
      ⊸-path refl refl (funExt λ a →
        ⊸-path refl refl (funExt λ b → C .charge/0))

    uncurryᶜ-curryᶜ-U : (f : A ⊗ B ⊸ C) (x : U (A ⊗ B))
      → uncurryᶜ-U (curryᶜ f) x ≡ f .U x
    uncurryᶜ-curryᶜ-U f (inj a b c) =
        C .charge c (f .U (inj a b 0ℂ))
      ≡⟨ sym (f .charge c (inj a b 0ℂ)) ⟩
        f .U (inj a b (c +ℂ 0ℂ))
      ≡⟨ cong (f .U ∘ inj a b) (+ℂ-identityʳ c) ⟩
        f .U (inj a b c)
      ∎
    uncurryᶜ-curryᶜ-U f (law₁ c c' a b i) =
      isSet→isSet'
        (C .is-set)
        (uncurryᶜ-curryᶜ-U f (inj (A .charge c' a) b c))
        (uncurryᶜ-curryᶜ-U f (inj a b (c +ℂ c')))
        (λ k → uncurryᶜ-U (curryᶜ f) (law₁ c c' a b k))
        (λ k → f .U (law₁ c c' a b k))
        i
    uncurryᶜ-curryᶜ-U f (law₂ c c' a b i) =
      isSet→isSet'
        (C .is-set)
        (uncurryᶜ-curryᶜ-U f (inj a (B .charge c' b) c))
        (uncurryᶜ-curryᶜ-U f (inj a b (c +ℂ c')))
        (λ k → uncurryᶜ-U (curryᶜ f) (law₂ c c' a b k))
        (λ k → f .U (law₂ c c' a b k))
        i
    uncurryᶜ-curryᶜ-U f (squash x y p q i j) =
      isSet→SquareP
        (λ k l → isProp→isSet
          (C .is-set
            (uncurryᶜ-U (curryᶜ f) (squash x y p q k l))
            (f .U (squash x y p q k l))))
        (cong (uncurryᶜ-curryᶜ-U f) p)
        (cong (uncurryᶜ-curryᶜ-U f) q)
        (λ _ → uncurryᶜ-curryᶜ-U f x)
        (λ _ → uncurryᶜ-curryᶜ-U f y)
        i j

    uncurryᶜ-curryᶜ : (f : A ⊗ B ⊸ C) → uncurryᶜ (curryᶜ f) ≡ f
    uncurryᶜ-curryᶜ f =
      ⊸-path refl refl (funExt (uncurryᶜ-curryᶜ-U f))
