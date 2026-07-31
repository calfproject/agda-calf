module Calf.Computation.Sum where

open import Calf.Value
open import Calf.Value.Sum public
open import Calf.Computation

_+ᶜ_ : 𝒞 → 𝒞 → 𝒞
(A +ᶜ B) .U = A .U ⊎ B .U
(A +ᶜ B) .is-set = isSet⊎ (A .is-set) (B .is-set)
(A +ᶜ B) .charge c (inj₁ a) = inj₁ (A .charge c a)
(A +ᶜ B) .charge c (inj₂ b) = inj₂ (B .charge c b)
(A +ᶜ B) .charge/0 {inj₁ a} = cong inj₁ (A .charge/0)
(A +ᶜ B) .charge/0 {inj₂ b} = cong inj₂ (B .charge/0)
(A +ᶜ B) .charge/+ {inj₁ a} = cong inj₁ (A .charge/+)
(A +ᶜ B) .charge/+ {inj₂ b} = cong inj₂ (B .charge/+)

inj₁ᶜ : A ⊸ A +ᶜ B
inj₁ᶜ .U a = inj₁ a
inj₁ᶜ .charge c a = refl

inj₂ᶜ : B ⊸ A +ᶜ B
inj₂ᶜ .U b = inj₂ b
inj₂ᶜ .charge c b = refl

caseᶜ : (A ⊸ C) → (B ⊸ C) → (A +ᶜ B ⊸ C)
caseᶜ f g .U ab = elim (f .U) (g .U) ab
caseᶜ f g .charge c (inj₁ a) = f .charge c a
caseᶜ f g .charge c (inj₂ b) = g .charge c b

open import Calf.Computation.Credit

▷A+▷B≡▷[A+B] : ∀ c → ((▷[ c ] A) +ᶜ (▷[ c ] B)) ≡ (▷[ c ] (A +ᶜ B))
▷A+▷B≡▷[A+B] c = conservativity fwd fwd-equiv
  where
    fwd : ((▷[ c ] A) +ᶜ (▷[ c ] B)) ⊸ (▷[ c ] (A +ᶜ B))
    fwd = caseᶜ (▷-map inj₁ᶜ) (▷-map inj₂ᶜ)

    fwd-equiv : isEquivᶜ fwd
    fwd-equiv = isoToIsEquiv (iso (fwd .U) inv sect retr)
      where
        inv : U (▷[ c ] (A +ᶜ B)) → U ((▷[ c ] A) +ᶜ (▷[ c ] B))
        inv a = {!   !}

        sect : ∀ a → fwd .U (inv a) ≡ a
        sect a = {!  !}

        retr : ∀ z → inv (fwd .U z) ≡ z
        retr = {!   !}

open import Calf.Computation.Tensor
open import Cubical.HITs.SetTruncation renaming (map to map')

A⊗C+B⊗C≡[A+B]⊗C : (A ⊗ C) +ᶜ (B ⊗ C) ≡ (A +ᶜ B) ⊗ C
A⊗C+B⊗C≡[A+B]⊗C {A} {C} {B} = conservativity fwd fwd-equiv
  where
    fwd : (A ⊗ C) +ᶜ (B ⊗ C) ⊸ (A +ᶜ B) ⊗ C
    fwd = caseᶜ (map₂ inj₁ᶜ idᶜ) (map₂ inj₂ᶜ idᶜ)

    fwd-equiv : isEquivᶜ fwd
    fwd-equiv = isoToIsEquiv (iso (fwd .U) inv sect retr)
      where
        inv : U ((A +ᶜ B) ⊗ C) → U ((A ⊗ C) +ᶜ (B ⊗ C))
        inv ∣ inj (inj₁ a) c ∣₂ = inj₁ ∣ inj a c ∣₂
        inv ∣ inj (inj₂ b) c ∣₂ = inj₂ ∣ inj b c ∣₂
        inv ∣ law c₀ (inj₁ a) c i ∣₂ = inj₁ ∣ law c₀ a c i ∣₂
        inv ∣ law c₀ (inj₂ b) c i ∣₂ = inj₂ ∣ law c₀ b c i ∣₂
        inv (squash₂ a a₁ p q i i₁) = {! a  !}

        sect : ∀ a → fwd .U (inv a) ≡ a
        sect a = {!  !}

        retr : ∀ z → inv (fwd .U z) ≡ z
        retr = {!   !}
