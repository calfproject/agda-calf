module Calf.Computation.Tensor.Credit where

open import Calf.Value
open import Calf.Computation
open import Calf.Computation.Abstraction
open import Calf.Computation.Credit

open import Cubical.HITs.SetTruncation

open import Calf.Computation.Tensor.Base
open import Calf.Computation.Tensor.Abstract

A⊗▷B≡▷[A⊗B] : ∀ c → (A ⊗ (▷[ c ] B)) ≡ (▷[ c ] (A ⊗ B))
A⊗▷B≡▷[A⊗B] {A} {B} c =
    (A ⊗ (▷[ c ] B))
  ≡⟨ cong (_⊗ (▷[ c ] B)) (sym Abstractionᶜ-id) ⟩
    (Abstractionᶜ A A idᶜ ⊗ (▷[ c ] B))
  ≡⟨ Abstractionᶜ-⊗ {A} {A} {idᶜ} {B} {B} {CHARGE c} ⟩
    Abstractionᶜ (A ⊗ B) (A ⊗ B) (map₂ idᶜ (CHARGE c))
  ≡⟨
    cong (Abstractionᶜ _ _)
      (⊸-path refl refl
          (funExt
            (⊛-≡ squash₂
              (map₂ idᶜ (CHARGE c) .U)
              (CHARGE {A ⊗ B} c .U)
              (λ a b → sym (cong ∣_∣₂ (law c a b))))))
  ⟩
    Abstractionᶜ (A ⊗ B) (A ⊗ B) (CHARGE c)
  ≡⟨ refl ⟩
    (▷[ c ] (A ⊗ B))
  ∎
