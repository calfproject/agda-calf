module Calf.Computation.Tensor.Credit where

open import Calf.Core.Abstract using (ABS)
open import Calf.Core.Cost
open import Calf.Value
import Calf.Value.Closed as ●
open import Calf.Computation
open import Calf.Computation.Open as ◯ᶜ
open import Calf.Computation.Closed as ●ᶜ
open import Calf.Computation.Glue
open import Calf.Computation.Abstraction
open import Calf.Computation.Credit

open import Cubical.HITs.SetTruncation

open import Calf.Computation.Tensor.Base
open import Calf.Computation.Tensor.Abstract


A⊗▷B≡▷[A⊗B] : ∀ c → (A ⊗ (▷[ c ] B)) ≡ (▷[ c ] (A ⊗ B))
A⊗▷B≡▷[A⊗B] {A} {B} c = 𝒞-fracture-≡ lemma• lemma◦ lemmaα
  where
    lemma• : ●ᶜ (A ⊗ (▷[ c ] B)) ≡ ●ᶜ (▷[ c ] (A ⊗ B))
    lemma• =
        ●ᶜ (A ⊗ (▷[ c ] B))
      ≡⟨ ●ᶜ-⊗ ⟩
        ●ᶜ A ⊗ ●ᶜ (▷[ c ] B)
      ≡⟨ cong (●ᶜ A ⊗_) (▷-●ᶜ c B) ⟩
        ●ᶜ A ⊗ ●ᶜ B
      ≡⟨ sym ●ᶜ-⊗ ⟩
        ●ᶜ (A ⊗ B)
      ≡⟨ sym (▷-●ᶜ c (A ⊗ B)) ⟩
        ●ᶜ (▷[ c ] (A ⊗ B))
      ∎

    lemma◦ : ◯ᶜ (A ⊗ (▷[ c ] B)) ≡ ◯ᶜ (▷[ c ] (A ⊗ B))
    lemma◦ =
      transport (sym (◯ᶜ-lex (A ⊗ (▷[ c ] B)) (▷[ c ] (A ⊗ B)))) λ abs →
      cong (A ⊗_) (▷-open abs c B) ∙ sym (▷-open abs c (A ⊗ B))

    lemmaα :
      PathP (λ i → lemma• i ⊸ ●ᶜ (lemma◦ i))
        (●ᶜ.map (η◦ᶜ {A = A ⊗ (▷[ c ] B)}))
        (●ᶜ.map (η◦ᶜ {A = ▷[ c ] (A ⊗ B)}))
    lemmaα =
      ⊸-path lemma• (cong ●ᶜ lemma◦)
        {f₀ = ●ᶜ.map (η◦ᶜ {A = A ⊗ (▷[ c ] B)})}
        {f₁ = ●ᶜ.map (η◦ᶜ {A = ▷[ c ] (A ⊗ B)})}
        {!   !}
