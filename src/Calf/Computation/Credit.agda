open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Univalence using (ua)
open import Cubical.Foundations.Path using (fromPathP⁻)
open import Cubical.Foundations.Transport using (transport⁻-fillerExt⁻)
open import Cubical.Data.Sigma

module Calf.Computation.Credit where

open import Calf.Core.Abstract
open import Calf.Core.Cost
open import Calf.Value
open import Calf.Value.Closed as ●
open import Calf.Computation
open import Calf.Computation.Open as ◯ᶜ
open import Calf.Computation.Closed as ●ᶜ
open import Calf.Computation.Glue
open import Calf.Computation.Abstraction

open 𝒞-FRACTURE

opaque
  ▷[_]_ : ℂ → 𝒞 → 𝒞
  ▷[ c ] A = Abstractionᶜ A A (CHARGE c)

  ▷-map : (A ⊸ B) → (▷[ c ] A ⊸ ▷[ c ] B)
  ▷-map {A} {B} {c} f =
    squareᶜ' (CHARGE c) (CHARGE c)
      f
      f
      (sym ∘ f .charge c)

  ▷/0 : ▷[ 0ℂ ] A ≡ A
  ▷/0 {A} = cong (Abstractionᶜ A A) CHARGE-0 ∙ Abstractionᶜ-id A

  ▷/+ : ▷[ c₁ +ℂ c₂ ] A ≡ ▷[ c₁ ] ▷[ c₂ ] A
  ▷/+ {c₁} {c₂} {A} =
      ▷[ c₁ +ℂ c₂ ] A
    ≡⟨⟩
      Abstractionᶜ A A (CHARGE (c₁ +ℂ c₂))
    ≡⟨ cong (Abstractionᶜ A A) (CHARGE-+ c₁ c₂) ⟩
      Abstractionᶜ A A (CHARGE c₂ ⨾ᶜ CHARGE c₁)
    ≡⟨ sym
        (Abstractionᶜ-Abstractionᶜ
          (CHARGE c₂) (CHARGE c₂)
          (CHARGE c₁) (CHARGE c₁)
          (λ a → cong ((_$ a) ∘ U) (CHARGE-comm {A} c₁ c₂)))
    ⟩
      Abstractionᶜ
        (Abstractionᶜ A A (CHARGE c₂))
        (Abstractionᶜ A A (CHARGE c₂))
        (squareᶜ' (CHARGE c₂) (CHARGE c₂) (CHARGE c₁) (CHARGE c₁) λ a → cong ((_$ a) ∘ U) (CHARGE-comm {A} c₁ c₂))
    ≡⟨
      cong
        (Abstractionᶜ (Abstractionᶜ A A (CHARGE c₂)) (Abstractionᶜ A A (CHARGE c₂)))
        (squareᶜ'-charge (CHARGE c₂) c₁ λ a → cong ((_$ a) ∘ U) (CHARGE-comm {A} c₁ c₂))
    ⟩
      Abstractionᶜ (Abstractionᶜ A A (CHARGE c₂)) (Abstractionᶜ A A (CHARGE c₂)) (CHARGE c₁)
    ≡⟨⟩
      ▷[ c₁ ] (▷[ c₂ ] A)
    ∎

  ▷-FRAC : ℂ → 𝒞 → 𝒞-FRACTURE
  ▷-FRAC c A .A• = ●ᶜ• A
  ▷-FRAC c A .A◦ = ◯ᶜ◦ A
  ▷-FRAC c A .α• = ●ᶜ.map (CHARGE c ⨾ᶜ η◦ᶜ)

  ▷-open : ⟨ ABS ⟩ → (c : ℂ) (A : 𝒞) → ▷[ c ] A ≡ A
  ▷-open abs c A = ◯[Abstractionᶜ≡A-abs] (CHARGE c) abs

  ▷-●ᶜ : (c : ℂ) (A : 𝒞) → ●ᶜ (▷[ c ] A) ≡ ●ᶜ A
  ▷-●ᶜ c A = ●ᶜ-Abstractionᶜ (CHARGE c)

  ▷-◯ᶜ : (c : ℂ) (A : 𝒞) → ◯ᶜ (▷[ c ] A) ≡ ◯ᶜ A
  ▷-◯ᶜ c A = ◯ᶜ-Abstractionᶜ (CHARGE c)

  ▷-coherence : (c : ℂ) (A : 𝒞) →
    PathP
      (λ i → sym (▷-●ᶜ c A) i ⊸ ●ᶜ (sym (▷-◯ᶜ c A) i))
      (●ᶜ.map (CHARGE c ⨾ᶜ η◦ᶜ {A = A}))
      (●ᶜ.map (η◦ᶜ {A = ▷[ c ] A}))
  ▷-coherence c A =
    Abstractionᶜ-coherence (CHARGE c)

  save : (A : 𝒞) (c : ℂ) → A ⊸ ▷[ c ] A
  save A c = triangle' (CHARGE c) idᶜ

  spend : (A : 𝒞) (c : ℂ) → ▷[ c ] A ⊸ A
  spend A c = triangle idᶜ

  save⨾spend≡charge : (A : 𝒞) (c : ℂ) → save A c ⨾ᶜ spend A c ≡ CHARGE c
  save⨾spend≡charge A c =
      save A c ⨾ᶜ spend A c
    ≡⟨ cong (_⨾ᶜ spend A c) (idᶜ⨾ᶜf≡f (triangle-Uᶜ (CHARGE c))) ⟩
      triangle-Uᶜ (CHARGE c) ⨾ᶜ spend A c
    ≡⟨ sym (fromPathP (λ i → triangle-Uᶜ (CHARGE c) ⨾ᶜ spend-path i)) ⟩
      transport (λ i → A ⊸ Abstractionᶜ-id A i) (triangle-Uᶜ (CHARGE c) ⨾ᶜ SQ₂)
    ≡⟨ cong (transport (λ i → A ⊸ Abstractionᶜ-id A i)) lemma ⟩
      transport (λ i → A ⊸ Abstractionᶜ-id A i) (CHARGE c ⨾ᶜ triangle-Uᶜ idᶜ)
    ≡⟨ fromPathP (λ i → CHARGE {A} c ⨾ᶜ triangle-Uᶜ-id i) ⟩
      CHARGE c ⨾ᶜ idᶜ
    ≡⟨ f⨾ᶜidᶜ≡f (CHARGE c) ⟩
      CHARGE c
    ∎
    where
      SQ₂ : Abstractionᶜ A A (CHARGE c) ⊸ Abstractionᶜ A A idᶜ
      SQ₂ = squareᶜ' (CHARGE c) idᶜ (CHARGE c ⨾ᶜ idᶜ) idᶜ (λ _ → refl)

      spend-path : PathP (λ i → Abstractionᶜ A A (CHARGE c) ⊸ Abstractionᶜ-id A i) SQ₂ (spend A c)
      spend-path = transport-filler (λ i → Abstractionᶜ A A (CHARGE c) ⊸ Abstractionᶜ-id A i) SQ₂

      lemma : triangle-Uᶜ (CHARGE c) ⨾ᶜ SQ₂ ≡ CHARGE c ⨾ᶜ triangle-Uᶜ idᶜ
      lemma =
          triangle-Uᶜ-natural (CHARGE c ⨾ᶜ idᶜ) idᶜ (λ _ → refl)
        ∙ cong (_⨾ᶜ triangle-Uᶜ idᶜ) (f⨾ᶜidᶜ≡f (CHARGE c))
