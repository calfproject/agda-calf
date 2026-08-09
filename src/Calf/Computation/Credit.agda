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

▷[_]_ : ℂ → 𝒞 → 𝒞
▷[ c ] A = Abstractionᶜ A A (CHARGE c)

▷-map : (A ⊸ B) → (▷[ c ] A ⊸ ▷[ c ] B)
▷-map {A} {B} {c} f =
  squareᶜ'
    {A-⊤ = A} {A-abs = A} {α = CHARGE c}
    {B-⊤ = B} {B-abs = B} {β = CHARGE c}
    f
    f
    (sym ∘ f .charge c)

▷/0 : ▷[ 0ℂ ] A ≡ A
▷/0 {A} = cong (Abstractionᶜ A A) CHARGE-0 ∙ Abstractionᶜ-id

▷/+ : ▷[ c₁ +ℂ c₂ ] A ≡ ▷[ c₁ ] ▷[ c₂ ] A
▷/+ {c₁} {c₂} {A} =
    ▷[ c₁ +ℂ c₂ ] A
  ≡⟨⟩
    Abstractionᶜ A A (CHARGE (c₁ +ℂ c₂))
  ≡⟨ cong (Abstractionᶜ A A) (CHARGE-+ c₁ c₂) ⟩
    Abstractionᶜ A A (CHARGE c₂ ⨾ᶜ CHARGE c₁)
  ≡⟨ sym
      (Abstractionᶜ-Abstractionᶜ
        {A} {A} {CHARGE c₂}
        {A} {A} {CHARGE c₂}
        {CHARGE c₁} {CHARGE c₁} {λ a → cong ((_$ a) ∘ U) (CHARGE-comm {A} c₁ c₂)})
  ⟩
    Abstractionᶜ
      (Abstractionᶜ A A (CHARGE c₂))
      (Abstractionᶜ A A (CHARGE c₂))
      (squareᶜ' {A} {A} {CHARGE c₂} {A} {A} {CHARGE c₂} (CHARGE c₁) (CHARGE c₁) λ a → cong ((_$ a) ∘ U) (CHARGE-comm {A} c₁ c₂))
  ≡⟨
    cong
      (Abstractionᶜ (Abstractionᶜ A A (CHARGE c₂)) (Abstractionᶜ A A (CHARGE c₂)))
      (squareᶜ'-charge {A} {A} {CHARGE c₂} {c₁} λ a → cong ((_$ a) ∘ U) (CHARGE-comm {A} c₁ c₂))
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
▷-open abs c A = ◯[Abstractionᶜ≡A-abs] abs

▷-●ᶜ : (c : ℂ) (A : 𝒞) → ●ᶜ (▷[ c ] A) ≡ ●ᶜ A
▷-●ᶜ c A = ●ᶜ-Abstractionᶜ {A} {A} {CHARGE c}

▷-◯ᶜ : (c : ℂ) (A : 𝒞) → ◯ᶜ (▷[ c ] A) ≡ ◯ᶜ A
▷-◯ᶜ c A = ◯ᶜ-Abstractionᶜ {A} {A} {CHARGE c}

save : (A : 𝒞) (c : ℂ) → A ⊸ ▷[ c ] A
save A c = triangle' {B-abs = A} idᶜ

spend : (A : 𝒞) (c : ℂ) → ▷[ c ] A ⊸ A
spend A c = triangle idᶜ

save⨾spend≡charge : (A : 𝒞) (c : ℂ) → save A c ⨾ᶜ spend A c ≡ CHARGE {A} c
save⨾spend≡charge A c =
    save A c ⨾ᶜ spend A c
  ≡⟨ {! refl  !} ⟩
    {!   !}
  ≡⟨ sym (fromPathP (λ i → save-path i ⨾ᶜ spend-path i)) ⟩
    transport (λ i → Abstractionᶜ-id {A} i ⊸ Abstractionᶜ-id {A} i) (SQ₁ ⨾ᶜ SQ₂)
  ≡⟨ cong (transport (λ i → Abstractionᶜ-id {A} i ⊸ Abstractionᶜ-id {A} i)) lemma ⟩
    transport (λ i → Abstractionᶜ-id {A} i ⊸ Abstractionᶜ-id {A} i) (CHARGE {Abstractionᶜ A A idᶜ} c)
  ≡⟨ fromPathP (λ i → CHARGE {Abstractionᶜ-id {A} i} c) ⟩
    CHARGE {A} c
  ∎
  where
    ▷ : 𝒞
    ▷ = Abstractionᶜ A A (CHARGE c)

    SQ₁ : Abstractionᶜ A A idᶜ ⊸ ▷
    SQ₁ = squareᶜ' {A} {A} {idᶜ} {A} {A} {CHARGE c} idᶜ (idᶜ ⨾ᶜ CHARGE c) (λ _ → refl)

    SQ₂ : ▷ ⊸ Abstractionᶜ A A idᶜ
    SQ₂ = squareᶜ' {A} {A} {CHARGE c} {A} {A} {idᶜ} (CHARGE c ⨾ᶜ idᶜ) idᶜ (λ _ → refl)

    save-path : PathP (λ i → Abstractionᶜ-id {A} i ⊸ ▷) SQ₁ (save A c)
    save-path = transport-filler (λ i → Abstractionᶜ-id {A} i ⊸ ▷) SQ₁

    spend-path : PathP (λ i → ▷ ⊸ Abstractionᶜ-id {A} i) SQ₂ (spend A c)
    spend-path = transport-filler (λ i → ▷ ⊸ Abstractionᶜ-id {A} i) SQ₂

    lemma : SQ₁ ⨾ᶜ SQ₂ ≡ CHARGE {Abstractionᶜ A A idᶜ} c
    lemma =
        squareᶜ'-⨾ᶜ idᶜ (idᶜ ⨾ᶜ CHARGE {A} c) (λ _ → refl) (CHARGE {A} c ⨾ᶜ idᶜ) idᶜ (λ _ → refl)
      ∙ squareᶜ'-≡
          (idᶜ⨾ᶜf≡f (CHARGE {A} c ⨾ᶜ idᶜ) ∙ f⨾ᶜidᶜ≡f (CHARGE {A} c))
          (f⨾ᶜidᶜ≡f (idᶜ ⨾ᶜ CHARGE {A} c) ∙ idᶜ⨾ᶜf≡f (CHARGE {A} c))
      ∙ squareᶜ'-charge (λ _ → refl)
