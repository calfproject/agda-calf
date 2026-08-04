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

open 𝒞-FRAC

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
  ≡⟨ refl ⟩
    Abstractionᶜ A A (CHARGE (c₁ +ℂ c₂))
  ≡⟨ cong (Abstractionᶜ A A) (CHARGE-+ c₁ c₂) ⟩
    Abstractionᶜ A A (CHARGE c₂ ⨾ᶜ CHARGE c₁)
  ≡⟨ sym Abstractionᶜ-Abstractionᶜ ⟩
    Abstractionᶜ
      (Abstractionᶜ A A (CHARGE c₂))
      (Abstractionᶜ A A (CHARGE c₂))
      (squareᶜ' (CHARGE c₁) (CHARGE c₁) (λ a → cong ((_$ a) ∘ U) (CHARGE-comm {A} c₁ c₂)))
  ≡⟨ cong (Abstractionᶜ _ _) (squareᶜ'-charge (λ a → cong ((_$ a) ∘ U) (CHARGE-comm {A} c₁ c₂))) ⟩
    Abstractionᶜ (Abstractionᶜ A A (CHARGE c₂)) (Abstractionᶜ A A (CHARGE c₂)) (CHARGE c₁)
  ≡⟨ refl ⟩
    ▷[ c₁ ] (▷[ c₂ ] A)
  ∎

▷-FRAC : ℂ → 𝒞 → 𝒞-FRAC
▷-FRAC c A .A• = ●ᶜ• A
▷-FRAC c A .A◦ = ◯ᶜ◦ A
▷-FRAC c A .α• = ●ᶜ.map (CHARGE c ⨾ᶜ η◦ᶜ)

▷-FRAC-open : ⟨ ABS ⟩ → (c : ℂ) (A : 𝒞) → ▷-FRAC c A ≡ 𝒞-toFRAC A
▷-FRAC-open abs c A i .A• = 𝒞-toFRAC A .A•
▷-FRAC-open abs c A i .A◦ = 𝒞-toFRAC A .A◦
▷-FRAC-open abs c A i .α• =
  ●ᶜ.map-open abs
    (CHARGE c ⨾ᶜ η◦ᶜ)
    η◦ᶜ
    i

opaque
  unfolding Abstractionᶜ

  ▷-open : ⟨ ABS ⟩ → (c : ℂ) (A : 𝒞) → ▷[ c ] A ≡ A
  ▷-open abs c A = cong 𝒞-fromFRAC (▷-FRAC-open abs c A) ∙ 𝒞-glue-fracture-retract A

  ▷-●ᶜ : (c : ℂ) (A : 𝒞) → ●ᶜ (▷[ c ] A) ≡ ●ᶜ A
  ▷-●ᶜ c A = cong (fst ∘ 𝒞-FRAC.A•) (𝒞-glue-fracture-section (▷-FRAC c A))

  ▷-◯ᶜ : (c : ℂ) (A : 𝒞) → ◯ᶜ (▷[ c ] A) ≡ ◯ᶜ A
  ▷-◯ᶜ c A = cong (fst ∘ 𝒞-FRAC.A◦) (𝒞-glue-fracture-section (▷-FRAC c A))

  transport-▷ : (c : ℂ) (A : 𝒞) (q : U (●ᶜ A)) →
          ●ᶜ.map (η◦ᶜ {A = ▷[ c ] A}) .U
            (transport (cong U (sym (▷-●ᶜ c A))) q)
          ≡ transport (cong (λ C → U (●ᶜ C)) (sym (▷-◯ᶜ c A)))
              ((▷-FRAC c A .𝒞-FRAC.α•) .U q)
  transport-▷ c A q =
    fromPathP⁻ $
      congP₂$
        (λ i → 𝒞-glue-fracture-section (▷-FRAC c A) i .𝒞-FRAC.α• .U)
        (λ i → transport⁻-fillerExt⁻ (cong U (▷-●ᶜ c A)) i q)

save : (c : ℂ) → A ⊸ ▷[ c ] A
save {A} c = triangle' idᶜ

spend : (c : ℂ) → ▷[ c ] A ⊸ A
spend {A} c = triangle idᶜ

spend⨾save≡charge : ∀ {A} {c} → save c ⨾ᶜ spend c ≡ CHARGE {A} c
spend⨾save≡charge {A} {c} =
    save c ⨾ᶜ spend c
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
    SQ₁ = squareᶜ' idᶜ (idᶜ ⨾ᶜ CHARGE c) (λ _ → refl)

    SQ₂ : ▷ ⊸ Abstractionᶜ A A idᶜ
    SQ₂ = squareᶜ' (CHARGE c ⨾ᶜ idᶜ) idᶜ (λ _ → refl)

    save-path : PathP (λ i → Abstractionᶜ-id {A} i ⊸ ▷) SQ₁ (save c)
    save-path = transport-filler (λ i → Abstractionᶜ-id {A} i ⊸ ▷) SQ₁

    spend-path : PathP (λ i → ▷ ⊸ Abstractionᶜ-id {A} i) SQ₂ (spend c)
    spend-path = transport-filler (λ i → ▷ ⊸ Abstractionᶜ-id {A} i) SQ₂

    lemma : SQ₁ ⨾ᶜ SQ₂ ≡ CHARGE {Abstractionᶜ A A idᶜ} c
    lemma =
        squareᶜ'-⨾ᶜ idᶜ (idᶜ ⨾ᶜ CHARGE c) (λ _ → refl) (CHARGE c ⨾ᶜ idᶜ) idᶜ (λ _ → refl)
      ∙ squareᶜ'-≡
          (idᶜ⨾ᶜf≡f (CHARGE c ⨾ᶜ idᶜ) ∙ f⨾ᶜidᶜ≡f (CHARGE c))
          (f⨾ᶜidᶜ≡f (idᶜ ⨾ᶜ CHARGE c) ∙ idᶜ⨾ᶜf≡f (CHARGE c))
      ∙ squareᶜ'-charge (λ _ → refl)
