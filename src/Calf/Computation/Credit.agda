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
open import Calf.Value.Closed as ●ᵛ
open import Calf.Computation
open import Calf.Computation.Open as ◯ᶜ
open import Calf.Computation.Closed as ●ᶜ
open import Calf.Computation.Glue
open import Calf.Computation.Abstraction

open 𝒞-FRAC

▷'[_]_ : val ℂ → 𝒞 → 𝒞
▷'[ c ] A = Abstractionᶜ A A (CHARGE c)

▷'/0 : ▷'[ 0ℂ ] A ≡ A
▷'/0 {A} = cong (Abstractionᶜ A A) CHARGE-0 ∙ Abstractionᶜ-id

▷'/+ : ▷'[ c₁ +ℂ c₂ ] A ≡ ▷'[ c₁ ] ▷'[ c₂ ] A
▷'/+ {c₁} {c₂} {A} =
    ▷'[ c₁ +ℂ c₂ ] A
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
    ▷'[ c₁ ] (▷'[ c₂ ] A)
  ∎

▷'-FRAC : val ℂ → 𝒞 → 𝒞-FRAC
▷'-FRAC c A .A• = ●ᶜ A , ●ᶜ.η-isEquiv
▷'-FRAC c A .A◦ = ◯ᶜ A , ◯ᶜ.η-isEquiv
▷'-FRAC c A .α• = ●ᶜ.map (CHARGE c ⨾ᶜ η◦ᶜ)

▷'-FRAC-open : ⟨ ABS ⟩ → (c : val ℂ) (A : 𝒞) → ▷'-FRAC c A ≡ 𝒞-toFRAC A
▷'-FRAC-open abs c A i .A• = 𝒞-toFRAC A .A•
▷'-FRAC-open abs c A i .A◦ = 𝒞-toFRAC A .A◦
▷'-FRAC-open abs c A i .α• =
  ●ᶜ.map-open abs
    (CHARGE c ⨾ᶜ η◦ᶜ)
    η◦ᶜ
    i

opaque
  unfolding Abstractionᶜ

  ▷'-open : ⟨ ABS ⟩ → (c : val ℂ) (A : 𝒞) → ▷'[ c ] A ≡ A
  ▷'-open abs c A = cong 𝒞-fromFRAC (▷'-FRAC-open abs c A) ∙ 𝒞-glue-fracture-retract A

  ▷'-●ᶜ : (c : val ℂ) (A : 𝒞) → ●ᶜ (▷'[ c ] A) ≡ ●ᶜ A
  ▷'-●ᶜ c A = cong (fst ∘ 𝒞-FRAC.A•) (𝒞-glue-fracture-section (▷'-FRAC c A))

  ▷'-◯ᶜ : (c : val ℂ) (A : 𝒞) → ◯ᶜ (▷'[ c ] A) ≡ ◯ᶜ A
  ▷'-◯ᶜ c A = cong (fst ∘ 𝒞-FRAC.A◦) (𝒞-glue-fracture-section (▷'-FRAC c A))

  transport-▷' : (c : val ℂ) (A : 𝒞) (q : cmp (●ᶜ A)) →
          ●ᶜ.map (η◦ᶜ {A = ▷'[ c ] A}) .U
            (transport (cong cmp (sym (▷'-●ᶜ c A))) q)
          ≡ transport (cong (λ C → cmp (●ᶜ C)) (sym (▷'-◯ᶜ c A)))
              ((▷'-FRAC c A .𝒞-FRAC.α•) .U q)
  transport-▷' c A q =
          fromPathP⁻ $
            congP₂$
              (λ i → 𝒞-glue-fracture-section (▷'-FRAC c A) i .𝒞-FRAC.α• .U)
              (λ i → transport⁻-fillerExt⁻ (cong cmp (▷'-●ᶜ c A)) i q)

store' : ∀ {c A} → A ⊸ ▷'[ c ] A
store' {c} {A} =
  subst (_⊸ ▷'[ c ] A) Abstractionᶜ-id $
  squareᶜ'
    {A-⊤ = A} {A-abs = A} {α = idᶜ}
    {B-⊤ = A} {B-abs = A} {β = CHARGE c}
    idᶜ
    (CHARGE c)
    (λ _ → refl)

spend : ▷'[ c ] A ⊸ A
spend {c} {A} =
  subst (▷'[ c ] A ⊸_) Abstractionᶜ-id $
  squareᶜ'
    {A-⊤ = A} {A-abs = A} {α = CHARGE c}
    {B-⊤ = A} {B-abs = A} {β = idᶜ}
    (CHARGE c)
    idᶜ
    (λ _ → refl)

▷'-map : (A ⊸ B) → (▷'[ c ] A ⊸ ▷'[ c ] B)
▷'-map {A} {B} {c} f =
  squareᶜ'
    {A-⊤ = A} {A-abs = A} {α = CHARGE c}
    {B-⊤ = B} {B-abs = B} {β = CHARGE c}
    f
    f
    (sym ∘ f .charge c)


ℙ : 𝒱
ℙ = ●ᵛ ℂ

-- variable
--   p q r s : val ℙ

▷[_] : val ℙ → 𝒞 → 𝒞
▷[ η• c ] A = ▷'[ c ] A
▷[ ∗ abs ] A = A
▷[ law c abs i ] A = ▷'-open abs c A i

store : ∀ {p A} → A ⊸ ▷[ p ] A
store {η• c} = store'
store {∗ abs} = idᶜ
store {law x abs i} = {!   !}
