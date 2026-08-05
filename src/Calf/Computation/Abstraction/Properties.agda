module Calf.Computation.Abstraction.Properties where

open import Cubical.Foundations.Univalence using (ua; ua→)

open import Calf.Value
import Calf.Value.Open as ◯
import Calf.Value.Closed as ●
open import Calf.Computation
open import Calf.Computation.Open as ◯ᶜ
open import Calf.Computation.Closed as ●ᶜ
open import Calf.Computation.Glue as Glueᶜ hiding (squareᶜ)
open 𝒞-FRAC

open import Calf.Computation.Abstraction.Base

opaque
  unfolding Abstractionᶜ

  ●ᶜ-Abstractionᶜ : ∀ {A-⊤ A-abs α} → ●ᶜ (Abstractionᶜ A-⊤ A-abs α) ≡ ●ᶜ A-⊤
  ●ᶜ-Abstractionᶜ {A-⊤} {A-abs} {α} =
    cong ⟨_⟩ᶜ (𝒞-glue•-path (Abstractionᶜ-FRAC A-⊤ A-abs α))

  ◯ᶜ-Abstractionᶜ : ∀ {A-⊤ A-abs α} → ◯ᶜ (Abstractionᶜ A-⊤ A-abs α) ≡ ◯ᶜ A-abs
  ◯ᶜ-Abstractionᶜ {A-⊤} {A-abs} {α} =
    cong ⟨_⟩ᶜ (𝒞-glue◦-path (Abstractionᶜ-FRAC A-⊤ A-abs α))

  squareᶜ'-charge
    : ∀ {A-⊤ A-abs α c}
    → (α-charge : (a : U A-⊤) → α .U (A-⊤ .charge c a) ≡ A-abs .charge c (α .U a))
    → squareᶜ'
        (CHARGE c) (CHARGE c)
        α-charge
      ≡ CHARGE {A = Abstractionᶜ A-⊤ A-abs α} c
  squareᶜ'-charge {A-⊤} {A-abs} {α} {c} α-charge =
    ⊸-path
      refl refl
      (funExt λ q → λ i → record
        { • = ●ᶜ-map-CHARGE c (q .•) i
        ; ◦ = λ p → A-abs .charge c (q .◦ p)
        ; •→◦ =
            isProp→PathP
              (λ i → ●ᶜ (◯ᶜ A-abs) .is-set
                (●ᶜ.map (α ⨾ᶜ η◦ᶜ) .U
                  (●ᶜ-map-CHARGE {A = A-⊤} c (q .•) i))
                (η• (λ p → A-abs .charge c (q .◦ p))))
              (squareᶜ'
                {A-⊤ = A-⊤} {A-abs = A-abs} {α = α}
                {B-⊤ = A-⊤} {B-abs = A-abs} {β = α}
                (CHARGE c) (CHARGE c)
                α-charge
                .U q .•→◦)
              (Abstractionᶜ A-⊤ A-abs α .charge c q .•→◦)
              i
        })

  squareᶜ'-⨾ᶜ : ∀ {A-⊤ A-abs α B-⊤ B-abs β C-⊤ C-abs γ}
    (f-⊤ : A-⊤ ⊸ B-⊤) (f-abs : A-abs ⊸ B-abs)
    (fc : (a : U A-⊤) → β .U (f-⊤ .U a) ≡ f-abs .U (α .U a))
    (g-⊤ : B-⊤ ⊸ C-⊤) (g-abs : B-abs ⊸ C-abs)
    (gc : (b : U B-⊤) → γ .U (g-⊤ .U b) ≡ g-abs .U (β .U b))
    → squareᶜ' {α = α} {β = β} f-⊤ f-abs fc ⨾ᶜ squareᶜ' {α = β} {β = γ} g-⊤ g-abs gc
      ≡ squareᶜ' {α = α} {β = γ} (f-⊤ ⨾ᶜ g-⊤) (f-abs ⨾ᶜ g-abs)
          (λ a → gc (f-⊤ .U a) ∙ cong (g-abs .U) (fc a))
  squareᶜ'-⨾ᶜ {A-⊤ = A-⊤} {A-abs = A-abs} {α = α} {β = β} {C-abs = C-abs} {γ = γ}
              f-⊤ f-abs fc g-⊤ g-abs gc =
    ⊸-path refl refl (funExt sq)
    where
      sq : (q : U (Abstractionᶜ A-⊤ A-abs α))
        → (squareᶜ' {α = α} {β = β} f-⊤ f-abs fc ⨾ᶜ squareᶜ' {α = β} {β = γ} g-⊤ g-abs gc) .U q
          ≡ squareᶜ' {α = α} {β = γ} (f-⊤ ⨾ᶜ g-⊤) (f-abs ⨾ᶜ g-abs)
              (λ a → gc (f-⊤ .U a) ∙ cong (g-abs .U) (fc a)) .U q
      sq q i .• = ●ᶜ.map-∘ f-⊤ g-⊤ i .U (q .•)
      sq q i .◦ = ◯ᶜ.map-∘ f-abs g-abs i .U (q .◦)
      sq q i .•→◦ =
        isProp→PathP
          (λ i → (●ᶜ (◯ᶜ C-abs)) .is-set
            (●ᶜ.map (γ ⨾ᶜ η◦ᶜ {A = C-abs}) .U (sq q i .•))
            (η• (sq q i .◦)))
          ((squareᶜ' {α = α} {β = β} f-⊤ f-abs fc ⨾ᶜ squareᶜ' {α = β} {β = γ} g-⊤ g-abs gc) .U q .•→◦)
          (squareᶜ' {α = α} {β = γ} (f-⊤ ⨾ᶜ g-⊤) (f-abs ⨾ᶜ g-abs)
            (λ a → gc (f-⊤ .U a) ∙ cong (g-abs .U) (fc a)) .U q .•→◦)
          i

  squareᶜ'-≡ : ∀ {A-⊤ A-abs α B-⊤ B-abs β}
    {f-⊤ f-⊤' : A-⊤ ⊸ B-⊤} {f-abs f-abs' : A-abs ⊸ B-abs}
    {fc : (a : U A-⊤) → β .U (f-⊤ .U a) ≡ f-abs .U (α .U a)}
    {fc' : (a : U A-⊤) → β .U (f-⊤' .U a) ≡ f-abs' .U (α .U a)}
    → f-⊤ ≡ f-⊤' → f-abs ≡ f-abs'
    → squareᶜ' {α = α} {β = β} f-⊤ f-abs fc ≡ squareᶜ' f-⊤' f-abs' fc'
  squareᶜ'-≡ {α = α} {B-abs = B-abs} {β = β} {fc = fc} {fc' = fc'} p q i =
    squareᶜ' (p i) (q i)
      (isProp→PathP
        (λ i u v → funExt λ a → B-abs .is-set (β .U (p i .U a)) (q i .U (α .U a)) (u a) (v a))
        fc fc' i)

  square-glue•-out
    : ∀ {A-⊤ A-abs α B-⊤ B-abs β f-⊤ f-abs f-coherence}
    → (q• : U (●ᶜ (𝒞-fromFRAC (Abstractionᶜ-FRAC A-⊤ A-abs α))))
    → glue•-out (U-FRACTURE (Abstractionᶜ-FRAC B-⊤ B-abs β))
        (●ᶜ.map (squareᶜ'-FRAC {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} f-⊤ f-abs f-coherence) .U q•)
    ≡ ●ᶜ.map f-⊤ .U
        (glue•-out (U-FRACTURE (Abstractionᶜ-FRAC A-⊤ A-abs α)) q•)
  square-glue•-out {B-⊤ = B-⊤} {f-⊤ = f-⊤} =
    ●.elim (λ _ → ●.isModal≡ isModal●) (λ g → refl)

  Abstractionᶜ-Abstractionᶜ-α•-path
    : ∀ {A-⊤ A-abs α B-⊤ B-abs β f-⊤ f-abs f-coherence}
    → PathP
        (λ i →
          ⟨ 𝒞-glue•-path (Abstractionᶜ-FRAC A-⊤ A-abs α) i ⟩ᶜ
            ⊸ ●ᶜ ⟨ 𝒞-glue◦-path (Abstractionᶜ-FRAC B-⊤ B-abs β) i ⟩ᶜ)
        (●ᶜ.map
          (squareᶜ'-FRAC {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} f-⊤ f-abs f-coherence
            ⨾ᶜ η◦ᶜ {A = 𝒞-fromFRAC (Abstractionᶜ-FRAC B-⊤ B-abs β)}))
        (●ᶜ.map ((α ⨾ᶜ f-abs) ⨾ᶜ η◦ᶜ {A = B-abs}))
  Abstractionᶜ-Abstractionᶜ-α•-path {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} {f-⊤} {f-abs} {f-coherence} =
    ⊸-path
      (λ i → ⟨ 𝒞-glue•-path (Abstractionᶜ-FRAC A-⊤ A-abs α) i ⟩ᶜ)
      (λ i → ●ᶜ ⟨ 𝒞-glue◦-path (Abstractionᶜ-FRAC B-⊤ B-abs β) i ⟩ᶜ)
      (ua→
        {e = glue•-equiv 𝒱A}
        {B = λ i → ● (ua (glue◦-equiv 𝒱B) i)}
        λ q• → toPathP
          (  transport (λ i → ● (ua (glue◦-equiv 𝒱B) i))
              (●.map ((sqF ⨾ᶜ η◦ᶜ) .U) q•)
           ≡⟨ cong (transport (λ i → ● (ua (glue◦-equiv 𝒱B) i)))
                (sym (●.map-∘ (sqF .U) η◦ q•)) ⟩
             transport (λ i → ● (ua (glue◦-equiv 𝒱B) i))
              (●.map η◦ (●.map (sqF .U) q•))
           ≡⟨ fromPathP (glue-χ-path 𝒱B (●.map (sqF .U) q•)) ⟩
             𝒱-FRACTURE.χ• 𝒱B (glue•-out 𝒱B (●.map (sqF .U) q•))
           ≡⟨ cong (𝒱-FRACTURE.χ• 𝒱B)
                (square-glue•-out
                  {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} {f-⊤} {f-abs} {f-coherence}
                  q•) ⟩
             𝒱-FRACTURE.χ• 𝒱B (●ᶜ.map f-⊤ .U (glue•-out 𝒱A q•))
           ≡⟨ ●.map-∘ (f-⊤ .U) ((β ⨾ᶜ η◦ᶜ) .U) (glue•-out 𝒱A q•) ⟩
             ●.map ((β ⨾ᶜ η◦ᶜ) .U ∘ f-⊤ .U) (glue•-out 𝒱A q•)
           ≡⟨ cong (λ h → ●.map h (glue•-out 𝒱A q•))
                (funExt λ a → cong η◦ (f-coherence a)) ⟩
             ●.map (((α ⨾ᶜ f-abs) ⨾ᶜ η◦ᶜ) .U) (glue•-out 𝒱A q•)
           ∎))
    where
      𝒱A 𝒱B : 𝒱-FRACTURE
      𝒱A = U-FRACTURE (Abstractionᶜ-FRAC A-⊤ A-abs α)
      𝒱B = U-FRACTURE (Abstractionᶜ-FRAC B-⊤ B-abs β)

      sqF : 𝒞-fromFRAC (Abstractionᶜ-FRAC A-⊤ A-abs α)
          ⊸ 𝒞-fromFRAC (Abstractionᶜ-FRAC B-⊤ B-abs β)
      sqF = squareᶜ'-FRAC {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} f-⊤ f-abs f-coherence

  Abstractionᶜ-Abstractionᶜ-FRAC
    : ∀ {A-⊤ A-abs α B-⊤ B-abs β f-⊤ f-abs f-coherence}
    → Abstractionᶜ-FRAC
        (𝒞-fromFRAC (Abstractionᶜ-FRAC A-⊤ A-abs α))
        (𝒞-fromFRAC (Abstractionᶜ-FRAC B-⊤ B-abs β))
        (squareᶜ'-FRAC {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} f-⊤ f-abs f-coherence)
      ≡ Abstractionᶜ-FRAC A-⊤ B-abs (α ⨾ᶜ f-abs)
  Abstractionᶜ-Abstractionᶜ-FRAC {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} {f-⊤} {f-abs} {f-coherence} =
    𝒞-FRAC-path
      (𝒞-glue•-path (Abstractionᶜ-FRAC A-⊤ A-abs α))
      (𝒞-glue◦-path (Abstractionᶜ-FRAC B-⊤ B-abs β))
      (Abstractionᶜ-Abstractionᶜ-α•-path
        {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} {f-⊤} {f-abs} {f-coherence})

  Abstractionᶜ-Abstractionᶜ : ∀ {A-⊤ A-abs α B-⊤ B-abs β f-⊤ f-abs f-coherence} →
    Abstractionᶜ (Abstractionᶜ A-⊤ A-abs α) (Abstractionᶜ B-⊤ B-abs β) (squareᶜ' {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} f-⊤ f-abs f-coherence)
    ≡ Abstractionᶜ A-⊤ B-abs (α ⨾ᶜ f-abs)
  Abstractionᶜ-Abstractionᶜ {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} {f-⊤} {f-abs} {f-coherence} =
    cong 𝒞-fromFRAC
      (Abstractionᶜ-Abstractionᶜ-FRAC
        {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} {f-⊤} {f-abs} {f-coherence})
