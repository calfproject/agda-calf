module Calf.Computation.Abstraction.Properties where

open import Calf.Value
import Calf.Value.Open as ◯
import Calf.Value.Closed as ●
open import Calf.Computation
open import Calf.Computation.Open as ◯ᶜ
open import Calf.Computation.Closed as ●ᶜ
open import Calf.Computation.Glue as Glueᶜ hiding (squareᶜ)
open import Cubical.Foundations.Univalence using (ua→; ua-gluePath)
open import Cubical.Functions.Embedding
open 𝒞-FRAC

open import Calf.Computation.Abstraction.Base

opaque
  unfolding Abstractionᶜ

  ●ᶜ-Abstractionᶜ : ∀ {A-⊤ A-abs α} → ●ᶜ (Abstractionᶜ A-⊤ A-abs α) ≡ ●ᶜ A-⊤
  ●ᶜ-Abstractionᶜ = {!   !}

  ◯ᶜ-Abstractionᶜ : ∀ {A-⊤ A-abs α} → ◯ᶜ (Abstractionᶜ A-⊤ A-abs α) ≡ ◯ᶜ A-abs
  ◯ᶜ-Abstractionᶜ = {!   !}

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

  Abstractionᶜ-glue•-out-square
    : ∀ {A-⊤ A-abs α B-⊤ B-abs β f-⊤ f-abs f-coherence}
    → (q• : U (●ᶜ (𝒞-fromFRAC (Abstractionᶜ-FRAC A-⊤ A-abs α))))
    → glue•-out
        (𝒞-FRAC→𝒱-FRAC (Abstractionᶜ-FRAC B-⊤ B-abs β))
        (●ᶜ.map (squareᶜ'-FRAC {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} f-⊤ f-abs f-coherence) .U q•)
      ≡ ●ᶜ.map f-⊤ .U
        (glue•-out
          (𝒞-FRAC→𝒱-FRAC (Abstractionᶜ-FRAC A-⊤ A-abs α))
          q•)
  Abstractionᶜ-glue•-out-square {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} {f-⊤} {f-abs} {f-coherence} q• =
    isEmbedding→Inj
      (isEquiv→isEmbedding (Abstractionᶜ-FRAC B-⊤ B-abs β .A• .snd))
      (glue•-out
        (𝒞-FRAC→𝒱-FRAC (Abstractionᶜ-FRAC B-⊤ B-abs β))
        (●ᶜ.map (squareᶜ'-FRAC {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} f-⊤ f-abs f-coherence) .U q•))
      (●ᶜ.map f-⊤ .U
        (glue•-out
          (𝒞-FRAC→𝒱-FRAC (Abstractionᶜ-FRAC A-⊤ A-abs α))
          q•))
      (  η•
          (glue•-out
            (𝒞-FRAC→𝒱-FRAC (Abstractionᶜ-FRAC B-⊤ B-abs β))
            (●ᶜ.map (squareᶜ'-FRAC {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} f-⊤ f-abs f-coherence) .U q•))
       ≡⟨ secIsEq
          (Abstractionᶜ-FRAC B-⊤ B-abs β .A• .snd)
          (●ᶜ.map (proj•ᶜ (Abstractionᶜ-FRAC B-⊤ B-abs β)) .U
            (●ᶜ.map (squareᶜ'-FRAC {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} f-⊤ f-abs f-coherence) .U q•)) ⟩
         ●ᶜ.map (proj•ᶜ (Abstractionᶜ-FRAC B-⊤ B-abs β)) .U
           (●ᶜ.map (squareᶜ'-FRAC {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} f-⊤ f-abs f-coherence) .U q•)
       ≡⟨ ●.map-∘
          (squareᶜ'-FRAC {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} f-⊤ f-abs f-coherence .U)
          (proj•ᶜ (Abstractionᶜ-FRAC B-⊤ B-abs β) .U)
          q• ⟩
         ●.map (λ q → ●ᶜ.map f-⊤ .U (q .•)) q•
       ≡⟨ sym (●.map-∘
          (proj•ᶜ (Abstractionᶜ-FRAC A-⊤ A-abs α) .U)
          (●ᶜ.map f-⊤ .U)
          q•) ⟩
         ●ᶜ.map (●ᶜ.map f-⊤) .U
           (●ᶜ.map (proj•ᶜ (Abstractionᶜ-FRAC A-⊤ A-abs α)) .U q•)
       ≡⟨ cong (●.map (●ᶜ.map f-⊤ .U))
          (sym (secIsEq
            (Abstractionᶜ-FRAC A-⊤ A-abs α .A• .snd)
            (●ᶜ.map (proj•ᶜ (Abstractionᶜ-FRAC A-⊤ A-abs α)) .U q•))) ⟩
         η•
           (●ᶜ.map f-⊤ .U
             (glue•-out
               (𝒞-FRAC→𝒱-FRAC (Abstractionᶜ-FRAC A-⊤ A-abs α))
               q•))
       ∎)

  Abstractionᶜ-Abstractionᶜ-α•-path
    : ∀ {A-⊤ A-abs α B-⊤ B-abs β f-⊤ f-abs f-coherence}
    → PathP
        (λ i →
          𝒞-glue•-path (Abstractionᶜ-FRAC A-⊤ A-abs α) i .fst
            ⊸ ●ᶜ (𝒞-glue◦-path (Abstractionᶜ-FRAC B-⊤ B-abs β) i .fst))
        (●ᶜ.map
          (squareᶜ'-FRAC {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} f-⊤ f-abs f-coherence
            ⨾ᶜ η◦ᶜ {A = 𝒞-fromFRAC (Abstractionᶜ-FRAC B-⊤ B-abs β)}))
        (●ᶜ.map ((α ⨾ᶜ f-abs) ⨾ᶜ η◦ᶜ {A = B-abs}))
  Abstractionᶜ-Abstractionᶜ-α•-path {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} {f-⊤} {f-abs} {f-coherence} =
    ⊸-path
      (λ i → 𝒞-glue•-path (Abstractionᶜ-FRAC A-⊤ A-abs α) i .fst)
      (λ i → ●ᶜ (𝒞-glue◦-path (Abstractionᶜ-FRAC B-⊤ B-abs β) i .fst))
      (ua→
        {e = glue•-equiv (𝒞-FRAC→𝒱-FRAC (Abstractionᶜ-FRAC A-⊤ A-abs α))}
        λ q• →
          toPathP
            (  transport
                (λ i → U (●ᶜ (𝒞-glue◦-path (Abstractionᶜ-FRAC B-⊤ B-abs β) i .fst)))
                (●.map
                  (η◦ᶜ {A = 𝒞-fromFRAC (Abstractionᶜ-FRAC B-⊤ B-abs β)} .U
                    ∘ squareᶜ'-FRAC {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} f-⊤ f-abs f-coherence .U)
                  q•)
             ≡⟨ cong
                  (transport
                    (λ i → U (●ᶜ (𝒞-glue◦-path (Abstractionᶜ-FRAC B-⊤ B-abs β) i .fst))))
                  (sym (●.map-∘
                    (squareᶜ'-FRAC {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} f-⊤ f-abs f-coherence .U)
                    (η◦ᶜ {A = 𝒞-fromFRAC (Abstractionᶜ-FRAC B-⊤ B-abs β)} .U)
                    q•)) ⟩
               transport
                (λ i → U (●ᶜ (𝒞-glue◦-path (Abstractionᶜ-FRAC B-⊤ B-abs β) i .fst)))
                (●.map (η◦ᶜ {A = 𝒞-fromFRAC (Abstractionᶜ-FRAC B-⊤ B-abs β)} .U)
                  (●.map
                    (squareᶜ'-FRAC {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} f-⊤ f-abs f-coherence .U)
                    q•))
             ≡⟨ fromPathP
                (glue-χ-path-base
                  (𝒞-FRAC→𝒱-FRAC (Abstractionᶜ-FRAC B-⊤ B-abs β))
                  (●ᶜ.map (squareᶜ'-FRAC {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} f-⊤ f-abs f-coherence) .U q•)) ⟩
               Abstractionᶜ-FRAC B-⊤ B-abs β .α• .U
                (glue•-out
                  (𝒞-FRAC→𝒱-FRAC (Abstractionᶜ-FRAC B-⊤ B-abs β))
                  (●ᶜ.map (squareᶜ'-FRAC {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} f-⊤ f-abs f-coherence) .U q•))
             ≡⟨ cong
                (λ q → Abstractionᶜ-FRAC B-⊤ B-abs β .α• .U q)
                (Abstractionᶜ-glue•-out-square
                  {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} {f-⊤} {f-abs} {f-coherence}
                  q•) ⟩
               Abstractionᶜ-FRAC B-⊤ B-abs β .α• .U
                (●ᶜ.map f-⊤ .U
                  (glue•-out
                    (𝒞-FRAC→𝒱-FRAC (Abstractionᶜ-FRAC A-⊤ A-abs α))
                    q•))
             ≡⟨ ●.map-∘
                (f-⊤ .U)
                ((β ⨾ᶜ η◦ᶜ {A = B-abs}) .U)
                (glue•-out
                  (𝒞-FRAC→𝒱-FRAC (Abstractionᶜ-FRAC A-⊤ A-abs α))
                  q•) ⟩
               ●.map (((β ⨾ᶜ η◦ᶜ {A = B-abs}) .U) ∘ f-⊤ .U)
                (glue•-out
                  (𝒞-FRAC→𝒱-FRAC (Abstractionᶜ-FRAC A-⊤ A-abs α))
                  q•)
             ≡⟨ cong
                (λ h → ●.map h
                  (glue•-out
                    (𝒞-FRAC→𝒱-FRAC (Abstractionᶜ-FRAC A-⊤ A-abs α))
                    q•))
                (funExt λ a →
                  cong (η◦ᶜ {A = B-abs} .U) (f-coherence a)) ⟩
               ●.map (((α ⨾ᶜ f-abs) ⨾ᶜ η◦ᶜ {A = B-abs}) .U)
                (glue•-out
                  (𝒞-FRAC→𝒱-FRAC (Abstractionᶜ-FRAC A-⊤ A-abs α))
                  q•)
             ∎))

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
      (Abstractionᶜ-Abstractionᶜ-α•-path {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} {f-⊤} {f-abs} {f-coherence})

  Abstractionᶜ-Abstractionᶜ : ∀ {A-⊤ A-abs α B-⊤ B-abs β f-⊤ f-abs f-coherence} →
    Abstractionᶜ (Abstractionᶜ A-⊤ A-abs α) (Abstractionᶜ B-⊤ B-abs β) (squareᶜ' {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} f-⊤ f-abs f-coherence)
    ≡ Abstractionᶜ A-⊤ B-abs (α ⨾ᶜ f-abs)
  Abstractionᶜ-Abstractionᶜ {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} {f-⊤} {f-abs} {f-coherence} =
      cong 𝒞-fromFRAC
        (Abstractionᶜ-Abstractionᶜ-FRAC
          {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} {f-⊤} {f-abs} {f-coherence})
