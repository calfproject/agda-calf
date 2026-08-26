module Calf.Computation.Potential where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence using (ua→; ua-gluePath)

open import Calf.Core.Cost
open import Calf.Value
open import Calf.Value.Closed as ●
open import Calf.Computation
open import Calf.Computation.Abstraction
open import Calf.Computation.Free

Potential : (X → ℂ) → 𝒞
Potential {X} Φ = Abstractionᶜ (F X) (F X) (bind' λ x → F _ .charge (Φ x) (ret x))

Potential-0ℂ : Potential {X} (λ _ → 0ℂ) ≡ F X
Potential-0ℂ =
    Abstractionᶜ (F _) (F _) (bind' λ x → F _ .charge 0ℂ (ret x))
  ≡⟨ cong (Abstractionᶜ _ _) (cong bind' (funExt λ _ → F _ .charge/0)) ⟩
    Abstractionᶜ (F _) (F _) (bind' ret)
  ≡⟨ cong (Abstractionᶜ _ _) bind'/η ⟩
    Abstractionᶜ (F _) (F _) idᶜ
  ≡⟨ Abstractionᶜ-id ⟩
    F _
  ∎

square : {ΦX : X → ℂ} {ΦY : Y → ℂ}
  → (f : X → Y)
  → (c-⊤ c-abs : X → ℂ)
  → (∀ x → c-⊤ x +ℂ ΦY (f x) ≡ ΦX x +ℂ c-abs x)
  → Potential ΦX ⊸ Potential ΦY
square {ΦX = ΦX} {ΦY = ΦY} f c-⊤ c-abs amortization =
  squareᶜ' (costed f c-⊤) (costed f c-abs) λ a →
    cong (λ h → h .U a)
      ( costed-⨾ᶜ f c-⊤ (λ y → y) ΦY
      ∙ costed-≡ (λ _ → refl) amortization
      ∙ sym (costed-⨾ᶜ (λ x → x) ΦX f c-abs))


module _ where
  open import Calf.Computation.Open as ◯ᶜ
  open import Calf.Computation.Closed as ●ᶜ
  open import Calf.Computation.Glue
  open import Calf.Computation.Credit
  open import Calf.Computation.Copower
  open import Calf.Computation.Tensor

  private
    Σᶜ-◯ᶜ-in : ∀ {X : 𝒱ₛ} {A : ⟨ X ⟩ → 𝒞} x →
      A x ⊸ ◯ᶜ (Σᶜ X A)
    Σᶜ-◯ᶜ-in x .U a◦ = η◦ (x , a◦)
    Σᶜ-◯ᶜ-in x .charge _ _ = refl

    Σᶜ-fracture-map' : ∀ {X : 𝒱ₛ} {A B : ⟨ X ⟩ → 𝒞} →
      ((x : ⟨ X ⟩) → A x ⊸ ●ᶜ (B x)) →
      ●ᶜ (Σᶜ X A) ⊸ ●ᶜ (◯ᶜ (Σᶜ X B))
    Σᶜ-fracture-map' {X} {A} {B} α = ●ᶜ.bind k
      where
        k : Σᶜ X A ⊸ ●ᶜ (◯ᶜ (Σᶜ X B))
        k .U (x , a) = ●ᶜ.map (Σᶜ-◯ᶜ-in {X} {B} x) .U (α x .U a)
        k .charge c (x , a) =
            ●ᶜ.map (Σᶜ-◯ᶜ-in {X} {B} x) .U (α x .U (A x .charge c a))
          ≡⟨ cong (●ᶜ.map (Σᶜ-◯ᶜ-in {X} {B} x) .U) (α x .charge c a) ⟩
            ●ᶜ.map (Σᶜ-◯ᶜ-in {X} {B} x) .U (●ᶜ (B x) .charge c (α x .U a))
          ≡⟨ ●ᶜ.map (Σᶜ-◯ᶜ-in {X} {B} x) .charge c (α x .U a) ⟩
            ●ᶜ (◯ᶜ (Σᶜ X B)) .charge c (●ᶜ.map (Σᶜ-◯ᶜ-in {X} {B} x) .U (α x .U a))
          ∎

  private opaque
    Σᶜ-fracture-map'-path : ∀ {X : 𝒱ₛ} {A B : ⟨ X ⟩ → 𝒞}
      → (m : Σᶜ X A ⊸ ◯ᶜ (Σᶜ X B))
      → (α : (x : ⟨ X ⟩) → ●ᶜ (A x) ⊸ ●ᶜ (◯ᶜ (B x)))
      → ((x : ⟨ X ⟩) (a : U (A x))
          → ●ᶜ.map (Σᶜ-◯ᶜ-in {X} {◯ᶜ ∘ B} x) .U (α x .U (η• a))
            ≡ η• (Σᶜ-◯ᶜ-fwd {X} {B} .U (m .U (x , a))))
      → PathP
          (λ i → Σᶜ-●ᶜ {X} {A} i ⊸ ●ᶜ (Σᶜ-◯ᶜ {X} {B} i))
          (●ᶜ.map m)
          (Σᶜ-fracture-map' {X} α)
    Σᶜ-fracture-map'-path {X} {A} {B} m α coh =
      ⊸-path
        (Σᶜ-●ᶜ {X} {A})
        (cong ●ᶜ (Σᶜ-◯ᶜ {X} {B}))
        {f₀ = ●ᶜ.map m}
        {f₁ = Σᶜ-fracture-map' {X} α}
        (ua→
          {e = Σᶜ-●ᶜ-fwd {X} {A} .U , Σᶜ-●ᶜ-fwd-equiv {X} {A}}
          (λ w →
            ●.elim
              (λ w →
                ●.isModalPathP ●.isModal●
                  {x = ●ᶜ.map m .U w}
                  {x' = Σᶜ-fracture-map' {X} α .U (Σᶜ-●ᶜ-fwd {X} {A} .U w)})
              (λ (x , a) →
                congP (λ _ → η•)
                  (ua-gluePath
                    ( Σᶜ-◯ᶜ-fwd {X} {B} .U , Σᶜ-◯ᶜ-fwd-equiv {X} {B})
                    {x = m .U (x , a)}
                    refl)
                ▷ sym (coh x a))
              w))

  opaque
    unfolding Abstractionᶜ

    Σᶜ-Abstractionᶜ : {X : 𝒱ₛ} {A-⊤ A-abs : ⟨ X ⟩ → 𝒞} (α : (x : ⟨ X ⟩) → A-⊤ x ⊸ A-abs x)
      → Abstractionᶜ (Σᶜ X A-⊤) (Σᶜ X A-abs) (Σᶜ-map α)
        ≡ Σᶜ X (λ x → Abstractionᶜ (A-⊤ x) (A-abs x) (α x))
    Σᶜ-Abstractionᶜ {X} {A-⊤} {A-abs} α =
      cong 𝒞-Glue fracture-proof ∙ 𝒞-glue-fracture-retract _
      where
        Abs : ⟨ X ⟩ → 𝒞
        Abs x = Abstractionᶜ (A-⊤ x) (A-abs x) (α x)

        fracture-proof :
          Abstractionᶜ-FRAC (Σᶜ X A-⊤) (Σᶜ X A-abs) (Σᶜ-map α) ≡ 𝒞-Fracture (Σᶜ X Abs)
        fracture-proof =
            Abstractionᶜ-FRAC (Σᶜ X A-⊤) (Σᶜ X A-abs) (Σᶜ-map α)
          ≡⟨ 𝒞-FRACTURE-pathᶜ
                (Σᶜ-●ᶜ {X} {A-⊤})
                (Σᶜ-◯ᶜ {X} {A-abs})
                (Σᶜ-fracture-map'-path {X} {A-⊤} {A-abs}
                  (Σᶜ-map α ⨾ᶜ η◦ᶜ {Σᶜ X A-abs})
                  (λ x → ●ᶜ.map (α x ⨾ᶜ η◦ᶜ {A-abs x}))
                  (λ x a → refl)) ⟩
            record
              { A• = ●ᶜ• (Σᶜ X (●ᶜ ∘ A-⊤))
              ; A◦ = ◯ᶜ◦ (Σᶜ X (◯ᶜ ∘ A-abs))
              ; α• = Σᶜ-fracture-map' {X} {●ᶜ ∘ A-⊤} {◯ᶜ ∘ A-abs} (λ x → ●ᶜ.map (α x ⨾ᶜ η◦ᶜ {A-abs x}))
              }
          ≡⟨ 𝒞-FRACTURE-pathᶜ
                (cong (●ᶜ ∘ Σᶜ X) (funExt λ x → sym (●ᶜ-Abstractionᶜ {A-⊤ x} {A-abs x} {α x})))
                (cong (◯ᶜ ∘ Σᶜ X) (funExt λ x → sym (◯ᶜ-Abstractionᶜ {A-⊤ x} {A-abs x} {α x})))
                (congP (λ _ → Σᶜ-fracture-map' {X})
                  (funExt λ x → Abstractionᶜ-coherence {A-⊤ x} {A-abs x} {α x})) ⟩
            record
              { A• = ●ᶜ• (Σᶜ X (●ᶜ ∘ Abs))
              ; A◦ = ◯ᶜ◦ (Σᶜ X (◯ᶜ ∘ Abs))
              ; α• = Σᶜ-fracture-map' {X} {●ᶜ ∘ Abs} {◯ᶜ ∘ Abs} (λ x → ●ᶜ.map (η◦ᶜ {Abs x}))
              }
          ≡⟨ 𝒞-FRACTURE-pathᶜ
                (sym (Σᶜ-●ᶜ {X} {Abs}))
                (sym (Σᶜ-◯ᶜ {X} {Abs}))
                (symP (Σᶜ-fracture-map'-path {X} {Abs} {Abs}
                  (η◦ᶜ {Σᶜ X Abs})
                  (λ x → ●ᶜ.map (η◦ᶜ {Abs x}))
                  (λ x a → refl))) ⟩
            𝒞-Fracture (Σᶜ X Abs)
          ∎

  opaque
    unfolding ▷[_]_

    potential-credit : ∀ {X : 𝒱ₛ} Φ →
      Potential Φ ≡ [ x ∈ X ] ⋊ ▷[ Φ x ] ⊤
    potential-credit {X = X} Φ =
        Potential Φ
      ≡⟨ (λ i → Abstractionᶜ (F-Σᶜ {X} i) (F-Σᶜ {X} i) (F-Σᶜ-potential {X} Φ i)) ⟩
        Abstractionᶜ ([ x ∈ X ] ⋊ ⊤) ([ x ∈ X ] ⋊ ⊤) (Σᶜ-map {X} {const ⊤} (λ x → CHARGE (Φ x)))
      ≡⟨ Σᶜ-Abstractionᶜ (λ x → CHARGE (Φ x)) ⟩
        [ x ∈ X ] ⋊ ▷[ Φ x ] ⊤
      ∎
