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
  squareᶜ'
    (bind' λ x → F _ .charge (c-⊤ x) (ret (f x)))
    (bind' λ x → F _ .charge (c-abs x) (ret (f x)))
    λ a-⊤ →
        bind' (λ x → F _ .charge (ΦY x) (ret x)) .U
        (bind' (λ x → F _ .charge (c-⊤ x) (ret (f x))) .U a-⊤)
      ≡⟨ bind'-assoc _ _ a-⊤ ⟩
        bind' (λ x →
          bind' (λ x → F _ .charge (ΦY x) (ret x)) .U
            (F _ .charge (c-⊤ x) (ret (f x)))) .U a-⊤
      ≡⟨ cong (λ e → bind' {A = F _} e .U a-⊤)
            (funExt λ x →
                bind' (λ x → F _ .charge (ΦY x) (ret x)) .U
                  (F _ .charge (c-⊤ x) (ret (f x)))
              ≡⟨ bind' (λ x → F _ .charge (ΦY x) (ret x)) .charge (c-⊤ x) (ret (f x)) ⟩
                F _ .charge (c-⊤ x)
                  (bind' (λ x → F _ .charge (ΦY x) (ret x)) .U (ret (f x)))
              ≡⟨ cong (F _ .charge (c-⊤ x)) bind'/β ⟩
                F _ .charge (c-⊤ x)
                  (F _ .charge (ΦY (f x)) (ret (f x)))
              ≡⟨ sym (F _ .charge/+) ⟩
                F _ .charge (c-⊤ x +ℂ ΦY (f x)) (ret (f x))
              ∎) ⟩
        bind' (λ x → F _ .charge (c-⊤ x +ℂ ΦY (f x)) (ret (f x))) .U a-⊤
      ≡⟨ cong (λ e → bind' {A = F _} e .U a-⊤) (funExt λ x → cong (λ e → F _ .charge e _) (amortization x)) ⟩
        bind' (λ x → F _ .charge (ΦX x +ℂ c-abs x) (ret (f x))) .U a-⊤
      ≡⟨ cong (λ e → bind' {A = F _} e .U a-⊤)
            (funExt λ x →
                F _ .charge (ΦX x +ℂ c-abs x) (ret (f x))
              ≡⟨ F _ .charge/+ ⟩
                F _ .charge (ΦX x)
                  (F _ .charge (c-abs x) (ret (f x)))
              ≡⟨ cong (F _ .charge (ΦX x)) (sym bind'/β) ⟩
                F _ .charge (ΦX x)
                  (bind' (λ x → F _ .charge (c-abs x) (ret (f x))) .U (ret x))
              ≡⟨ sym (bind' (λ x → F _ .charge (c-abs x) (ret (f x))) .charge (ΦX x) (ret x)) ⟩
                bind' (λ x → F _ .charge (c-abs x) (ret (f x))) .U
                  (F _ .charge (ΦX x) (ret x))
              ∎) ⟩
        bind' (λ x →
          bind' (λ x → F _ .charge (c-abs x) (ret (f x))) .U
            (F _ .charge (ΦX x) (ret x))) .U a-⊤
      ≡⟨ sym (bind'-assoc _ _ a-⊤) ⟩
        bind' (λ x → F _ .charge (c-abs x) (ret (f x))) .U
        (bind' (λ x → F _ .charge (ΦX x) (ret x)) .U a-⊤)
      ∎


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

  potential-credit : ∀ {X : 𝒱ₛ} Φ →
    Potential Φ ≡ [ x ∈ X ] ⋊ ▷[ Φ x ] ⊤
  potential-credit {X = X} Φ =
      Potential Φ
    ≡⟨ sym (𝒞-glue-fracture-retract (Potential Φ)) ⟩
      𝒞-Glue (𝒞-Fracture (Potential Φ))
    ≡⟨ cong 𝒞-Glue fracture-proof ⟩
      𝒞-Glue (𝒞-Fracture ([ x ∈ X ] ⋊ ▷[ Φ x ] ⊤))
    ≡⟨ 𝒞-glue-fracture-retract ([ x ∈ X ] ⋊ ▷[ Φ x ] ⊤) ⟩
      [ x ∈ X ] ⋊ ▷[ Φ x ] ⊤
    ∎
    where
      ▷⊤-●ᶜ : (x : ⟨ X ⟩) → ●ᶜ ⊤ ≡ ●ᶜ (▷[ Φ x ] ⊤)
      ▷⊤-●ᶜ x = sym (▷-●ᶜ (Φ x) ⊤)

      ▷⊤-◯ᶜ : (x : ⟨ X ⟩) → ◯ᶜ ⊤ ≡ ◯ᶜ (▷[ Φ x ] ⊤)
      ▷⊤-◯ᶜ x = sym (▷-◯ᶜ (Φ x) ⊤)

      ▷⊤-coherence : (x : ⟨ X ⟩) →
        PathP
          (λ i → ▷⊤-●ᶜ x i ⊸ ●ᶜ (▷⊤-◯ᶜ x i))
          (●ᶜ.map (CHARGE (Φ x) ⨾ᶜ η◦ᶜ {⊤}))
          (●ᶜ.map (η◦ᶜ {▷[ Φ x ] ⊤}))
      ▷⊤-coherence x = ▷-coherence (Φ x) ⊤

      opaque
        unfolding Abstractionᶜ

        fracture-proof :
          𝒞-Fracture (Potential Φ) ≡
          𝒞-Fracture ([ x ∈ X ] ⋊ ▷[ Φ x ] ⊤)
        fracture-proof =
            𝒞-Fracture (Potential Φ)
          ≡⟨ 𝒞-glue-fracture-section
                (Abstractionᶜ-FRAC _ _ (bind' λ x → F ⟨ X ⟩ .charge (Φ x) (ret x))) ⟩
            Abstractionᶜ-FRAC (F ⟨ X ⟩) (F ⟨ X ⟩) (bind' λ x → F ⟨ X ⟩ .charge (Φ x) (ret x))
          ≡⟨ 𝒞-FRACTURE-pathᶜ
                (cong ●ᶜ F-Σᶜ)
                (cong ◯ᶜ F-Σᶜ)
                (congP (λ _ m → ●ᶜ.map (m ⨾ᶜ η◦ᶜ)) (F-Σᶜ-potential {X} Φ)) ⟩
            record
              { A• = ●ᶜ• ([ x ∈ X ] ⋊ ⊤)
              ; A◦ = ◯ᶜ◦ ([ x ∈ X ] ⋊ ⊤)
              ; α• = ●ᶜ.map (Σᶜ-map {X} {const ⊤} (λ x → CHARGE (Φ x)) ⨾ᶜ η◦ᶜ {[ x ∈ X ] ⋊ ⊤})
              }
          ≡⟨ 𝒞-FRACTURE-pathᶜ
                (Σᶜ-●ᶜ {X} {const ⊤})
                (Σᶜ-◯ᶜ {X} {const ⊤})
                (Σᶜ-fracture-map'-path {X} {const ⊤} {const ⊤}
                  (Σᶜ-map {X} {const ⊤} (λ x → CHARGE (Φ x)) ⨾ᶜ η◦ᶜ {[ x ∈ X ] ⋊ ⊤})
                  (λ x → ●ᶜ.map (CHARGE (Φ x) ⨾ᶜ η◦ᶜ {⊤}))
                  (λ x a → refl)) ⟩
            record
              { A• = ●ᶜ• ([ x ∈ X ] ⋊ ●ᶜ ⊤)
              ; A◦ = ◯ᶜ◦ ([ x ∈ X ] ⋊ ◯ᶜ ⊤)
              ; α• = Σᶜ-fracture-map' {X} {const (●ᶜ ⊤)} {const (◯ᶜ ⊤)} (λ x → ●ᶜ.map (CHARGE (Φ x) ⨾ᶜ η◦ᶜ {⊤}))
              }
          ≡⟨ 𝒞-FRACTURE-pathᶜ
                (cong (●ᶜ ∘ Σᶜ X) (funExt ▷⊤-●ᶜ))
                (cong (◯ᶜ ∘ Σᶜ X) (funExt ▷⊤-◯ᶜ))
                (congP (λ _ → Σᶜ-fracture-map' {X}) (funExt ▷⊤-coherence)) ⟩
            record
              { A• = ●ᶜ• ([ x ∈ X ] ⋊ ●ᶜ (▷[ Φ x ] ⊤))
              ; A◦ = ◯ᶜ◦ ([ x ∈ X ] ⋊ ◯ᶜ (▷[ Φ x ] ⊤))
              ; α• = Σᶜ-fracture-map' {X} {λ x → ●ᶜ (▷[ Φ x ] ⊤)} {λ x → ◯ᶜ (▷[ Φ x ] ⊤)} (λ x → ●ᶜ.map (η◦ᶜ {▷[ Φ x ] ⊤}))
              }
          ≡⟨ 𝒞-FRACTURE-pathᶜ
                (sym (Σᶜ-●ᶜ {X} {λ x → ▷[ Φ x ] ⊤}))
                (sym (Σᶜ-◯ᶜ {X} {λ x → ▷[ Φ x ] ⊤}))
                (symP (Σᶜ-fracture-map'-path {X} {λ x → ▷[ Φ x ] ⊤} {λ x → ▷[ Φ x ] ⊤}
                  (η◦ᶜ {[ x ∈ X ] ⋊ ▷[ Φ x ] ⊤})
                  (λ x → ●ᶜ.map (η◦ᶜ {▷[ Φ x ] ⊤}))
                  (λ x a → refl))) ⟩
            𝒞-Fracture ([ x ∈ X ] ⋊ ▷[ Φ x ] ⊤)
          ∎
