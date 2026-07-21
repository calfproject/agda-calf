module Calf.Computation.Potential where

open import Cubical.Foundations.Prelude

open import Calf.Core.Cost
open import Calf.Value
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
  open import Calf.Computation.Open
  open import Calf.Computation.Closed
  open import Calf.Computation.Glue
  open import Calf.Computation.Credit
  open import Calf.Computation.Copower
  open import Calf.Computation.Tensor

  potential-credit : ∀ {X : 𝒱ₛ} Φ →
    Potential Φ ≡ [ x ∈ X ] ⋊ ▷[ Φ x ] ⊤
  potential-credit {X} Φ = 𝒞-fracture-≡ lemma• lemma◦ {!   !}
    where
      lemma• : ●ᶜ (Potential Φ) ≡ ●ᶜ ([ x ∈ X ] ⋊ ▷[ Φ x ] ⊤)
      lemma• =
          ●ᶜ (Potential Φ)
        ≡⟨ ●ᶜ-Abstractionᶜ ⟩
          ●ᶜ (F ⟨ X ⟩)
        ≡⟨ cong ●ᶜ (sym (Σᶜ-F {X})) ⟩
          ●ᶜ ([ x ∈ X ] ⋊ ⊤)
        ≡⟨ Σᶜ-●ᶜ {X} {const ⊤} ⟩
          ●ᶜ ([ x ∈ X ] ⋊ ●ᶜ ⊤)
        ≡⟨ cong (●ᶜ ∘ Σᶜ X) (funExt λ _ → sym ●ᶜ-Abstractionᶜ) ⟩
          ●ᶜ ([ x ∈ X ] ⋊ ●ᶜ (▷[ Φ x ] ⊤))
        ≡⟨ sym (Σᶜ-●ᶜ {X} {λ x → ▷[ Φ x ] ⊤}) ⟩
          ●ᶜ ([ x ∈ X ] ⋊ ▷[ Φ x ] ⊤)
        ∎

      lemma◦ : ◯ᶜ (Potential Φ) ≡ ◯ᶜ ([ x ∈ X ] ⋊ ▷[ Φ x ] ⊤)
      lemma◦ =
          ◯ᶜ (Potential Φ)
        ≡⟨ ◯ᶜ-Abstractionᶜ ⟩
          ◯ᶜ (F ⟨ X ⟩)
        ≡⟨ cong ◯ᶜ (sym (Σᶜ-F {X})) ⟩
          ◯ᶜ ([ x ∈ X ] ⋊ ⊤)
        ≡⟨ Σᶜ-◯ᶜ {X} {const ⊤} ⟩
          ◯ᶜ ([ x ∈ X ] ⋊ ◯ᶜ ⊤)
        ≡⟨ cong (◯ᶜ ∘ Σᶜ X) (funExt λ _ → sym ◯ᶜ-Abstractionᶜ) ⟩
          ◯ᶜ ([ x ∈ X ] ⋊ ◯ᶜ (▷[ Φ x ] ⊤))
        ≡⟨ sym (Σᶜ-◯ᶜ {X} {λ x → ▷[ Φ x ] ⊤}) ⟩
          ◯ᶜ ([ x ∈ X ] ⋊ ▷[ Φ x ] ⊤)
        ∎
