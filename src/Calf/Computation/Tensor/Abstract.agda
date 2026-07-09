module Calf.Computation.Tensor.Abstract where

open import Calf.Value
open import Calf.Computation
open import Calf.Computation.Tensor.Base

open import Cubical.HITs.SetTruncation

module _ where
  open import Calf.Computation.Closed using (●ᶜ; ●ᶜ-charge-map)
  import Calf.Value.Closed as ●

  combine● : ●.● (U A) → ●.● (U B) → ●.● ∥ A ⊛ B ∥₂
  combine● {A} {B} a• b• = ●.bind a• (λ a → ●.map (λ b → ∣ inj {A} {B} a b ∣₂) b•)

  ●ᶜ-⊗ : ●ᶜ (A ⊗ B) ≡ (●ᶜ A ⊗ ●ᶜ B)
  ●ᶜ-⊗ {A} {B} = conservativity Φ Φ-equiv
    where
      ε⊛ : A ⊛ B → ●ᶜ A ⊛ ●ᶜ B
      ε⊛ (inj a b) = inj (●.η• a) (●.η• b)
      ε⊛ (law c a b i) = law c (●.η• a) (●.η• b) i

      ε : ∥ A ⊛ B ∥₂ → ∥ ●ᶜ A ⊛ ●ᶜ B ∥₂
      ε = map ε⊛

      Φ-U : U (●ᶜ (A ⊗ B)) → U (●ᶜ A ⊗ ●ᶜ B)
      Φ-U =
        ●.ind (λ _ → ∥ ●ᶜ A ⊛ ●ᶜ B ∥₂)
          ε
          (λ abs → ∣ inj (●.∗ abs) (●.∗ abs) ∣₂)
          (λ w abs →
            ⊛-≡ squash₂ ε (λ _ → ∣ inj (●.∗ abs) (●.∗ abs) ∣₂)
              (λ a b →
                  cong (λ z → ∣ inj {●ᶜ A} {●ᶜ B} z (●.η• b) ∣₂) (●.law a abs)
                ∙ cong (λ z → ∣ inj {●ᶜ A} {●ᶜ B} (●.∗ abs) z ∣₂) (●.law b abs))
              w)

      Φ : ●ᶜ (A ⊗ B) ⊸ (●ᶜ A ⊗ ●ᶜ B)
      Φ .U = Φ-U
      Φ .charge c =
        ●.ind (λ a• → Φ-U (●ᶜ (A ⊗ B) .charge c a•) ≡ (●ᶜ A ⊗ ●ᶜ B) .charge c (Φ-U a•))
          (λ w →
            ⊛-≡ squash₂
              (λ w → ε (map (charge⊛ c) w))
              (λ w → map (charge⊛ c) (ε w))
              (λ a b → refl)
              w)
          (λ abs → refl)
          (λ w abs →
            isProp→PathP (λ _ → squash₂ _ _)
              (⊛-≡ squash₂ (λ w → ε (map (charge⊛ c) w)) (λ w → map (charge⊛ c) (ε w)) (λ a b → refl) w)
              refl)

      comb : ●.● (U A) → ●.● (U B) → ●.● ∥ A ⊛ B ∥₂
      comb = combine●

      comb-law : ∀ c a• b•
        → comb (●ᶜ A .charge c a•) b• ≡ comb a• (●ᶜ B .charge c b•)
      comb-law c a• b• =
        ●.ind (λ a• → comb (●ᶜ A .charge c a•) b• ≡ comb a• (●ᶜ B .charge c b•))
          (λ a →
              cong (λ f → ●.map f b•) (funExt λ b → cong ∣_∣₂ (law c a b))
            ∙ sym (●.map-∘ (B .charge c) (λ b → ∣ inj a b ∣₂) b•)
            ∙ cong (●.map (λ b → ∣ inj a b ∣₂)) (sym (●ᶜ-charge-map c b•)))
          (λ abs → refl)
          (λ a abs → isProp→PathP (λ _ → ●.●-preserves-isSet squash₂ _ _) _ refl)
          a•

      Ψ⊛ : ●ᶜ A ⊛ ●ᶜ B → ●.● ∥ A ⊛ B ∥₂
      Ψ⊛ (inj a• b•) = comb a• b•
      Ψ⊛ (law c a• b• i) = comb-law c a• b• i

      Ψ : U (●ᶜ A ⊗ ●ᶜ B) → U (●ᶜ (A ⊗ B))
      Ψ = rec (●.●-preserves-isSet squash₂) Ψ⊛

      sect-pt : ∀ a• b• → Φ-U (comb a• b•) ≡ ∣ inj a• b• ∣₂
      sect-pt a• b• =
        ●.ind (λ a• → Φ-U (comb a• b•) ≡ ∣ inj a• b• ∣₂)
          (λ a →
            ●.ind (λ b• → Φ-U (comb (●.η• a) b•) ≡ ∣ inj (●.η• a) b• ∣₂)
              (λ b → refl)
              (λ abs → cong (λ z → ∣ inj {●ᶜ A} {●ᶜ B} z (●.∗ abs) ∣₂) (sym (●.law a abs)))
              (λ b abs → isProp→PathP (λ _ → squash₂ _ _) _ _)
              b•)
          (λ abs → cong (λ z → ∣ inj (●.∗ abs) z ∣₂) (sym (●.●-path-to-star abs b•)))
          (λ a abs → isProp→PathP (λ _ → squash₂ _ _) _ _)
          a•

      Φ-equiv : isEquivᶜ Φ
      Φ-equiv = isoToIsEquiv (iso Φ-U Ψ sect retr)
        where
          sect : ∀ y → Φ-U (Ψ y) ≡ y
          sect = ⊛-≡ squash₂ (λ y → Φ-U (Ψ y)) (λ y → y) (λ a• b• → sect-pt a• b•)

          retr : ∀ x → Ψ (Φ-U x) ≡ x
          retr =
            ●.ind (λ x → Ψ (Φ-U x) ≡ x)
              (⊛-≡ (●.●-preserves-isSet squash₂) (λ w → Ψ (ε w)) ●.η• (λ a b → refl))
              (λ abs → refl)
              (λ w abs → isProp→PathP (λ _ → ●.●-preserves-isSet squash₂ _ _) _ refl)

module _ where
  open import Calf.Computation.Open as ◯ᶜ
  open import Calf.Computation.Closed as ●ᶜ
  open import Calf.Computation.Glue
  open import Calf.Computation.Abstraction

  opaque
    unfolding Abstractionᶜ

    Abstractionᶜ-⊗ : ∀ {A-⊤ A-abs α B-⊤ B-abs β} →
      Abstractionᶜ A-⊤ A-abs α ⊗ Abstractionᶜ B-⊤ B-abs β ≡
      Abstractionᶜ (A-⊤ ⊗ B-⊤) (A-abs ⊗ B-abs) (map₂ α β)
    Abstractionᶜ-⊗ = {!   !}
