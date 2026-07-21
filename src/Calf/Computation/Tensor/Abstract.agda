module Calf.Computation.Tensor.Abstract where

open import Calf.Value
open import Calf.Computation
open import Calf.Computation.Tensor.Base

open import Cubical.HITs.SetTruncation

open import Calf.Computation.Closed hiding (map)
import Calf.Value.Closed as ●

●ᶜ-⊗ : ●ᶜ (A ⊗ B) ≡ (●ᶜ A ⊗ ●ᶜ B)
●ᶜ-⊗ {A} {B} = conservativity fwd fwd-equiv
  where
    fwd-U₀ : ∥ A ⊛ B ∥₂ → ∥ ●ᶜ A ⊛ ●ᶜ B ∥₂
    fwd-U₀ = map₂ η•ᶜ η•ᶜ .U

    fwd-U : U (●ᶜ (A ⊗ B)) → U (●ᶜ A ⊗ ●ᶜ B)
    fwd-U =
      ●.ind (λ _ → ∥ ●ᶜ A ⊛ ●ᶜ B ∥₂)
        (map₂ η•ᶜ η•ᶜ .U)
        (λ abs → ∣ inj (●.∗ abs) (●.∗ abs) ∣₂)
        (λ w abs →
          ⊛-≡ squash₂ fwd-U₀ (λ _ → ∣ inj (●.∗ abs) (●.∗ abs) ∣₂)
            (λ a b →
                cong (λ z → ∣ inj {●ᶜ A} {●ᶜ B} z (●.η• b) ∣₂) (●.law a abs)
              ∙ cong (λ z → ∣ inj {●ᶜ A} {●ᶜ B} (●.∗ abs) z ∣₂) (●.law b abs))
            w)

    fwd : ●ᶜ (A ⊗ B) ⊸ (●ᶜ A ⊗ ●ᶜ B)
    fwd .U = fwd-U
    fwd .charge c =
      ●.ind (λ a• → fwd-U (●ᶜ (A ⊗ B) .charge c a•) ≡ (●ᶜ A ⊗ ●ᶜ B) .charge c (fwd-U a•))
        (λ w →
          ⊛-≡ squash₂
            (λ w → fwd-U₀ (map (charge⊛ c) w))
            (λ w → map (charge⊛ c) (fwd-U₀ w))
            (λ a b → refl)
            w)
        (λ abs → refl)
        (λ w abs →
          isProp→PathP (λ _ → squash₂ _ _)
            (⊛-≡ squash₂ (λ w → fwd-U₀ (map (charge⊛ c) w)) (λ w → map (charge⊛ c) (fwd-U₀ w)) (λ a b → refl) w)
            refl)

    comb : ●.● (U A) → ●.● (U B) → ●.● ∥ A ⊛ B ∥₂
    comb a• b• = ●.bind a• (λ a → ●.map (λ b → ∣ inj {A} {B} a b ∣₂) b•)

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

    bwd-U₀ : ●ᶜ A ⊛ ●ᶜ B → ●.● ∥ A ⊛ B ∥₂
    bwd-U₀ (inj a• b•) = comb a• b•
    bwd-U₀ (law c a• b• i) = comb-law c a• b• i

    bwd-U : U (●ᶜ A ⊗ ●ᶜ B) → U (●ᶜ (A ⊗ B))
    bwd-U = rec (●.●-preserves-isSet squash₂) bwd-U₀

    sect-pt : ∀ a• b• → fwd-U (comb a• b•) ≡ ∣ inj a• b• ∣₂
    sect-pt a• b• =
      ●.ind (λ a• → fwd-U (comb a• b•) ≡ ∣ inj a• b• ∣₂)
        (λ a →
          ●.ind (λ b• → fwd-U (comb (●.η• a) b•) ≡ ∣ inj (●.η• a) b• ∣₂)
            (λ b → refl)
            (λ abs → cong (λ z → ∣ inj {●ᶜ A} {●ᶜ B} z (●.∗ abs) ∣₂) (sym (●.law a abs)))
            (λ b abs → isProp→PathP (λ _ → squash₂ _ _) _ _)
            b•)
        (λ abs → cong (λ z → ∣ inj (●.∗ abs) z ∣₂) (sym (●.●-path-to-star abs b•)))
        (λ a abs → isProp→PathP (λ _ → squash₂ _ _) _ _)
        a•

    fwd-equiv : isEquivᶜ fwd
    fwd-equiv = isoToIsEquiv (iso fwd-U bwd-U sect retr)
      where
        sect : ∀ y → fwd-U (bwd-U y) ≡ y
        sect = ⊛-≡ squash₂ (λ y → fwd-U (bwd-U y)) (λ y → y) (λ a• b• → sect-pt a• b•)

        retr : ∀ x → bwd-U (fwd-U x) ≡ x
        retr =
          ●.ind (λ x → bwd-U (fwd-U x) ≡ x)
            (⊛-≡ (●.●-preserves-isSet squash₂) (λ w → bwd-U (fwd-U₀ w)) ●.η• (λ a b → refl))
            (λ abs → refl)
            (λ w abs → isProp→PathP (λ _ → ●.●-preserves-isSet squash₂ _ _) _ refl)
