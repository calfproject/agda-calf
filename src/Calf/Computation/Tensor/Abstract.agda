module Calf.Computation.Tensor.Abstract where

open import Cubical.Foundations.Structure

open import Calf.Core.Abstract
open import Calf.Value
open import Calf.Computation
open import Calf.Computation.Tensor.Base

open import Cubical.HITs.SetTruncation

open import Calf.Computation.Closed hiding (map)
import Calf.Value.Closed as ●
import Calf.Value.Open as ◯

●ᶜ-⊗ : ●ᶜ (A ⊗ B) ≡ (●ᶜ A ⊗ ●ᶜ B)
●ᶜ-⊗ {A} {B} = conservativity fwd fwd-equiv
  where
    ⊗•-isContr : (abs : ⟨ ABS ⟩) → isContr (U (●ᶜ A ⊗ ●ᶜ B))
    ⊗•-isContr abs .fst = ∣ inj (●.∗ abs) (●.∗ abs) ∣₂
    ⊗•-isContr abs .snd =
      ⊛-≡ squash₂ (λ _ → ∣ inj (●.∗ abs) (●.∗ abs) ∣₂) (λ w → w)
        (λ a• b• →
          cong₂ (λ x y → ∣ inj {●ᶜ A} {●ᶜ B} x y ∣₂)
            (●.◯-isProp● abs (●.∗ abs) a•)
            (●.◯-isProp● abs (●.∗ abs) b•))

    ⊗•-isProp : (abs : ⟨ ABS ⟩) → isProp (U (●ᶜ A ⊗ ●ᶜ B))
    ⊗•-isProp abs = isContr→isProp (⊗•-isContr abs)

    ⊗• : 𝒞•
    ⊗• = (●ᶜ A ⊗ ●ᶜ B) , isConnected◯→isModal● (◯.◯isContr→isConnected ⊗•-isContr)

    fwd : ●ᶜ (A ⊗ B) ⊸ (●ᶜ A ⊗ ●ᶜ B)
    fwd = ●ᶜ-rec ⊗• (map₂ η•ᶜ η•ᶜ)

    comb : ●.● (U A) → ●.● (U B) → ●.● ∥ A ⊛ B ∥₂
    comb a• b• = ●.bind a• (λ a → ●.map (λ b → ∣ inj {A} {B} a b ∣₂) b•)

    opaque
      unfolding ●.elim′

      comb-law : ∀ c a• b•
        → comb (●ᶜ A .charge c a•) b• ≡ comb a• (●ᶜ B .charge c b•)
      comb-law c a• b• =
        ●.ind-prop (λ a• → comb (●ᶜ A .charge c a•) b• ≡ comb a• (●ᶜ B .charge c b•))
          (λ _ → ●.isSet● squash₂ _ _)
          (λ a →
            ●.ind-prop (λ b• → comb (●.η• (A .charge c a)) b• ≡ comb (●.η• a) (●ᶜ B .charge c b•))
              (λ _ → ●.isSet● squash₂ _ _)
              (λ b → cong (λ w → ●.η• ∣ w ∣₂) (law c a b))
              (λ abs → refl)
              b•)
          (λ abs → refl)
          a•

    bwd-U₀ : ●ᶜ A ⊛ ●ᶜ B → ●.● ∥ A ⊛ B ∥₂
    bwd-U₀ (inj a• b•) = comb a• b•
    bwd-U₀ (law c a• b• i) = comb-law c a• b• i

    bwd-U : U (●ᶜ A ⊗ ●ᶜ B) → U (●ᶜ (A ⊗ B))
    bwd-U = rec (●.isSet● squash₂) bwd-U₀

    opaque
      unfolding ●.elim′

      sect-pt : ∀ a• b• → fwd .U (comb a• b•) ≡ ∣ inj a• b• ∣₂
      sect-pt a• b• =
        ●.ind-prop (λ a• → fwd .U (comb a• b•) ≡ ∣ inj a• b• ∣₂)
          (λ _ → squash₂ _ _)
          (λ a →
            ●.ind-prop (λ b• → fwd .U (comb (●.η• a) b•) ≡ ∣ inj (●.η• a) b• ∣₂)
              (λ _ → squash₂ _ _)
              (λ b → refl)
              (λ abs → ⊗•-isProp abs _ _)
              b•)
          (λ abs → ⊗•-isProp abs _ _)
          a•

    fwd-equiv : isEquivᶜ fwd
    fwd-equiv = isoToIsEquiv (iso (fwd .U) bwd-U sect retr)
      where
        sect : ∀ y → fwd .U (bwd-U y) ≡ y
        sect = ⊛-≡ squash₂ (λ y → fwd .U (bwd-U y)) (λ y → y) sect-pt

        opaque
          unfolding ●.elim′

          retr : ∀ x → bwd-U (fwd .U x) ≡ x
          retr =
            ●.ind-prop _ (λ _ → ●.isSet● squash₂ _ _)
              (⊛-≡ (●.isSet● squash₂) (λ w → bwd-U (fwd .U (●.η• w))) ●.η• (λ a b → refl))
              (λ abs → ●.◯-isProp● abs _ _)
