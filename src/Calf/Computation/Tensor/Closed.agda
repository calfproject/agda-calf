module Calf.Computation.Tensor.Closed where

open import Cubical.Foundations.Structure

open import Calf.Core.Abstract
open import Calf.Value
open import Calf.Computation
open import Calf.Computation.Tensor.Base

open import Cubical.HITs.SetTruncation
open import Cubical.Foundations.Equiv.Properties using (isEquiv[equivFunA≃B∘f]→isEquiv[f])

open import Calf.Computation.Closed as ●ᶜ hiding (map)
import Calf.Value.Closed as ●
import Calf.Value.Open as ◯

module _ {A B : 𝒞} where
  private
    ⊗•-isContr : (abs : ⟨ ABS ⟩) → isContr (U (●ᶜ A ⊗ ●ᶜ B))
    ⊗•-isContr abs = ⊗-isContr (◯-isConnected abs) (◯-isConnected abs)

  private
    ⊗• : 𝒞•
    ⊗• = (●ᶜ A ⊗ ●ᶜ B) , isConnected◯→isModal● (◯.◯isContr→isConnected ⊗•-isContr)

  ●ᶜ-⊗-fwd : ●ᶜ (A ⊗ B) ⊸ (●ᶜ A ⊗ ●ᶜ B)
  ●ᶜ-⊗-fwd = ●ᶜ-rec ⊗• (map₂ η•ᶜ η•ᶜ)

  private
    comb-in : U (●ᶜ B) → A ⊸ ●ᶜ (A ⊗ B)
    comb-in b• .U a = ●.map (λ b → ∣ inj a b ∣₂) b•
    comb-in b• .charge c a =
      sym (●.map-∘ (λ b → ∣ inj a b ∣₂) ((A ⊗ B) .charge c) b•)

    combᶜ : U (●ᶜ B) → ●ᶜ A ⊸ ●ᶜ (A ⊗ B)
    combᶜ b• = ●ᶜ.bind (comb-in b•)

    combᶜ-charge : ∀ c b• → combᶜ b• ⨾ᶜ CHARGE c ≡ combᶜ (●ᶜ B .charge c b•)
    combᶜ-charge c b• =
        combᶜ b• ⨾ᶜ CHARGE c
      ≡⟨ ⊸-path refl refl refl ⟩
        combᶜ b• ⨾ᶜ ●ᶜ.map (CHARGE c)
      ≡⟨ ●ᶜ.bind-map (comb-in b•) (CHARGE c) ⟩
        ●ᶜ.bind (comb-in b• ⨾ᶜ ●ᶜ.map (CHARGE c))
      ≡⟨ cong ●ᶜ.bind
            (⊸-path refl refl (funExt λ a →
                ●.map-∘ (λ b → ∣ inj a b ∣₂) ((A ⊗ B) .charge c) b•
              ∙ cong (λ h → ●.map h b•) (funExt λ b → cong ∣_∣₂ (law c a b))
              ∙ sym (●.map-∘ (B .charge c) (λ b → ∣ inj a b ∣₂) b•))) ⟩
        ●ᶜ.bind (comb-in (●ᶜ B .charge c b•))
      ∎

    comb : ●.● (U A) → ●.● (U B) → ●.● ∥ A ⊛ B ∥₂
    comb a• b• = combᶜ b• .U a•

    sect-pt : ∀ a• b• → ●ᶜ-⊗-fwd .U (comb a• b•) ≡ ∣ inj a• b• ∣₂
    sect-pt a• b• =
      ●.ind-prop (λ a• → ●ᶜ-⊗-fwd .U (comb a• b•) ≡ ∣ inj a• b• ∣₂)
        (λ _ → squash₂ _ _)
        (λ a →
          ●.ind-prop (λ b• → ●ᶜ-⊗-fwd .U (comb (●.η• a) b•) ≡ ∣ inj (●.η• a) b• ∣₂)
            (λ _ → squash₂ _ _)
            (λ b → ●ᶜ-rec-β ⊗• (map₂ η•ᶜ η•ᶜ) ∣ inj a b ∣₂)
            (λ abs → isContr→isProp (⊗•-isContr abs) _ _)
            b•)
        (λ abs → isContr→isProp (⊗•-isContr abs) _ _)
        a•

  ⊗-str● : (●ᶜ A ⊗ ●ᶜ B) ⊸ ●ᶜ (A ⊗ B)
  ⊗-str● =
    ⊗-rec comb
      (λ c a• b• → combᶜ b• .charge c a•)
      (λ c a• b• → cong (λ h → h .U a•) (sym (combᶜ-charge c b•)))

  ●ᶜ-⊗-equiv : isEquivᶜ ●ᶜ-⊗-fwd
  ●ᶜ-⊗-equiv = isoToIsEquiv (iso (●ᶜ-⊗-fwd .U) (⊗-str● .U) sect retr)
    where
      sect : ∀ y → ●ᶜ-⊗-fwd .U (⊗-str● .U y) ≡ y
      sect = ⊛-≡ squash₂ (λ y → ●ᶜ-⊗-fwd .U (⊗-str● .U y)) (λ y → y) sect-pt

      retr : ∀ x → ⊗-str● .U (●ᶜ-⊗-fwd .U x) ≡ x
      retr =
        ●.ind-prop _ (λ _ → ●.isSet● squash₂ _ _)
          (⊛-≡ (●.isSet● squash₂) (λ w → ⊗-str● .U (●ᶜ-⊗-fwd .U (●.η• w))) ●.η•
            (λ a b → cong (⊗-str● .U) (●ᶜ-rec-β ⊗• (map₂ η•ᶜ η•ᶜ) ∣ inj a b ∣₂)))
          (λ abs → ●.◯-isProp● abs _ _)

  ●ᶜ-⊗ : ●ᶜ (A ⊗ B) ≡ (●ᶜ A ⊗ ●ᶜ B)
  ●ᶜ-⊗ = conservativity ●ᶜ-⊗-fwd ●ᶜ-⊗-equiv

●ᶜ-⊗-natural : {A A' B B' : 𝒞} (f : A ⊸ A') (g : B ⊸ B')
  → ∀ w →
    map₂ (●ᶜ.map f) (●ᶜ.map g) .U (●ᶜ-⊗-fwd .U w)
    ≡ ●ᶜ-⊗-fwd .U (●ᶜ.map (map₂ f g) .U w)
●ᶜ-⊗-natural {A} {A'} {B} {B'} f g =
  ●.ind-prop _ (λ _ → squash₂ _ _)
    (⊛-≡ squash₂
      (λ z → map₂ (●ᶜ.map f) (●ᶜ.map g) .U (●ᶜ-⊗-fwd .U (●.η• z)))
      (λ z → ●ᶜ-⊗-fwd .U (●ᶜ.map (map₂ f g) .U (●.η• z)))
      (λ a b → refl))
    (λ abs → isContr→isProp (⊗-isContr (◯-isConnected abs) (◯-isConnected abs)) _ _)

●ᶜ-map₂-equiv : {A A' B B' : 𝒞} {f : A ⊸ A'} {g : B ⊸ B'}
  → isEquiv (●ᶜ.map f .U) → isEquiv (●ᶜ.map g .U)
  → isEquiv (●ᶜ.map (map₂ f g) .U)
●ᶜ-map₂-equiv {A} {A'} {B} {B'} {f} {g} fe ge =
  isEquiv[equivFunA≃B∘f]→isEquiv[f] (●ᶜ.map (map₂ f g) .U) (●ᶜ-⊗-fwd .U , ●ᶜ-⊗-equiv)
    (subst isEquiv (funExt (●ᶜ-⊗-natural f g))
      (compEquiv (●ᶜ-⊗-fwd .U , ●ᶜ-⊗-equiv)
        (map₂ (●ᶜ.map f) (●ᶜ.map g) .U , map₂-equivᶜ {f = ●ᶜ.map f} {g = ●ᶜ.map g} fe ge) .snd))
