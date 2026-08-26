module Calf.Computation.Tensor.Credit where

open import Calf.Core.Abstract using (ABS)
open import Calf.Core.Cost
open import Calf.Value
import Calf.Value.Closed as ●
open import Calf.Computation
open import Calf.Computation.Open as ◯ᶜ
open import Calf.Computation.Closed as ●ᶜ
open import Calf.Computation.Power using (Πᶜ)
open import Calf.Computation.Glue
open import Calf.Computation.Abstraction
open import Calf.Computation.Credit

open import Cubical.Foundations.Univalence using (ua→; ua-gluePath)
open import Cubical.Foundations.Equiv.Properties using (isEquiv[equivFunA≃B∘f]→isEquiv[f])
open import Cubical.Foundations.HLevels using (isOfHLevelPathP')

open import Calf.Computation.Tensor.Base
open import Calf.Computation.Tensor.Closed
open 𝒞-FRACTURE

opaque
  unfolding ▷[_]_ triangle-Uᶜ

  A⊗▷B≡▷[A⊗B] : ∀ c → (A ⊗ (▷[ c ] B)) ≡ (▷[ c ] (A ⊗ B))
  A⊗▷B≡▷[A⊗B] {A} {B} c =
      A ⊗ (▷[ c ] B)
    ≡⟨ sym (𝒞-glue-fracture-retract _) ⟩
      𝒞-Glue (𝒞-Fracture (A ⊗ (▷[ c ] B)))
    ≡⟨ cong 𝒞-Glue (sym fracture-proof) ⟩
      𝒞-Glue (Abstractionᶜ-FRAC (A ⊗ B) (A ⊗ B) (CHARGE c))
    ≡⟨⟩
      ▷[ c ] (A ⊗ B)
    ∎
    where
      fwd : ●ᶜ (A ⊗ B) ⊸ ●ᶜ (A ⊗ (▷[ c ] B))
      fwd = ●ᶜ.map (map₂ idᶜ (triangle-Uᶜ {B} {B}))

      q• : ●ᶜ (A ⊗ B) ≡ ●ᶜ (A ⊗ (▷[ c ] B))
      q• = conservativity fwd (●ᶜ-map₂-equiv (●ᶜ.map-id-equiv {A}) (●ᶜ-Abstractionᶜ-≃ᶜ {B} {B} {CHARGE c} .snd))

      q◦ : ◯ᶜ (A ⊗ B) ≡ ◯ᶜ (A ⊗ (▷[ c ] B))
      q◦ =
        cong (Πᶜ ⟨ ABS ⟩)
          (funExt λ abs → sym (cong (A ⊗_) (▷-open abs c B)))

      qα :
        PathP (λ i → q• i ⊸ ●ᶜ (q◦ i))
          (●ᶜ.map (CHARGE c ⨾ᶜ η◦ᶜ {A = A ⊗ B}))
          (●ᶜ.map (η◦ᶜ {A = A ⊗ (▷[ c ] B)}))
      qα =
        ⊸-path q• (cong ●ᶜ q◦)
          {f₀ = ●ᶜ.map (CHARGE c ⨾ᶜ η◦ᶜ {A = A ⊗ B})}
          {f₁ = ●ᶜ.map (η◦ᶜ {A = A ⊗ (▷[ c ] B)})}
          (ua→
            {e = fwd .U , ●ᶜ-map₂-equiv ●ᶜ.map-id-equiv (●ᶜ-Abstractionᶜ-≃ᶜ .snd)}
            (●.ind-prop _
              (λ w → isOfHLevelPathP' 1 (●.isSet● (is-set (◯ᶜ (A ⊗ (▷[ c ] B))))) _ _)
              (λ w → toPathP
                (rec-unique
                  ((●ᶜ (◯ᶜ (A ⊗ (▷[ c ] B)))) .is-preorder)
                  (λ w → transport (λ i → U (●ᶜ (q◦ i)))
                    (●.η• ((CHARGE c ⨾ᶜ η◦ᶜ {A = A ⊗ B}) .U w)))
                  (λ w → ●.η• (η◦ᶜ {A = A ⊗ (▷[ c ] B)} .U
                    (map₂ idᶜ (triangle-Uᶜ {B} {B}) .U w)))
                  (⊗₀-elimProp {A} {B}
                    (λ _ → is-set (●ᶜ (◯ᶜ (A ⊗ (▷[ c ] B)))) _ _)
                    (λ a b → fromPathP
                      (congP (λ _ → ●.η•)
                        (funExt λ abs →
                          cong ηᴾ (law c a b)
                          ◁ congP (λ _ q → ηᴾ (inj a q))
                              (symP (◯[triangleᶜ'≡b-abs]
                                {B-⊤ = B} {B-abs = B} {β = CHARGE c}
                                {b-⊤ = b} {b-abs = B .charge c b} {b-coh = refl} abs))))))
                  w))
              (λ abs → λ i → ●.∗ abs)))

      fracture-proof :
        Abstractionᶜ-FRAC (A ⊗ B) (A ⊗ B) (CHARGE c) ≡
        𝒞-Fracture (A ⊗ (▷[ c ] B))
      fracture-proof = 𝒞-FRACTURE-pathᶜ q• q◦ qα
