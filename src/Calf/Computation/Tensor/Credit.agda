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
  unfolding Abstractionᶜ triangle-Uᶜ

  ⊗-Abstractionᶜ : (A : 𝒞) {B-⊤ B-abs : 𝒞} {β : B-⊤ ⊸ B-abs}
    → A ⊗ Abstractionᶜ B-⊤ B-abs β ≡ Abstractionᶜ (A ⊗ B-⊤) (A ⊗ B-abs) (map₂ idᶜ β)
  ⊗-Abstractionᶜ A {B-⊤} {B-abs} {β} =
    sym (𝒞-glue-fracture-retract _) ∙ cong 𝒞-Glue (sym fracture-proof)
    where
      fwd : ●ᶜ (A ⊗ B-⊤) ⊸ ●ᶜ (A ⊗ Abstractionᶜ B-⊤ B-abs β)
      fwd = ●ᶜ.map (map₂ idᶜ (triangle-Uᶜ β))

      fwd-equiv : isEquiv (fwd .U)
      fwd-equiv = ●ᶜ-map₂-equiv (●ᶜ.map-id-equiv {A}) (●ᶜ-Abstractionᶜ-≃ᶜ β .snd)

      q• : ●ᶜ (A ⊗ B-⊤) ≡ ●ᶜ (A ⊗ Abstractionᶜ B-⊤ B-abs β)
      q• = conservativity fwd fwd-equiv

      q◦ : ◯ᶜ (A ⊗ B-abs) ≡ ◯ᶜ (A ⊗ Abstractionᶜ B-⊤ B-abs β)
      q◦ =
        cong (Πᶜ ⟨ ABS ⟩)
          (funExt λ abs → sym (cong (A ⊗_) (◯[Abstractionᶜ≡A-abs] β abs)))

      qα :
        PathP (λ i → q• i ⊸ ●ᶜ (q◦ i))
          (●ᶜ.map (map₂ idᶜ β ⨾ᶜ η◦ᶜ))
          (●ᶜ.map η◦ᶜ)
      qα =
        ⊸-path q• (cong ●ᶜ q◦)
          (ua→ {e = fwd .U , fwd-equiv}
            (●.elim (λ _ → ●.isModalPathP ●.isModal●) λ w →
              rec-uniqueP (λ i → U (●ᶜ (q◦ i)))
                (●ᶜ (◯ᶜ (A ⊗ Abstractionᶜ B-⊤ B-abs β)) .is-preorder)
                (λ w → ●.η• ((map₂ idᶜ β ⨾ᶜ η◦ᶜ) .U w))
                (λ w → ●.η• (η◦ᶜ {A = A ⊗ Abstractionᶜ B-⊤ B-abs β} .U
                  (map₂ idᶜ (triangle-Uᶜ β) .U w)))
                (⊗₀-elimProp {A} {B-⊤}
                  (λ _ → isOfHLevelPathP' {A = λ i → U (●ᶜ (q◦ i))} 1
                    (is-set (●ᶜ (◯ᶜ (A ⊗ Abstractionᶜ B-⊤ B-abs β)))) _ _)
                  (λ a b →
                    congP (λ _ → ●.η•) (funExt λ abs →
                      congP (λ i q → ηᴾ (inj {A} {◯[Abstractionᶜ≡A-abs] β abs (~ i)} a q))
                        (symP (◯[triangleᶜ'≡b-abs] β b (β .U b) refl abs)))))
                w))

      fracture-proof :
        Abstractionᶜ-FRAC (A ⊗ B-⊤) (A ⊗ B-abs) (map₂ idᶜ β)
          ≡ 𝒞-Fracture (A ⊗ Abstractionᶜ B-⊤ B-abs β)
      fracture-proof = 𝒞-FRACTURE-pathᶜ q• q◦ qα

map₂-idᶜ-CHARGE : ∀ c → map₂ (idᶜ {A}) (CHARGE {B} c) ≡ CHARGE {A ⊗ B} c
map₂-idᶜ-CHARGE c =
  ⊸-path refl refl (funExt (⊗₀-≡ isPreorderP _ _ λ a b → sym (∥-law c a b)))

opaque
  unfolding ▷[_]_

  A⊗▷B≡▷[A⊗B] : ∀ c → (A ⊗ (▷[ c ] B)) ≡ (▷[ c ] (A ⊗ B))
  A⊗▷B≡▷[A⊗B] {A} {B} c =
    ⊗-Abstractionᶜ A ∙ cong (Abstractionᶜ (A ⊗ B) (A ⊗ B)) (map₂-idᶜ-CHARGE c)
