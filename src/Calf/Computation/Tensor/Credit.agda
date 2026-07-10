module Calf.Computation.Tensor.Credit where

open import Calf.Core.Abstract using (ABS)
open import Calf.Core.Cost
open import Calf.Value
import Calf.Value.Closed as ●
open import Calf.Computation
open import Calf.Computation.Open as ◯ᶜ
open import Calf.Computation.Closed as ●ᶜ
open import Calf.Computation.Glue
open import Calf.Computation.Abstraction
open import Calf.Computation.Credit

open import Cubical.HITs.SetTruncation

open import Calf.Computation.Tensor.Base

opaque
  unfolding Abstractionᶜ

  A⊗▷B≡▷[A⊗B] : ∀ c → (A ⊗ (▷[ c ] B)) ≡ (▷[ c ] (A ⊗ B))
  A⊗▷B≡▷[A⊗B] {A} {B} c = conservativity fwd fwd-equiv
    where
      ▷B-rhs◦ : U B → U (◯ᶜ B)
      ▷B-rhs◦ = (CHARGE c ⨾ᶜ η◦ᶜ {A = B}) .U

      rhs◦ : U (A ⊗ B) → U (◯ᶜ (A ⊗ B))
      rhs◦ = (CHARGE c ⨾ᶜ η◦ᶜ {A = A ⊗ B}) .U

      rhsα : U (●ᶜ (A ⊗ B)) → U (●ᶜ (◯ᶜ (A ⊗ B)))
      rhsα = ●ᶜ.map (CHARGE c ⨾ᶜ η◦ᶜ {A = A ⊗ B}) .U

      open⊗ : U A → U (◯ᶜ B) → U (◯ᶜ (A ⊗ B))
      open⊗ a q◦ abs = ∣ inj a (q◦ abs) ∣₂

      unit▷ : U B → U (▷[ c ] B)
      unit▷ b .• = ●.η• b
      unit▷ b .◦ = ▷B-rhs◦ b
      unit▷ b .•→◦ = refl

      unit▷∗ : ⟨ ABS ⟩ → U B → U (▷[ c ] B)
      unit▷∗ abs b .• = ●.∗ abs
      unit▷∗ abs b .◦ = η◦ b
      unit▷∗ abs b .•→◦ = sym (●.law (η◦ b) abs)

      unit▷-charge
        : (e : ℂ) (b : U B)
        → (▷[ c ] B) .charge e (unit▷ b) ≡ unit▷ (B .charge e b)
      unit▷-charge e b =
        glue-path {A-⊤ = B} {A-abs = B} {α = CHARGE c}
          refl
          (funExt λ _ → charge/comm B {c = e} {c' = c} {a = b})

      unit▷∗-charge
        : (abs : ⟨ ABS ⟩) (e : ℂ) (b : U B)
        → (▷[ c ] B) .charge e (unit▷∗ abs b) ≡ unit▷∗ abs (B .charge e b)
      unit▷∗-charge abs e b =
        glue-path {A-⊤ = B} {A-abs = B} {α = CHARGE c} refl refl

      unit▷ᶜ : B ⊸ ▷[ c ] B
      unit▷ᶜ .U = unit▷
      unit▷ᶜ .charge e b = sym (unit▷-charge e b)

      unit▷∗ᶜ : ⟨ ABS ⟩ → B ⊸ ▷[ c ] B
      unit▷∗ᶜ abs .U = unit▷∗ abs
      unit▷∗ᶜ abs .charge e b = sym (unit▷∗-charge abs e b)

      tensor-unit▷ : U (A ⊗ B) → U (A ⊗ (▷[ c ] B))
      tensor-unit▷ = map₂ idᶜ unit▷ᶜ .U

      tensor-star▷ : ⟨ ABS ⟩ → U (A ⊗ B) → U (A ⊗ (▷[ c ] B))
      tensor-star▷ abs = map₂ idᶜ (unit▷∗ᶜ abs) .U

      unit▷-star-charge
        : (abs : ⟨ ABS ⟩) (b : U B)
        → unit▷ b ≡ (▷[ c ] B) .charge c (unit▷∗ abs b)
      unit▷-star-charge abs b =
        glue-path {A-⊤ = B} {A-abs = B} {α = CHARGE c}
          (●.law b abs)
          refl

      tensor-unit▷-star-charge
        : (abs : ⟨ ABS ⟩) (x : U (A ⊗ B))
        → tensor-unit▷ x ≡ tensor-star▷ abs ((A ⊗ B) .charge c x)
      tensor-unit▷-star-charge abs =
        ⊛-≡ squash₂
          tensor-unit▷
          (tensor-star▷ abs ∘ (A ⊗ B) .charge c)
          (λ a b →
              cong (λ q → ∣ inj {A} {▷[ c ] B} a q ∣₂) (unit▷-star-charge abs b)
            ∙ sym (cong ∣_∣₂ (law {A = A} {B = ▷[ c ] B} c a (unit▷∗ abs b))))

      fwd-inj-coh : (a : U A) (q : U (▷[ c ] B)) →
        rhsα (●.map (λ b → ∣ inj a b ∣₂) (q .•))
          ≡ ●.η• (open⊗ a (q .◦))
      fwd-inj-coh a q =
          ●.map rhs◦ (●.map (λ b → ∣ inj a b ∣₂) (q .•))
        ≡⟨ ●.map-∘ (λ b → ∣ inj a b ∣₂) rhs◦ (q .•) ⟩
          ●.map (rhs◦ ∘ (λ b → ∣ inj a b ∣₂)) (q .•)
        ≡⟨ cong (λ h → ●.map h (q .•))
              (funExt λ b →
                funExt λ _ → cong ∣_∣₂ (law {A = A} {B = B} c a b)) ⟩
          ●.map (open⊗ a ∘ ▷B-rhs◦) (q .•)
        ≡⟨ sym (●.map-∘ ▷B-rhs◦ (open⊗ a) (q .•)) ⟩
          ●.map (open⊗ a) (●ᶜ.map (CHARGE c ⨾ᶜ η◦ᶜ {A = B}) .U (q .•))
        ≡⟨ cong (●.map (open⊗ a)) (q .•→◦) ⟩
          ●.η• (open⊗ a (q .◦))
        ∎

      fwd-law-•
        : (e : ℂ) (a : U A) (q : U (▷[ c ] B))
        → ●.map (λ b → ∣ inj {A} {B} (A .charge e a) b ∣₂) (q .•)
          ≡ ●.map (λ b → ∣ inj {A} {B} a b ∣₂) (●ᶜ B .charge e (q .•))
      fwd-law-• e a q =
          ●.map (λ b → ∣ inj {A} {B} (A .charge e a) b ∣₂) (q .•)
        ≡⟨ cong (λ h → ●.map h (q .•))
              (funExt λ b → cong ∣_∣₂ (law {A = A} {B = B} e a b)) ⟩
          ●.map ((λ b → ∣ inj {A} {B} a b ∣₂) ∘ B .charge e) (q .•)
        ≡⟨ sym (●.map-∘ (B .charge e) (λ b → ∣ inj {A} {B} a b ∣₂) (q .•)) ⟩
          ●.map (λ b → ∣ inj {A} {B} a b ∣₂) (●.map (B .charge e) (q .•))
        ≡⟨ cong (●.map (λ b → ∣ inj {A} {B} a b ∣₂)) (sym (●ᶜ-charge-map e (q .•))) ⟩
          ●.map (λ b → ∣ inj {A} {B} a b ∣₂) (●ᶜ B .charge e (q .•))
        ∎

      fwd-law-◦
        : (e : ℂ) (a : U A) (q : U (▷[ c ] B))
        → open⊗ (A .charge e a) (q .◦)
          ≡ open⊗ a (λ abs → B .charge e (q .◦ abs))
      fwd-law-◦ e a q =
        funExt λ abs → cong ∣_∣₂ (law {A = A} {B = B} e a (q .◦ abs))

      fwd⊛ : A ⊛ (▷[ c ] B) → U (▷[ c ] (A ⊗ B))
      fwd⊛ (inj a q) .• = ●.map (λ b → ∣ inj a b ∣₂) (q .•)
      fwd⊛ (inj a q) .◦ = open⊗ a (q .◦)
      fwd⊛ (inj a q) .•→◦ = fwd-inj-coh a q
      fwd⊛ (law e a q i) =
        glue-path {A-⊤ = A ⊗ B} {A-abs = A ⊗ B} {α = CHARGE c}
          {q =
            record
              { • = ●.map (λ b → ∣ inj (A .charge e a) b ∣₂) (q .•)
              ; ◦ = open⊗ (A .charge e a) (q .◦)
              ; •→◦ = fwd-inj-coh (A .charge e a) q
              }}
          {r =
            record
              { • = ●.map (λ b → ∣ inj a b ∣₂) (●ᶜ B .charge e (q .•))
              ; ◦ = open⊗ a (λ abs → B .charge e (q .◦ abs))
              ; •→◦ = fwd-inj-coh a ((▷[ c ] B) .charge e q)
              }}
          (fwd-law-• e a q)
          (fwd-law-◦ e a q)
          i

      fwd-charge-•
        : (e : ℂ) (a : U A) (q : U (▷[ c ] B))
        → ●.map (λ b → ∣ inj (A .charge e a) b ∣₂) (q .•)
          ≡ ●ᶜ (A ⊗ B) .charge e (●.map (λ b → ∣ inj a b ∣₂) (q .•))
      fwd-charge-• e a q =
          ●.map (λ b → ∣ inj (A .charge e a) b ∣₂) (q .•)
        ≡⟨ sym (●.map-∘ (λ b → ∣ inj a b ∣₂) ((A ⊗ B) .charge e) (q .•)) ⟩
          ●.map ((A ⊗ B) .charge e) (●.map (λ b → ∣ inj a b ∣₂) (q .•))
        ≡⟨ sym (●ᶜ-charge-map e (●.map (λ b → ∣ inj a b ∣₂) (q .•))) ⟩
          ●ᶜ (A ⊗ B) .charge e (●.map (λ b → ∣ inj a b ∣₂) (q .•))
        ∎

      fwd-charge
        : (e : ℂ) (a : U A) (q : U (▷[ c ] B))
        → fwd⊛ (charge⊛ e (inj a q)) ≡ (▷[ c ] (A ⊗ B)) .charge e (fwd⊛ (inj a q))
      fwd-charge e a q =
        glue-path {A-⊤ = A ⊗ B} {A-abs = A ⊗ B} {α = CHARGE c}
          (fwd-charge-• e a q)
          refl

      fwd : A ⊗ (▷[ c ] B) ⊸ ▷[ c ] (A ⊗ B)
      fwd .U = rec ((▷[ c ] (A ⊗ B)) .is-set) fwd⊛
      fwd .charge e =
        ⊛-≡ ((▷[ c ] (A ⊗ B)) .is-set)
          (λ z → fwd .U ((A ⊗ (▷[ c ] B)) .charge e z))
          (λ z → (▷[ c ] (A ⊗ B)) .charge e (fwd .U z))
          (fwd-charge e)

      bwd-from-fiber
        : (q◦ : U (◯ᶜ (A ⊗ B)))
        → ●.● (fiber rhs◦ q◦)
        → U (A ⊗ (▷[ c ] B))
      bwd-from-fiber q◦ =
        ●.ind
          (λ _ → U (A ⊗ (▷[ c ] B)))
          (λ (x , _) → tensor-unit▷ x)
          (λ abs → tensor-star▷ abs (q◦ abs))
          (λ (x , x-coh) abs →
              tensor-unit▷ x
            ≡⟨ tensor-unit▷-star-charge abs x ⟩
              tensor-star▷ abs (rhs◦ x abs)
            ≡⟨ cong (tensor-star▷ abs) (funExt⁻ x-coh abs) ⟩
              tensor-star▷ abs (q◦ abs)
            ∎)

      bwd-fiber : (q : U (▷[ c ] (A ⊗ B))) → ●.● (fiber rhs◦ (q .◦))
      bwd-fiber q = ●.●-fiber-in rhs◦ (q .◦) (q .• , q .•→◦)

      bwd : U (▷[ c ] (A ⊗ B)) → U (A ⊗ (▷[ c ] B))
      bwd q = bwd-from-fiber (q .◦) (bwd-fiber q)

      fiber-in-fst
        : (q◦ : U (◯ᶜ (A ⊗ B)))
        → (x• : U (●ᶜ (A ⊗ B)))
        → (x-coh : rhsα x• ≡ ●.η• q◦)
        → ●.map (λ (r : fiber rhs◦ q◦) → r .fst)
            (●.●-fiber-in rhs◦ q◦ (x• , x-coh))
          ≡ x•
      fiber-in-fst q◦ =
        ●.ind R η•-case ∗-case law-case
        where
          R : U (●ᶜ (A ⊗ B)) → 𝒱
          R x• =
            (x-coh : rhsα x• ≡ ●.η• q◦)
            → ●.map (λ (r : fiber rhs◦ q◦) → r .fst)
                (●.●-fiber-in rhs◦ q◦ (x• , x-coh))
              ≡ x•
          η•-case : (x : U (A ⊗ B)) → R (●.η• x)
          η•-case x x-coh =
              ●.map (λ (r : fiber rhs◦ q◦) → r .fst)
                (●.●-fiber-in rhs◦ q◦ (●.η• x , x-coh))
            ≡⟨ ●.map-∘ (λ r → x , r) (λ (r : fiber rhs◦ q◦) → r .fst) (●.●-lex x-coh) ⟩
              ●.map (λ _ → x) (●.●-lex x-coh)
            ≡⟨ ●.●-map-const x (●.●-lex x-coh) ⟩
              ●.η• x
            ∎
          ∗-case : (abs : ⟨ ABS ⟩) → R (●.∗ abs)
          ∗-case abs x-coh = refl
          law-case
            : (x : U (A ⊗ B)) (abs : ⟨ ABS ⟩)
            → PathP (λ i → R (●.law x abs i)) (η•-case x) (∗-case abs)
          law-case x abs =
            isProp→PathP
              (λ i → isPropΠ λ x-coh →
                isProp→isSet (●.●-isProp abs)
                  (●.map (λ (r : fiber rhs◦ q◦) → r .fst)
                    (●.●-fiber-in rhs◦ q◦ (●.law x abs i , x-coh)))
                  (●.law x abs i))
              (η•-case x)
              (∗-case abs)

      fwd-tensor-unit▷-•
        : (x : U (A ⊗ B))
        → fwd .U (tensor-unit▷ x) .• ≡ ●.η• x
      fwd-tensor-unit▷-• =
        ⊛-≡ (●ᶜ (A ⊗ B) .is-set)
          (λ x → fwd .U (tensor-unit▷ x) .•)
          ●.η•
          (λ a b → refl)

      fwd-tensor-unit▷-◦
        : (x : U (A ⊗ B))
        → fwd .U (tensor-unit▷ x) .◦ ≡ rhs◦ x
      fwd-tensor-unit▷-◦ =
        ⊛-≡ (◯ᶜ (A ⊗ B) .is-set)
          (λ x → fwd .U (tensor-unit▷ x) .◦)
          rhs◦
          (λ a b → funExt λ _ → sym (cong ∣_∣₂ (law c a b)))

      fwd-tensor-star▷-•
        : (abs : ⟨ ABS ⟩) (x : U (A ⊗ B))
        → fwd .U (tensor-star▷ abs x) .• ≡ ●.∗ abs
      fwd-tensor-star▷-• abs =
        ⊛-≡ (●ᶜ (A ⊗ B) .is-set)
          (λ x → fwd .U (tensor-star▷ abs x) .•)
          (λ _ → ●.∗ abs)
          (λ a b → refl)

      fwd-tensor-star▷-◦
        : (abs : ⟨ ABS ⟩) (x : U (A ⊗ B))
        → fwd .U (tensor-star▷ abs x) .◦ ≡ η◦ x
      fwd-tensor-star▷-◦ abs =
        ⊛-≡ (◯ᶜ (A ⊗ B) .is-set)
          (λ x → fwd .U (tensor-star▷ abs x) .◦)
          η◦
          (λ a b → refl)

      fwd-bwd-fiber-•
        : (q◦ : U (◯ᶜ (A ⊗ B))) (u : ●.● (fiber rhs◦ q◦))
        → fwd .U (bwd-from-fiber q◦ u) .•
          ≡ ●.map (λ (r : fiber rhs◦ q◦) → r .fst) u
      fwd-bwd-fiber-• q◦ (●.η• (x , x-coh)) = fwd-tensor-unit▷-• x
      fwd-bwd-fiber-• q◦ (●.∗ abs) = fwd-tensor-star▷-• abs (q◦ abs)
      fwd-bwd-fiber-• q◦ (●.law (x , x-coh) abs i) =
        isProp→PathP
          (λ i → isProp→isSet (●.●-isProp abs)
            (fwd .U (bwd-from-fiber q◦ (●.law (x , x-coh) abs i)) .•)
            (●.map (λ (r : fiber rhs◦ q◦) → r .fst) (●.law (x , x-coh) abs i)))
          (fwd-bwd-fiber-• q◦ (●.η• (x , x-coh)))
          (fwd-bwd-fiber-• q◦ (●.∗ abs))
          i

      fwd-bwd-fiber-◦
        : (q◦ : U (◯ᶜ (A ⊗ B))) (u : ●.● (fiber rhs◦ q◦))
        → fwd .U (bwd-from-fiber q◦ u) .◦ ≡ q◦
      fwd-bwd-fiber-◦ q◦ (●.η• (x , x-coh)) =
          fwd .U (tensor-unit▷ x) .◦
        ≡⟨ fwd-tensor-unit▷-◦ x ⟩
          rhs◦ x
        ≡⟨ x-coh ⟩
          q◦
        ∎
      fwd-bwd-fiber-◦ q◦ (●.∗ abs) =
          fwd .U (tensor-star▷ abs (q◦ abs)) .◦
        ≡⟨ fwd-tensor-star▷-◦ abs (q◦ abs) ⟩
          η◦ (q◦ abs)
        ≡⟨ funExt (λ p → cong q◦ (str ABS abs p)) ⟩
          q◦
        ∎
      fwd-bwd-fiber-◦ q◦ (●.law (x , x-coh) abs i) =
        isProp→PathP
          (λ i → ◯ᶜ (A ⊗ B) .is-set
            (fwd .U (bwd-from-fiber q◦ (●.law (x , x-coh) abs i)) .◦)
            q◦)
          (fwd-bwd-fiber-◦ q◦ (●.η• (x , x-coh)))
          (fwd-bwd-fiber-◦ q◦ (●.∗ abs))
          i

      fwd-bwd : section (fwd .U) bwd
      fwd-bwd q =
        glue-path {A-⊤ = A ⊗ B} {A-abs = A ⊗ B} {α = CHARGE c}
          ( fwd .U (bwd q) .•
          ≡⟨ fwd-bwd-fiber-• (q .◦) (bwd-fiber q) ⟩
            ●.map (λ (r : fiber rhs◦ (q .◦)) → r .fst) (bwd-fiber q)
          ≡⟨ fiber-in-fst (q .◦) (q .•) (q .•→◦) ⟩
            q .•
          ∎)
          (fwd-bwd-fiber-◦ (q .◦) (bwd-fiber q))

      unit▷-path
        : (b : U B) (q◦ : U (◯ᶜ B))
        → (r : ▷B-rhs◦ b ≡ q◦)
        → unit▷ b ≡
            record
              { • = ●.η• b
              ; ◦ = q◦
              ; •→◦ = cong ●.η• r
              }
      unit▷-path b q◦ r =
        glue-path {A-⊤ = B} {A-abs = B} {α = CHARGE c} refl r

      unit▷∗-path
        : (abs : ⟨ ABS ⟩) (q◦ : U (◯ᶜ B))
        → (qcoh : ●ᶜ.map (CHARGE c ⨾ᶜ η◦ᶜ {A = B}) .U (●.∗ abs) ≡ ●.η• q◦)
        → unit▷∗ abs (q◦ abs) ≡
            record
              { • = ●.∗ abs
              ; ◦ = q◦
              ; •→◦ = qcoh
              }
      unit▷∗-path abs q◦ qcoh =
        glue-path {A-⊤ = B} {A-abs = B} {α = CHARGE c}
          refl
          (funExt λ p → cong q◦ (str ABS abs p))

      unit▷∗-η-path
        : (b : U B) (abs : ⟨ ABS ⟩) (q◦ : U (◯ᶜ B))
        → unit▷∗ abs (q◦ abs) ≡
            record
              { • = ●.η• b
              ; ◦ = q◦
              ; •→◦ = ●.●-unlex (●.∗ abs)
              }
      unit▷∗-η-path b abs q◦ =
        glue-path {A-⊤ = B} {A-abs = B} {α = CHARGE c}
          (sym (●.law b abs))
          (funExt λ p → cong q◦ (str ABS abs p))

      bwd-fwd-inj-•
        : (a : U A)
        → (q• : U (●ᶜ B))
        → (q◦ : U (◯ᶜ B))
        → (qcoh : ●ᶜ.map (CHARGE c ⨾ᶜ η◦ᶜ {A = B}) .U q• ≡ ●.η• q◦)
        → bwd (fwd .U ∣ inj {A} {▷[ c ] B} a (record { • = q• ; ◦ = q◦ ; •→◦ = qcoh }) ∣₂)
          ≡ ∣ inj {A} {▷[ c ] B} a (record { • = q• ; ◦ = q◦ ; •→◦ = qcoh }) ∣₂
      bwd-fwd-inj-• a =
        ●.ind R η•-case ∗-case law-case
        where
          glued▷
            : (q• : U (●ᶜ B))
            → (q◦ : U (◯ᶜ B))
            → ●ᶜ.map (CHARGE c ⨾ᶜ η◦ᶜ {A = B}) .U q• ≡ ●.η• q◦
            → U (▷[ c ] B)
          glued▷ q• q◦ qcoh =
            record
              { • = q•
              ; ◦ = q◦
              ; •→◦ = qcoh
              }

          R : U (●ᶜ B) → 𝒱
          R q• =
            (q◦ : U (◯ᶜ B))
            → (qcoh : ●ᶜ.map (CHARGE c ⨾ᶜ η◦ᶜ {A = B}) .U q• ≡ ●.η• q◦)
            → bwd (fwd .U ∣ inj {A} {▷[ c ] B} a (glued▷ q• q◦ qcoh) ∣₂)
              ≡ ∣ inj {A} {▷[ c ] B} a (glued▷ q• q◦ qcoh) ∣₂

          R-isProp : (q• : U (●ᶜ B)) → isProp (R q•)
          R-isProp q• f g =
            funExt λ q◦ →
              funExt λ qcoh →
                squash₂
                  (bwd (fwd .U ∣ inj {A} {▷[ c ] B} a (glued▷ q• q◦ qcoh) ∣₂))
                  (∣ inj {A} {▷[ c ] B} a (glued▷ q• q◦ qcoh) ∣₂)
                  (f q◦ qcoh)
                  (g q◦ qcoh)

          η•-case : (b : U B) → R (●.η• b)
          η•-case b q◦ qcoh =
            subst
              (λ h →
                bwd (fwd .U ∣ inj {A} {▷[ c ] B} a (glued▷ (●.η• b) q◦ h) ∣₂)
                ≡ ∣ inj {A} {▷[ c ] B} a (glued▷ (●.η• b) q◦ h) ∣₂)
              (●.●-unlex-lex qcoh)
              (●.ind
                (λ u →
                  bwd (fwd .U ∣ inj {A} {▷[ c ] B} a
                    (glued▷ (●.η• b) q◦ (●.●-unlex u)) ∣₂)
                  ≡ ∣ inj {A} {▷[ c ] B} a
                    (glued▷ (●.η• b) q◦ (●.●-unlex u)) ∣₂)
                (λ r →
                    bwd (fwd .U ∣ inj {A} {▷[ c ] B} a
                      (glued▷ (●.η• b) q◦ (●.●-unlex (●.η• r))) ∣₂)
                  ≡⟨ cong (λ q → bwd (fwd .U ∣ inj {A} {▷[ c ] B} a q ∣₂))
                        (sym (unit▷-path b q◦ r)) ⟩
                    bwd (fwd .U ∣ inj {A} {▷[ c ] B} a (unit▷ b) ∣₂)
                  ≡⟨ refl ⟩
                    ∣ inj {A} {▷[ c ] B} a (unit▷ b) ∣₂
                  ≡⟨ cong (λ q → ∣ inj {A} {▷[ c ] B} a q ∣₂) (unit▷-path b q◦ r) ⟩
                    ∣ inj {A} {▷[ c ] B} a
                      (glued▷ (●.η• b) q◦ (●.●-unlex (●.η• r))) ∣₂
                  ∎)
                (λ abs →
                    bwd (fwd .U ∣ inj {A} {▷[ c ] B} a
                      (glued▷ (●.η• b) q◦ (●.●-unlex (●.∗ abs))) ∣₂)
                  ≡⟨
                    cong
                      (λ abs' → ∣ inj {A} {▷[ c ] B} a (unit▷∗ abs' (q◦ abs')) ∣₂)
                      (str ABS _ abs)
                  ⟩
                    ∣ inj {A} {▷[ c ] B} a (unit▷∗ abs (q◦ abs)) ∣₂
                  ≡⟨ cong (λ q → ∣ inj {A} {▷[ c ] B} a q ∣₂) (unit▷∗-η-path b abs q◦) ⟩
                    ∣ inj {A} {▷[ c ] B} a
                      (glued▷ (●.η• b) q◦ (●.●-unlex (●.∗ abs))) ∣₂
                  ∎)
                (λ r abs →
                  isProp→PathP
                    (λ i →
                      squash₂
                        (bwd (fwd .U ∣ inj {A} {▷[ c ] B} a
                          (glued▷ (●.η• b) q◦ (●.●-unlex (●.law r abs i))) ∣₂))
                        (∣ inj {A} {▷[ c ] B} a
                          (glued▷ (●.η• b) q◦ (●.●-unlex (●.law r abs i))) ∣₂))
                    _ _)
                (●.●-lex qcoh))

          ∗-case : (abs : ⟨ ABS ⟩) → R (●.∗ abs)
          ∗-case abs q◦ qcoh =
              bwd (fwd .U ∣ inj {A} {▷[ c ] B} a (glued▷ (●.∗ abs) q◦ qcoh) ∣₂)
            ≡⟨ refl ⟩
              ∣ inj {A} {▷[ c ] B} a (unit▷∗ abs (q◦ abs)) ∣₂
            ≡⟨ cong (λ q → ∣ inj {A} {▷[ c ] B} a q ∣₂) (unit▷∗-path abs q◦ qcoh) ⟩
              ∣ inj {A} {▷[ c ] B} a (glued▷ (●.∗ abs) q◦ qcoh) ∣₂
            ∎

          law-case
            : (b : U B) (abs : ⟨ ABS ⟩)
            → PathP (λ i → R (●.law b abs i)) (η•-case b) (∗-case abs)
          law-case b abs =
            isProp→PathP (λ i → R-isProp (●.law b abs i)) (η•-case b) (∗-case abs)

      bwd-fwd : retract (fwd .U) bwd
      bwd-fwd =
        ⊛-≡ squash₂
          (bwd ∘ fwd .U)
          (λ z → z)
          (λ a q → bwd-fwd-inj-• a (q .•) (q .◦) (q .•→◦))

      fwd-equiv : isEquivᶜ fwd
      fwd-equiv = isoToIsEquiv (iso (fwd .U) bwd fwd-bwd bwd-fwd)
