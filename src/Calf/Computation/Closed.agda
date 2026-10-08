module Calf.Computation.Closed where

open import Calf.Value
open import Calf.Computation
open import Calf.Computation.Copower

open import Calf.Value.Closed as ● public
  hiding (map; join; bind; rec)

●ᶜ : 𝒞 → 𝒞
●ᶜ A .U = ● (A .U)
●ᶜ A .is-preorder = isPreorder● (A .is-preorder)
●ᶜ A .charge = ●.map ∘ A .charge
●ᶜ A .charge-0 {a•} =
  cong (λ e → ●.map e a•) (funExt (λ _ → A .charge-0))
  ∙ sym (●.map-id a•)
●ᶜ A .charge-+ {a•} {c₁} {c₂} =
  cong (λ e → ●.map e a•) (funExt (λ _ → A .charge-+))
  ∙ sym (●.map-∘ (A .charge c₂) (A .charge c₁) a•)

η•ᶜ : A ⊸ ●ᶜ A
η•ᶜ .U = η•
η•ᶜ .charge _ _ = refl

isModalᶜ : 𝒞 → 𝒱
isModalᶜ A = isModal (U A)

𝒞• : 𝒱₁
𝒞• = 𝒞WithStr isModalᶜ

𝒞•-path : {A• B• : 𝒞•} → ⟨ A• ⟩ᶜ ≡ ⟨ B• ⟩ᶜ → A• ≡ B•
𝒞•-path p = Σ≡Prop (λ A → isPropIsEquiv (η•ᶜ {A} .U)) p

●ᶜ• : 𝒞 → 𝒞•
●ᶜ• A = ●ᶜ A , isModal●

U• : 𝒞• → 𝒱•
U• A• .fst = ⟨ A• ⟩ᶜ .U
U• A• .snd = A• .snd

map : (A ⊸ B) → (●ᶜ A ⊸ ●ᶜ B)
map f .U = ●.map (f .U)
map f .charge c = elim (λ _ → isModal●≡) (cong η• ∘ f .charge c)

●ᶜ-≃ : A ≃ᶜ B → ●ᶜ A ≃ᶜ ●ᶜ B
●ᶜ-≃ e = map (equivFunᶜ e) , equivIsEquiv (●-≃ (U-≃ e))

join : ●ᶜ (●ᶜ A) ⊸ ●ᶜ A
join .U = ●.join
join .charge c = elim (λ _ → isModal●≡) λ _ → ●.join-identityˡ

bind : (A ⊸ ●ᶜ B) → (●ᶜ A ⊸ ●ᶜ B)
bind f = map f ⨾ᶜ join

rec : (B• : 𝒞•) → (A ⊸ ⟨ B• ⟩ᶜ) → (●ᶜ A ⊸ ⟨ B• ⟩ᶜ)
rec B• f .U = ●.rec (strᶜ B•) (f .U)
rec {A} B• f .charge c =
  η-ext (const (strᶜ B•)) λ a →
    rec-β (strᶜ B•) {f .U} (A .charge c a)
    ∙ f .charge c a
    ∙ cong (⟨ B• ⟩ᶜ .charge c) (sym (rec-β (strᶜ B•) {f .U} a))

∘ηᶜ-≃ : (B• : 𝒞•) → (●ᶜ A ⊸ ⟨ B• ⟩ᶜ) ≃ (A ⊸ ⟨ B• ⟩ᶜ)
∘ηᶜ-≃ B• =
  isoToEquiv
    (iso
      (η•ᶜ ⨾ᶜ_)
      (rec B•)
      (λ f → funExtᶜ (rec-β (strᶜ B•)))
      (λ g → funExtᶜ (η-ext (const (strᶜ B•)) (rec-β (strᶜ B•)))))

{-
private
  embed : ∀ {X A} → Σᶜ₌ X A .U → Σᶜ₌ X (●ᶜ ∘ A) .U
  embed (x , a) = x , η• a

Σᶜ-●ᶜ-fwd : (X : 𝒱₌) (A : ⟨ X ⟩ → 𝒞) → ●ᶜ (Σᶜ₌ X A) ⊸ ●ᶜ (Σᶜ₌ X (●ᶜ ∘ A))
Σᶜ-●ᶜ-fwd X A = map (Σᶜ-map (λ _ → η•ᶜ))

Σᶜ-●ᶜ-fwd-equiv : (X : 𝒱₌) (A : ⟨ X ⟩ → 𝒞) → isEquivᶜ (Σᶜ-●ᶜ-fwd X A)
Σᶜ-●ᶜ-fwd-equiv X A =
  subst isEquiv (funExt⁻ ●.map′≡map (embed {X} {A})) (invEquiv ●Σ●≃●Σ .snd)

Σᶜ-●ᶜ : (X : 𝒱₌) (A : ⟨ X ⟩ → 𝒞) → ●ᶜ (Σᶜ₌ X A) ≡ ●ᶜ (Σᶜ₌ X (●ᶜ ∘ A))
Σᶜ-●ᶜ X A =
  conservativity (Σᶜ-●ᶜ-fwd X A) (Σᶜ-●ᶜ-fwd-equiv X A)
-}
