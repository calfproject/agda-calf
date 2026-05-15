{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Relation.Binary

module Calf.Directed (BEH : Type) (BEH-isProp : isProp BEH) (𝕀 : Type) (𝕀0 𝕀1 : 𝕀) (𝕀-isAlgorithmic : BEH → isContr 𝕀) where

private
  variable X Y : Type

_⊑_ : X → X → Type
_⊑_ {X} x x' = ∃[ path ∈ (𝕀 → X) ] (path 𝕀0 ≡ x) × (path 𝕀1 ≡ x')

⊑-isProp : {x x' : X} → isProp (x ⊑ x')
⊑-isProp = squash₁

⊑-syntax : X → X → Type
⊑-syntax {X} = _⊑_ {X}

-- syntax ⊑-syntax {X} x x' = x ⊑[ X ] x'


open BinaryRelation

≡⇒⊑ : {x x' : X} → x ≡ x' → x ⊑ x'
≡⇒⊑ {x = x} x≡x' = ∣ const x , refl , x≡x' ∣₁

⊑-refl : isRefl (_⊑_ {X})
⊑-refl x = ≡⇒⊑ refl

⊑-mono : (f : X → Y) {x x' : X} → x ⊑ x' → f x ⊑ f x'
⊑-mono f = map λ (path , path₀ , path₁) → f ∘ path , cong f path₀ , cong f path₁

⊑-beh : BEH → isEquiv (≡⇒⊑ {X})
⊑-beh beh .equiv-proof x⊑x' .fst .fst = {! 𝕀-isAlgorithmic beh  !}
⊑-beh beh .equiv-proof x⊑x' .fst .snd = {!   !}
⊑-beh beh .equiv-proof x⊑x' .snd = {!   !}

record SyntheticPreorder : Type₁ where
  field
    isPreorder : Type → Type
    isPreorder-isProp : isProp (isPreorder X)
    P : Type → Type
    P-isPreorder : isPreorder (P X)

  TypeP : Type₁
  TypeP = Σ[ X ∈ Type ] isPreorder X

  field
    η : X → P X
    ortho : isPreorder Y → isEquiv {A = P X → Y} {B = X → Y} (_∘ η)

  field
    ⊑-trans : isPreorder X → isTrans (_⊑_ {X})
    ⊑-funext : {Y : X → Type}
      → (∀ x → isPreorder (Y x))
      → (f f' : (x : X) → Y x)
      → ((x : X) → f x ⊑ f' x)
      → f ⊑ f'


module _ where
  open SyntheticPreorder

  SyntheticPreorderPath : SyntheticPreorder
  SyntheticPreorderPath = {!   !}

-- open import Calf.Prelude
-- open import Calf.CBPV
-- open import Relation.Binary.PropositionalEquality

-- open import Relation.Binary.Core
-- open import Relation.Binary.Definitions
-- open import Relation.Binary.Structures

-- -- Directed ordering on positive types.

-- infix 4 _≤⁺_
-- postulate
--   _≤⁺_ : val A → val A → □
--   ≤⁺-isPreorder : IsPreorder _≡_ (_≤⁺_ {A})

--   ≤⁺-mono : (f : val A → val B) →
--     f Preserves (_≤⁺_ {A}) ⟶ (_≤⁺_ {B})

-- ≤⁺-reflexive : _≡_ ⇒ _≤⁺_ {A}
-- ≤⁺-reflexive = IsPreorder.reflexive ≤⁺-isPreorder

-- ≤⁺-refl : Reflexive (_≤⁺_ {A})
-- ≤⁺-refl = IsPreorder.refl ≤⁺-isPreorder

-- ≤⁺-trans : Transitive (_≤⁺_ {A})
-- ≤⁺-trans = IsPreorder.trans ≤⁺-isPreorder

-- ≤⁺-mono₂ : (f : val A → val B → val C) →
--   f Preserves₂ (_≤⁺_ {A}) ⟶ (_≤⁺_ {B}) ⟶ (_≤⁺_ {C})
-- ≤⁺-mono₂ f a≤a' b≤b' =
--   ≤⁺-trans
--   (≤⁺-mono (f _) b≤b')
--   (≤⁺-mono (λ a → f a _) a≤a')

-- ≤⁺-syntax : val A → val A → □
-- ≤⁺-syntax {A} = _≤⁺_ {A}

-- syntax ≤⁺-syntax {A} a a' = a ≤⁺[ A ] a'


-- -- Directed ordering on negative types.
-- -- Since `cmp X = val (U X)`, derived form in terms of ordering on positive types.

-- infix 4 _≤⁻_
-- _≤⁻_ : cmp X → cmp X → □
-- _≤⁻_ {X} e e' = e ≤⁺[ U X ] e'

-- ≤⁻-isPreorder : IsPreorder _≡_ (_≤⁻_ {X})
-- ≤⁻-isPreorder {X} =
--   record
--     { isEquivalence = IsPreorder.isEquivalence (≤⁺-isPreorder {U X})
--     ; reflexive = ≤⁺-reflexive
--     ; trans = ≤⁺-trans
--     }

-- ≤⁻-mono : (f : cmp X → cmp Y) →
--   f Preserves (_≤⁻_ {X}) ⟶ (_≤⁻_ {Y})
-- ≤⁻-mono = ≤⁺-mono

-- ≤⁻-mono₂ : (f : cmp X → cmp Y → cmp Z) →
--   f Preserves₂ (_≤⁻_ {X}) ⟶ (_≤⁻_ {Y}) ⟶ (_≤⁻_ {Z})
-- ≤⁻-mono₂ = ≤⁺-mono₂

-- postulate
--   λ-mono-≤⁻ : {X : val A → tp⁻} {f f' : (a : val A) → cmp (X a)}
--     → ((a : val A) → _≤⁻_ {X a} (f a) (f' a))
--     → _≤⁻_ {Π A X} f f'

-- ≤⁻-reflexive : _≡_ ⇒ _≤⁻_ {X}
-- ≤⁻-reflexive = IsPreorder.reflexive ≤⁻-isPreorder

-- ≤⁻-refl : Reflexive (_≤⁻_ {X})
-- ≤⁻-refl = IsPreorder.refl ≤⁻-isPreorder

-- ≤⁻-trans : Transitive (_≤⁻_ {X})
-- ≤⁻-trans = IsPreorder.trans ≤⁻-isPreorder

-- ≤⁻-syntax : cmp X → cmp X → □
-- ≤⁻-syntax {X} = _≤⁻_ {X}

-- syntax ≤⁻-syntax {X} e e' = e ≤⁻[ X ] e'


-- bind-mono-≤⁻ : {e e' : cmp (F A)} {f f' : val A → cmp X}
--   → e ≤⁻[ F A ] e'
--   → f ≤⁻[ Π A (λ _ → X) ] f'
--   → (bind {A} X e f) ≤⁻[ X ] (bind {A} X e' f')
-- bind-mono-≤⁻ {A} {X} {e' = e'} {f} {f'} e≤e' f≤f' =
--   ≤⁻-trans
--     (≤⁻-mono (λ e → bind {A} X e f) e≤e')
--     (≤⁻-mono {Π A (λ _ → X)} {X} (bind {A} X e') {f} {f'} f≤f')

-- bind-monoˡ-≤⁻ : {e e' : cmp (F A)} (f : val A → cmp X)
--   → e ≤⁻[ F A ] e'
--   → (bind {A} X e f) ≤⁻[ X ] (bind {A} X e' f)
-- bind-monoˡ-≤⁻ f e≤e' = bind-mono-≤⁻ e≤e' ≤⁻-refl

-- bind-monoʳ-≤⁻ : (e : cmp (F A)) {f f' : val A → cmp X}
--   → ((a : val A) → (f a) ≤⁻[ X ] (f' a))
--   → (bind {A} X e f) ≤⁻[ X ] (bind {A} X e f')
-- bind-monoʳ-≤⁻ e f≤f' = bind-mono-≤⁻ (≤⁻-refl {x = e}) (λ-mono-≤⁻ f≤f')

-- bind-irr-mono-≤⁻ : {e₁ e₁' : cmp (F A)} {e₂ e₂' : cmp X}
--   → e₁ ≤⁻[ F A ] e₁'
--   → e₂ ≤⁻[ X ] e₂'
--   → (bind {A} X e₁ λ _ → e₂) ≤⁻[ X ] (bind {A} X e₁' λ _ → e₂')
-- bind-irr-mono-≤⁻ e₁≤e₁' e₂≤e₂' =
--   bind-mono-≤⁻ e₁≤e₁' (λ-mono-≤⁻ λ a → e₂≤e₂')

-- bind-irr-monoˡ-≤⁻ : {e₁ e₁' : cmp (F A)} {e₂ : cmp X}
--   → e₁ ≤⁻[ F A ] e₁'
--   → (bind {A} X e₁ λ _ → e₂) ≤⁻[ X ] (bind {A} X e₁' λ _ → e₂)
-- bind-irr-monoˡ-≤⁻ e₁≤e₁' =
--   bind-irr-mono-≤⁻ e₁≤e₁' ≤⁻-refl


-- open import Level using (0ℓ)
-- open import Relation.Binary using (Preorder)
-- open import Relation.Binary.Structures

-- ≤⁻-preorder : tp⁻ → Preorder 0ℓ 0ℓ 0ℓ
-- Preorder.Carrier (≤⁻-preorder X) = cmp X
-- Preorder._≈_ (≤⁻-preorder X) = _≡_
-- Preorder._≲_ (≤⁻-preorder X) = _≤⁻_ {X}
-- Preorder.isPreorder (≤⁻-preorder X) = ≤⁻-isPreorder {X}

-- module ≤⁻-Reasoning (X : tp⁻) where
--   open import Relation.Binary.Reasoning.Preorder (≤⁻-preorder X) public
