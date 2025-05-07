{-# OPTIONS --cubical-compatible --safe #-}

-- Common cost monoids.

module Algebra.Cost.Instances where

open import Algebra.Cost.Structures
open import Algebra.Cost.Bundles
open import Data.Product
open import Function
open import Relation.Nullary.Negation
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; module ≡-Reasoning)


ℕ-CostMonoid : CostMonoid
ℕ-CostMonoid = record
  { ℂ = ℕ
  ; zero = zero
  ; _+_ = _+_
  ; _≤_ = _≤_
  ; isCostMonoid = record
    { isMonoid = +-0-isMonoid
    ; isPreorder = ≤-isPreorder
    ; isMonotone = record { ∙-mono-≤ = +-mono-≤ }
    }
  }
  where
    open import Data.Nat
    open import Data.Nat.Properties

ℕ⊔-CostMonoid : CostMonoid
ℕ⊔-CostMonoid = record
  { ℂ = ℕ
  ; zero = zero
  ; _+_ = _⊔_
  ; _≤_ = _≤_
  ; isCostMonoid = record
    { isMonoid = ⊔-0-isMonoid
    ; isPreorder = ≤-isPreorder
    ; isMonotone = record { ∙-mono-≤ = ⊔-mono-≤ }
    }
  }
  where
    open import Data.Nat
    open import Data.Nat.Properties

ℤ-CostMonoid : CostMonoid
ℤ-CostMonoid = record
  { ℂ = ℤ
  ; zero = 0ℤ
  ; _+_ = _+_
  ; _≤_ = _≤_
  ; isCostMonoid = record
    { isMonoid = +-0-isMonoid
    ; isPreorder = ≤-isPreorder
    ; isMonotone = record { ∙-mono-≤ = +-mono-≤ }
    }
  }
  where
    open import Data.Integer
    open import Data.Integer.Properties

ℚ-CostMonoid : CostMonoid
ℚ-CostMonoid = record
  { ℂ = ℚ
  ; zero = 0ℚ
  ; _+_ = _+_
  ; _≤_ = _≤_
  ; isCostMonoid = record
    { isMonoid = +-0-isMonoid
    ; isPreorder = ≤-isPreorder
    ; isMonotone = record { ∙-mono-≤ = +-mono-≤ }
    }
  }
  where
    open import Data.Rational
    open import Data.Rational.Properties

ResourceMonoid : CostMonoid
ResourceMonoid = record
  { ℂ = ℕ × ℕ
  ; zero = 0 , 0
  ; _+_ = _·_
  ; _≤_ = _≤ᵣ_
  ; isCostMonoid = record
    { isMonoid = record
      { isSemigroup = record
        { isMagma = record
          { isEquivalence = Eq.isEquivalence
          ; ∙-cong = Eq.cong₂ _·_
          }
        ; assoc = assoc
        }
      ; identity = identityˡ , identityʳ
      }
    ; isPreorder = record
      { isEquivalence = Eq.isEquivalence
      ; reflexive = λ { refl → (≤-refl , ≤-refl) }
      ; trans = λ (h₁ , h₂) (h₁' , h₂') → ≤-trans h₁ h₁' , ≤-trans h₂' h₂
      }
    ; isMonotone = record { ∙-mono-≤ = ∙-mono-≤ᵣ }
    }
  }
  where
    open import Data.Nat
    open import Data.Nat.Properties
    open import Data.Sum

    open ≤-Reasoning

    open import Algebra.Definitions {A = ℕ × ℕ} _≡_
    open import Relation.Binary


    _·_ : ℕ × ℕ → ℕ × ℕ → ℕ × ℕ
    (p , p') · (q , q') = p + (q ∸ p') , q' + (p' ∸ q)

    _≤ᵣ_ : ℕ × ℕ → ℕ × ℕ → Set
    (p , p') ≤ᵣ (q , q') = (p ≤ q) × (q' ≤ p')

    +-∸-comm′ : (m : ℕ) {n o : ℕ} → n ≤ o → (m + n) ∸ o ≡ m ∸ (o ∸ n)
    +-∸-comm′ m {n}     {o}     z≤n       = Eq.cong (_∸ o) (+-identityʳ m)
    +-∸-comm′ m {suc n} {suc o} (s≤s n≤o) = begin-equality
      (m + suc n) ∸ suc o  ≡⟨ Eq.cong (_∸ suc o) (+-suc m n) ⟩
      suc (m + n) ∸ suc o  ≡⟨ +-∸-comm′ m n≤o ⟩
      m ∸ (o ∸ n) ∎

    assoc : Associative _·_
    assoc (p , p') (q , q') (r , r') with ≤-total p' q | ≤-total q' r
    ... | inj₁ p'≤q | inj₁ q'≤r =
      Eq.cong₂ _,_
        (begin-equality
          (p + (q ∸ p')) + (r ∸ (q' + (p' ∸ q)))
        ≡⟨ Eq.cong (λ x → (p + (q ∸ p')) + (r ∸ (q' + x))) (m≤n⇒m∸n≡0 p'≤q) ⟩
          (p + (q ∸ p')) + (r ∸ (q' + 0))
        ≡⟨ Eq.cong (λ x → (p + (q ∸ p')) + (r ∸ x)) (+-identityʳ q') ⟩
          (p + (q ∸ p')) + (r ∸ q')
        ≡⟨ +-assoc p (q ∸ p') (r ∸ q') ⟩
          p + ((q ∸ p') + (r ∸ q'))
        ≡˘⟨ Eq.cong (p +_) (+-∸-comm (r ∸ q') p'≤q) ⟩
          p + ((q + (r ∸ q')) ∸ p')
        ∎)
        (begin-equality
          r' + ((q' + (p' ∸ q)) ∸ r)
        ≡⟨ Eq.cong (λ x → r' + ((q' + x) ∸ r)) (m≤n⇒m∸n≡0 p'≤q) ⟩
          r' + ((q' + 0) ∸ r)
        ≡⟨ Eq.cong (λ x → r' + (x ∸ r)) (+-identityʳ q') ⟩
          r' + (q' ∸ r)
        ≡˘⟨ +-identityʳ (r' + (q' ∸ r)) ⟩
          (r' + (q' ∸ r)) + 0
        ≡˘⟨ Eq.cong (λ x → (r' + (q' ∸ r)) + x) (m≤n⇒m∸n≡0 (≤-trans p'≤q (m≤m+n q (r ∸ q')))) ⟩
          (r' + (q' ∸ r)) + (p' ∸ (q + (r ∸ q')))
        ∎)
    ... | inj₁ p'≤q | inj₂ r≤q' =
      Eq.cong₂ _,_
        (begin-equality
          (p + (q ∸ p')) + (r ∸ (q' + (p' ∸ q)))
        ≡⟨ Eq.cong ((p + (q ∸ p')) +_) (m≤n⇒m∸n≡0 (≤-trans r≤q' (m≤m+n q' (p' ∸ q)))) ⟩
          (p + (q ∸ p')) + 0
        ≡⟨ +-identityʳ (p + (q ∸ p')) ⟩
          p + (q ∸ p')
        ≡˘⟨ Eq.cong (λ x → p + (x ∸ p')) (+-identityʳ q) ⟩
          p + ((q + 0) ∸ p')
        ≡˘⟨ Eq.cong (λ x → p + ((q + x) ∸ p')) (m≤n⇒m∸n≡0 r≤q') ⟩
          p + ((q + (r ∸ q')) ∸ p')
        ∎)
        (begin-equality
          r' + ((q' + (p' ∸ q)) ∸ r)
        ≡⟨ Eq.cong (λ x → r' + ((q' + x) ∸ r)) (m≤n⇒m∸n≡0 p'≤q) ⟩
          r' + ((q' + 0) ∸ r)
        ≡⟨ Eq.cong (λ x → r' + (x ∸ r)) (+-identityʳ q') ⟩
          r' + (q' ∸ r)
        ≡˘⟨ +-identityʳ (r' + (q' ∸ r)) ⟩
          (r' + (q' ∸ r)) + 0
        ≡˘⟨ Eq.cong ((r' + (q' ∸ r)) +_) (m≤n⇒m∸n≡0 (≤-trans p'≤q (m≤m+n q (r ∸ q')))) ⟩
          (r' + (q' ∸ r)) + (p' ∸ (q + (r ∸ q')))
        ∎)
    ... | inj₂ q≤p' | inj₁ q'≤r =
      Eq.cong₂ _,_
        (begin-equality
          (p + (q ∸ p')) + (r ∸ (q' + (p' ∸ q)))
        ≡⟨ Eq.cong (λ x → (p + x) + (r ∸ (q' + (p' ∸ q)))) (m≤n⇒m∸n≡0 q≤p') ⟩
          (p + 0) + (r ∸ (q' + (p' ∸ q)))
        ≡⟨ Eq.cong (_+ (r ∸ (q' + (p' ∸ q)))) (+-identityʳ p) ⟩
          p + (r ∸ (q' + (p' ∸ q)))
        ≡⟨ Eq.cong (p +_) (arithmetic p' q q' r q≤p' q'≤r) ⟩
          p + ((q + (r ∸ q')) ∸ p')
        ∎)
        (begin-equality
          r' + ((q' + (p' ∸ q)) ∸ r)
        ≡˘⟨ Eq.cong (r' +_) (arithmetic r q' q p' q'≤r q≤p') ⟩
          r' + (p' ∸ (q + (r ∸ q')))
        ≡˘⟨ Eq.cong (_+ (p' ∸ (q + (r ∸ q')))) (+-identityʳ r') ⟩
          (r' + 0) + (p' ∸ (q + (r ∸ q')))
        ≡˘⟨ Eq.cong (λ x → (r' + x) + (p' ∸ (q + (r ∸ q')))) (m≤n⇒m∸n≡0 q'≤r) ⟩
          (r' + (q' ∸ r)) + (p' ∸ (q + (r ∸ q')))
        ∎)
      where
        arithmetic : (p' q q' r : ℕ) → q ≤ p' → q' ≤ r → r ∸ (q' + (p' ∸ q)) ≡ ((q + (r ∸ q')) ∸ p')
        arithmetic p' q q' r q≤p' q'≤r =
          begin-equality
            r ∸ (q' + (p' ∸ q))
          ≡˘⟨ ∸-+-assoc r q' (p' ∸ q) ⟩
            (r ∸ q') ∸ (p' ∸ q)
          ≡˘⟨ +-∸-comm′ (r ∸ q') q≤p' ⟩
            ((r ∸ q') + q) ∸ p'
          ≡⟨ Eq.cong (_∸ p') (+-comm (r ∸ q') q) ⟩
            (q + (r ∸ q')) ∸ p'
          ∎
    ... | inj₂ q≤p' | inj₂ r≤q' =
      Eq.cong₂ _,_
        (begin-equality
          (p + (q ∸ p')) + (r ∸ (q' + (p' ∸ q)))
        ≡⟨ Eq.cong ((p + (q ∸ p')) +_) (m≤n⇒m∸n≡0 (≤-trans r≤q' (m≤m+n q' (p' ∸ q)))) ⟩
          (p + (q ∸ p')) + 0
        ≡⟨ +-identityʳ (p + (q ∸ p')) ⟩
          p + (q ∸ p')
        ≡˘⟨ Eq.cong (λ x → p + (x ∸ p')) (+-identityʳ q) ⟩
          p + ((q + 0) ∸ p')
        ≡˘⟨ Eq.cong (λ x → p + ((q + x) ∸ p')) (m≤n⇒m∸n≡0 r≤q') ⟩
          p + ((q + (r ∸ q')) ∸ p')
        ∎)
        (begin-equality
          r' + ((q' + (p' ∸ q)) ∸ r)
        ≡⟨ Eq.cong (r' +_) (+-∸-comm (p' ∸ q) r≤q') ⟩
          r' + ((q' ∸ r) + (p' ∸ q))
        ≡˘⟨ +-assoc r' (q' ∸ r) (p' ∸ q) ⟩
          (r' + (q' ∸ r)) + (p' ∸ q)
        ≡˘⟨ Eq.cong (λ x → (r' + (q' ∸ r)) + (p' ∸ x)) (+-identityʳ q) ⟩
          (r' + (q' ∸ r)) + (p' ∸ (q + 0))
        ≡˘⟨ Eq.cong (λ x → (r' + (q' ∸ r)) + (p' ∸ (q + x))) (m≤n⇒m∸n≡0 r≤q') ⟩
          (r' + (q' ∸ r)) + (p' ∸ (q + (r ∸ q')))
        ∎)

    identityˡ : LeftIdentity (0 , 0) _·_
    identityˡ (q , q') =
      Eq.cong
        (q ,_)
        (begin-equality
          q' + (0 ∸ q)
        ≡⟨ Eq.cong (q' +_) (0∸n≡0 q) ⟩
          q' + 0
        ≡⟨ +-identityʳ q' ⟩
          q'
        ∎)

    identityʳ : RightIdentity (0 , 0) _·_
    identityʳ (q , q') =
      Eq.cong
        (_, q')
        (begin-equality
          q + (0 ∸ q')
        ≡⟨ Eq.cong (q +_) (0∸n≡0 q') ⟩
          q + 0
        ≡⟨ +-identityʳ q ⟩
          q
        ∎)

    ∙-mono-≤ᵣ : _·_ Preserves₂ _≤ᵣ_ ⟶ _≤ᵣ_ ⟶ _≤ᵣ_
    ∙-mono-≤ᵣ (h₁ , h₁') (h₂ , h₂') =
      +-mono-≤ h₁ (∸-mono h₂ h₁') ,
      +-mono-≤ h₂' (∸-mono h₁' h₂)

List-CostMonoid : Set → CostMonoid
List-CostMonoid A = record
  { ℂ = List A
  ; zero = []
  ; _+_ = _++_
  ; _≤_ = _⊆_
  ; isCostMonoid = record
    { isMonoid = ++-isMonoid
    ; isPreorder = ⊆-isPreorder
    ; isMonotone = record { ∙-mono-≤ = ++⁺ }
    }
  }
  where
    open import Data.List
    open import Data.List.Properties
    open import Data.List.Relation.Binary.Sublist.Propositional
    open import Data.List.Relation.Binary.Sublist.Propositional.Properties

cm-× : CostMonoid → CostMonoid → CostMonoid
cm-× cm₁ cm₂ = record
  { ℂ = ℂ cm₁ × ℂ cm₂
  ; zero = zero cm₁ , zero cm₂
  ; _+_ = λ (a₁ , a₂) (b₁ , b₂) → _+_ cm₁ a₁ b₁ , _+_ cm₂ a₂ b₂
  ; _≤_ = λ (a₁ , a₂) (b₁ , b₂) → _≤_ cm₁ a₁ b₁ × _≤_ cm₂ a₂ b₂
  ; isCostMonoid = record
    { isMonoid = record
      { isSemigroup = record
        { isMagma = record
          { isEquivalence = Eq.isEquivalence
          ; ∙-cong = Eq.cong₂ _
          }
        ; assoc =
            λ (a₁ , a₂) (b₁ , b₂) (c₁ , c₂) →
              Eq.cong₂ _,_ (+-assoc cm₁ a₁ b₁ c₁) (+-assoc cm₂ a₂ b₂ c₂)
        }
      ; identity =
          (λ (a₁ , a₂) → Eq.cong₂ _,_ (+-identityˡ cm₁ a₁) (+-identityˡ cm₂ a₂)) ,
          (λ (a₁ , a₂) → Eq.cong₂ _,_ (+-identityʳ cm₁ a₁) (+-identityʳ cm₂ a₂))
      }
    ; isPreorder = record
      { isEquivalence = Eq.isEquivalence
      ; reflexive = λ { refl → ≤-refl cm₁ , ≤-refl cm₂ }
      ; trans = λ (h₁ , h₂) (h₁' , h₂') → ≤-trans cm₁ h₁ h₁' , ≤-trans cm₂ h₂ h₂'
      }
    ; isMonotone = record
      { ∙-mono-≤ = λ (h₁ , h₂) (h₁' , h₂') → +-mono-≤ cm₁ h₁ h₁' , +-mono-≤ cm₂ h₂ h₂'
      }
    }
  }
  where
    open CostMonoid

cm-rev : CostMonoid → CostMonoid
cm-rev cm .CostMonoid.ℂ = cm .CostMonoid.ℂ
cm-rev cm .CostMonoid.zero = cm .CostMonoid.zero
cm-rev cm .CostMonoid._+_ x y = cm .CostMonoid._+_ y x
cm-rev cm .CostMonoid._≤_ = cm .CostMonoid._≤_
cm-rev cm .CostMonoid.isCostMonoid .IsCostMonoid.isMonoid .IsMonoid.isSemigroup .IsSemigroup.isMagma .IsMagma.isEquivalence =
  cm .CostMonoid.isCostMonoid .IsCostMonoid.isMonoid .IsMonoid.isSemigroup .IsSemigroup.isMagma .IsMagma.isEquivalence
cm-rev cm .CostMonoid.isCostMonoid .IsCostMonoid.isMonoid .IsMonoid.isSemigroup .IsSemigroup.isMagma .IsMagma.∙-cong h₁ h₂ =
  cm .CostMonoid.isCostMonoid .IsCostMonoid.isMonoid .IsMonoid.isSemigroup .IsSemigroup.isMagma .IsMagma.∙-cong h₂ h₁
cm-rev cm .CostMonoid.isCostMonoid .IsCostMonoid.isMonoid .IsMonoid.isSemigroup .IsSemigroup.assoc x y z =
  Eq.sym (cm .CostMonoid.isCostMonoid .IsCostMonoid.isMonoid .IsMonoid.isSemigroup .IsSemigroup.assoc z y x)
cm-rev cm .CostMonoid.isCostMonoid .IsCostMonoid.isMonoid .IsMonoid.identity .proj₁ =
  cm .CostMonoid.isCostMonoid .IsCostMonoid.isMonoid .IsMonoid.identity .proj₂
cm-rev cm .CostMonoid.isCostMonoid .IsCostMonoid.isMonoid .IsMonoid.identity .proj₂ =
  cm .CostMonoid.isCostMonoid .IsCostMonoid.isMonoid .IsMonoid.identity .proj₁
cm-rev cm .CostMonoid.isCostMonoid .IsCostMonoid.isPreorder =
  cm .CostMonoid.isCostMonoid .IsCostMonoid.isPreorder
cm-rev cm .CostMonoid.isCostMonoid .IsCostMonoid.isMonotone .IsMonotone.∙-mono-≤ h₁ h₂ =
  IsMonotone.∙-mono-≤ (IsCostMonoid.isMonotone (CostMonoid.isCostMonoid cm)) h₂ h₁


sequentialParCostMonoid :
  (cm : CostMonoid)
  → IsCommutativeMonoid (CostMonoid.ℂ cm) (CostMonoid._+_ cm) (CostMonoid.zero cm)
  → ParCostMonoid
sequentialParCostMonoid cm isCommutativeMonoid = record
  { ℂ = ℂ
  ; 𝟘 = zero
  ; _⊕_ = _+_
  ; _⊗_ = _+_
  ; _≤_ = _≤_
  ; isParCostMonoid = record
    { isMonoid = isMonoid
    ; isCommutativeMonoid = isCommutativeMonoid
    ; isPreorder = isPreorder
    ; isMonotone-⊕ = isMonotone
    ; isMonotone-⊗ = isMonotone
    }
  }
  where open CostMonoid cm

ℕ-Work-ParCostMonoid : ParCostMonoid
ℕ-Work-ParCostMonoid = sequentialParCostMonoid ℕ-CostMonoid +-0-isCommutativeMonoid
  where open import Data.Nat.Properties using (+-0-isCommutativeMonoid)

ℕ-Span-ParCostMonoid : ParCostMonoid
ℕ-Span-ParCostMonoid = record
  { ℂ = ℕ
  ; 𝟘 = 0
  ; _⊕_ = _+_
  ; _⊗_ = _⊔_
  ; _≤_ = _≤_
  ; isParCostMonoid = record
    { isMonoid = +-0-isMonoid
    ; isCommutativeMonoid = ⊔-0-isCommutativeMonoid
    ; isPreorder = ≤-isPreorder
    ; isMonotone-⊕ = record { ∙-mono-≤ = +-mono-≤ }
    ; isMonotone-⊗ = record { ∙-mono-≤ = ⊔-mono-≤ }
    }
  }
  where
    open import Data.Nat
    open import Data.Nat.Properties

pcm-× : ParCostMonoid → ParCostMonoid → ParCostMonoid
pcm-× pcm₁ pcm₂ = record
  { ℂ = ℂ pcm₁ × ℂ pcm₂
  ; 𝟘 = 𝟘 pcm₁ , 𝟘 pcm₂
  ; _⊕_ = λ (a₁ , a₂) (b₁ , b₂) → _⊕_ pcm₁ a₁ b₁ , _⊕_ pcm₂ a₂ b₂
  ; _⊗_ = λ (a₁ , a₂) (b₁ , b₂) → _⊗_ pcm₁ a₁ b₁ , _⊗_ pcm₂ a₂ b₂
  ; _≤_ = Pointwise (_≤_ pcm₁) (_≤_ pcm₂)
  ; isParCostMonoid = record
    { isMonoid = record
      { isSemigroup = record
        { isMagma = record
          { isEquivalence = Eq.isEquivalence
          ; ∙-cong = Eq.cong₂ _
          }
        ; assoc =
            λ (a₁ , a₂) (b₁ , b₂) (c₁ , c₂) →
            Eq.cong₂ _,_ (⊕-assoc pcm₁ a₁ b₁ c₁) (⊕-assoc pcm₂ a₂ b₂ c₂)
        }
      ; identity =
          (λ (a₁ , a₂) → Eq.cong₂ _,_ (⊕-identityˡ pcm₁ a₁) (⊕-identityˡ pcm₂ a₂)) ,
          (λ (a₁ , a₂) → Eq.cong₂ _,_ (⊕-identityʳ pcm₁ a₁) (⊕-identityʳ pcm₂ a₂))
      }
    ; isCommutativeMonoid = record
      { isMonoid = record
        { isSemigroup = record
          { isMagma = record
            { isEquivalence = Eq.isEquivalence
            ; ∙-cong = Eq.cong₂ _
            }
          ; assoc =
              λ (a₁ , a₂) (b₁ , b₂) (c₁ , c₂) →
                Eq.cong₂ _,_ (⊗-assoc pcm₁ a₁ b₁ c₁) (⊗-assoc pcm₂ a₂ b₂ c₂)
          }
        ; identity =
            (λ (a₁ , a₂) → Eq.cong₂ _,_ (⊗-identityˡ pcm₁ a₁) (⊗-identityˡ pcm₂ a₂)) ,
            (λ (a₁ , a₂) → Eq.cong₂ _,_ (⊗-identityʳ pcm₁ a₁) (⊗-identityʳ pcm₂ a₂))
        }
      ; comm = λ (a₁ , a₂) (b₁ , b₂) → Eq.cong₂ _,_ (⊗-comm pcm₁ a₁ b₁) (⊗-comm pcm₂ a₂ b₂)
      }
    ; isPreorder = record
      { isEquivalence = Eq.isEquivalence
      ; reflexive = λ { refl → ≤-refl pcm₁ , ≤-refl pcm₂ }
      ; trans = λ (h₁ , h₂) (h₁' , h₂') → ≤-trans pcm₁ h₁ h₁' , ≤-trans pcm₂ h₂ h₂'
      }
    ; isMonotone-⊕ = record
      { ∙-mono-≤ = λ (h₁ , h₂) (h₁' , h₂') → ⊕-mono-≤ pcm₁ h₁ h₁' , ⊕-mono-≤ pcm₂ h₂ h₂'
      }
    ; isMonotone-⊗ = record
      { ∙-mono-≤ = λ (h₁ , h₂) (h₁' , h₂') → ⊗-mono-≤ pcm₁ h₁ h₁' , ⊗-mono-≤ pcm₂ h₂ h₂'
      }
    }
  }
  where
    open ParCostMonoid
    open import Data.Product.Relation.Binary.Pointwise.NonDependent

ℕ²-ParCostMonoid : ParCostMonoid
ℕ²-ParCostMonoid = pcm-× ℕ-Work-ParCostMonoid ℕ-Span-ParCostMonoid
