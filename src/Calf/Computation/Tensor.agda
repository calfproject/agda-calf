module Calf.Computation.Tensor where

open import Calf.Value
open import Calf.Computation
open import Calf.Core.Cost
open import Calf.Value.Product public
open import Calf.Value.Sigma public
open import Calf.Computation.Free public
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Function

data _U⊗_ (A B : 𝒞) : Type where
  inj : (a : cmp A) (b : cmp B) (c : val ℂ) → A U⊗ B
  law₁ : ∀ c c' a b → inj (A .charge c' a) b c ≡ inj a b (c +ℂ c')
  law₂ : ∀ c c' a b → inj a (B .charge c' b) c ≡ inj a b (c +ℂ c')
  squash : isSet (A U⊗ B)

chargeU⊗ : (A B : 𝒞) (c : val ℂ) → A U⊗ B → A U⊗ B
chargeU⊗ A B c (inj a b c') = inj a b (c +ℂ c')
chargeU⊗ A B c (law₁ c₁ c' a b i) =
    ( inj (A .charge c' a) b (c +ℂ c₁)
    ≡⟨ law₁ (c +ℂ c₁) c' a b ⟩
      inj a b ((c +ℂ c₁) +ℂ c')
    ≡⟨ cong (inj a b) (+ℂ-assoc c c₁ c') ⟩
      inj a b (c +ℂ (c₁ +ℂ c'))
    ∎ ) i
chargeU⊗ A B c (law₂ c₁ c' a b i) =
    ( inj a (B .charge c' b) (c +ℂ c₁)
    ≡⟨ law₂ (c +ℂ c₁) c' a b ⟩
      inj a b ((c +ℂ c₁) +ℂ c')
    ≡⟨ cong (inj a b) (+ℂ-assoc c c₁ c') ⟩
      inj a b (c +ℂ (c₁ +ℂ c'))
    ∎ ) i
chargeU⊗ A B c (squash x y p q i j) =
  squash (chargeU⊗ A B c x) (chargeU⊗ A B c y)
    (cong (chargeU⊗ A B c) p) (cong (chargeU⊗ A B c) q) i j

_⊗_ : 𝒞 → 𝒞 → 𝒞
(A ⊗ B) .U .val = A U⊗ B
(A ⊗ B) .U .isPreorder = {!   !}
(A ⊗ B) .charge c x = chargeU⊗ A B c x
(A ⊗ B) .charge/0 {x} = chargeU⊗/0 A B x
  where
    chargeU⊗/0 : ∀ (A B : 𝒞) (x : A U⊗ B) → chargeU⊗ A B 0ℂ x ≡ x
    chargeU⊗/0 A B (inj a b c) = cong (inj a b) (+ℂ-identityˡ c)
    chargeU⊗/0 A B (law₁ c c' a b i) =
      isSet→isSet' squash
        (cong (inj (A .charge c' a) b) (+ℂ-identityˡ c))
        (cong (inj a b) (+ℂ-identityˡ (c +ℂ c')))
        (λ k → chargeU⊗ A B 0ℂ (law₁ c c' a b k))
        (law₁ c c' a b)
        i
    chargeU⊗/0 A B (law₂ c c' a b i) =
      isSet→isSet' squash
        (cong (inj a (B .charge c' b)) (+ℂ-identityˡ c))
        (cong (inj a b) (+ℂ-identityˡ (c +ℂ c')))
        (λ k → chargeU⊗ A B 0ℂ (law₂ c c' a b k))
        (law₂ c c' a b)
        i
    chargeU⊗/0 A B (squash x y p q i j) =
      isSet→SquareP
        (λ k l → isProp→isSet
          (squash (chargeU⊗ A B 0ℂ (squash x y p q k l)) (squash x y p q k l)))
        (cong (chargeU⊗/0 A B) p)
        (cong (chargeU⊗/0 A B) q)
        (λ _ → chargeU⊗/0 A B x)
        (λ _ → chargeU⊗/0 A B y)
        i j
(A ⊗ B) .charge/+ {x} {c₁} {c₂} = chargeU⊗/+ A B c₁ c₂ x
  where
    chargeU⊗/+ : ∀ (A B : 𝒞) (c₁ c₂ : val ℂ) (x : A U⊗ B)
               → chargeU⊗ A B (c₁ +ℂ c₂) x ≡ chargeU⊗ A B c₁ (chargeU⊗ A B c₂ x)
    chargeU⊗/+ A B c₁ c₂ (inj a b c) = cong (inj a b) (+ℂ-assoc c₁ c₂ c)
    chargeU⊗/+ A B c₁ c₂ (law₁ c c' a b i) =
      isSet→isSet' squash
        (cong (inj (A .charge c' a) b) (+ℂ-assoc c₁ c₂ c))
        (cong (inj a b) (+ℂ-assoc c₁ c₂ (c +ℂ c')))
        (λ k → chargeU⊗ A B (c₁ +ℂ c₂) (law₁ c c' a b k))
        (λ k → chargeU⊗ A B c₁ (chargeU⊗ A B c₂ (law₁ c c' a b k)))
        i
    chargeU⊗/+ A B c₁ c₂ (law₂ c c' a b i) =
      isSet→isSet' squash
        (cong (inj a (B .charge c' b)) (+ℂ-assoc c₁ c₂ c))
        (cong (inj a b) (+ℂ-assoc c₁ c₂ (c +ℂ c')))
        (λ k → chargeU⊗ A B (c₁ +ℂ c₂) (law₂ c c' a b k))
        (λ k → chargeU⊗ A B c₁ (chargeU⊗ A B c₂ (law₂ c c' a b k)))
        i
    chargeU⊗/+ A B c₁ c₂ (squash x y p q i j) =
      isSet→SquareP
        (λ k l → isProp→isSet
          (squash (chargeU⊗ A B (c₁ +ℂ c₂) (squash x y p q k l))
                  (chargeU⊗ A B c₁ (chargeU⊗ A B c₂ (squash x y p q k l)))))
        (cong (chargeU⊗/+ A B c₁ c₂) p)
        (cong (chargeU⊗/+ A B c₁ c₂) q)
        (λ _ → chargeU⊗/+ A B c₁ c₂ x)
        (λ _ → chargeU⊗/+ A B c₁ c₂ y)
        i j

_∥_ : cmp A → cmp B → cmp (A ⊗ B)
a ∥ b = inj a b 0ℂ

opaque
  unfolding F

  leftF : (val X → cmp (F Y)) → (F X ⊸ F Y)
  leftF k = bind' id⊸ k

  rightF : (F X ⊸ F Y) → val X → cmp (F Y)
  rightF {X} f a = f .U (ret {X} a)

  right-leftF : (k : val X → cmp (F Y)) (a : val X)
            → rightF {X} {Y} (leftF k) a ≡ k a
  right-leftF {Y = Y} k a = F Y .charge/0

  F⊗-fwd : (F X ⊗ F Y) ⊸ F (X ×ᵛ Y)
  F⊗-fwd .U (inj (cx , x) (cy , y) c) = c +ℂ (cx +ℂ cy) , x , y
  F⊗-fwd .U (law₁ c c' (cx , x) (cy , y) i) =
    ( cong (c +ℂ_) (+ℂ-assoc c' cx cy)
      ∙ sym (+ℂ-assoc c c' (cx +ℂ cy))) i
    , x , y
  F⊗-fwd .U (law₂ c c' (cx , x) (cy , y) i) =
    ( cong (c +ℂ_) (sym (+ℂ-assoc cx c' cy))
      ∙ cong (λ z → c +ℂ (z +ℂ cy)) (+ℂ-comm cx c')
      ∙ cong (c +ℂ_) (+ℂ-assoc c' cx cy)
      ∙ sym (+ℂ-assoc c c' (cx +ℂ cy)) ) i
    , x , y
  F⊗-fwd .U (squash e e₁ x y i i₁) = {!   !}
  F⊗-fwd .charge = {!   !}

  F⊗-bwd : F (X ×ᵛ Y) ⊸ (F X ⊗ F Y)
  F⊗-bwd .U (c , x , y) = inj (0ℂ , x) (0ℂ , y) c
  F⊗-bwd .charge c (c' , x , y) = refl

par : cmp (F X) → cmp (F Y) → cmp (F (X ×ᵛ Y))
par ex ey = F⊗-fwd .U (ex ∥ ey)
