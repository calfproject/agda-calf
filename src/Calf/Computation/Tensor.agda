open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_; fiber)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Foundations.CartesianKanOps
open import Cubical.Foundations.Univalence using (ua)

module Calf.Computation.Tensor where

open import Calf.Value
open import Calf.Computation
open import Calf.Core.Cost
open import Calf.Core.Abstract
open import Calf.Value.Product
open import Calf.Value.Sigma
open import Calf.Value.Unit
open import Calf.Value.Closed as ●ᵛ
open import Calf.Computation.Free
open import Calf.Computation.Open as ◯ᶜ
open import Calf.Computation.Closed as ●ᶜ
open import Calf.Computation.Glue
open import Calf.Computation.Potential

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
(A ⊗ B) .U .is-set = squash
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

  F⊗-fwd : (F X ⊗ F Y) ⊸ F (X ×ᵛ Y)
  F⊗-fwd {X} {Y} = record { U = f ; charge = chargeF }
    where
      f : cmp (F X ⊗ F Y) → cmp (F (X ×ᵛ Y))
      f (inj (cx , x) (cy , y) c) = c +ℂ (cx +ℂ cy) , x , y
      f (law₁ c c' (cx , x) (cy , y) i) =
        ( c +ℂ ((c' +ℂ cx) +ℂ cy)
        ≡⟨ cong (c +ℂ_) (+ℂ-assoc c' cx cy) ⟩
          c +ℂ (c' +ℂ (cx +ℂ cy))
        ≡⟨ sym (+ℂ-assoc c c' (cx +ℂ cy)) ⟩
          (c +ℂ c') +ℂ (cx +ℂ cy)
        ∎) i
        , x , y
      f (law₂ c c' (cx , x) (cy , y) i) =
        ( c +ℂ (cx +ℂ (c' +ℂ cy))
        ≡⟨ cong (c +ℂ_) (sym (+ℂ-assoc cx c' cy)) ⟩
          c +ℂ ((cx +ℂ c') +ℂ cy)
        ≡⟨ cong (λ z → c +ℂ (z +ℂ cy)) (+ℂ-comm cx c') ⟩
          c +ℂ ((c' +ℂ cx) +ℂ cy)
        ≡⟨ cong (c +ℂ_) (+ℂ-assoc c' cx cy) ⟩
          c +ℂ (c' +ℂ (cx +ℂ cy))
        ≡⟨ sym (+ℂ-assoc c c' (cx +ℂ cy)) ⟩
          (c +ℂ c') +ℂ (cx +ℂ cy)
        ∎) i
        , x , y
      f (squash e e₁ p q i j) =
        isSet→SquareP (λ _ _ → isSet× (ℂ .is-set) (isSet× (X .is-set) (Y .is-set)))
          (cong f p) (cong f q)
          (λ _ → f e) (λ _ → f e₁)
          i j

      chargeF : (c : val ℂ) (a : cmp (F X ⊗ F Y))
        → f ((F X ⊗ F Y) .charge c a) ≡ F (X ×ᵛ Y) .charge c (f a)
      chargeF c (inj (cx , x) (cy , y) c') =
        cong (_, x , y) (+ℂ-assoc c c' (cx +ℂ cy))
      chargeF c (law₁ c' c'' (cx , x) (cy , y) i) =
        isSet→isSet' (isSet× (ℂ .is-set) (isSet× (X .is-set) (Y .is-set)))
          (cong (_, x , y) (+ℂ-assoc c c' ((c'' +ℂ cx) +ℂ cy)))
          (cong (_, x , y) (+ℂ-assoc c (c' +ℂ c'') (cx +ℂ cy)))
          (λ k → f (chargeU⊗ (F X) (F Y) c (law₁ c' c'' (cx , x) (cy , y) k)))
          (λ k → F (X ×ᵛ Y) .charge c (f (law₁ c' c'' (cx , x) (cy , y) k)))
          i
      chargeF c (law₂ c' c'' (cx , x) (cy , y) i) =
        isSet→isSet' (isSet× (ℂ .is-set) (isSet× (X .is-set) (Y .is-set)))
          (cong (_, x , y) (+ℂ-assoc c c' (cx +ℂ (c'' +ℂ cy))))
          (cong (_, x , y) (+ℂ-assoc c (c' +ℂ c'') (cx +ℂ cy)))
          (λ k → f (chargeU⊗ (F X) (F Y) c (law₂ c' c'' (cx , x) (cy , y) k)))
          (λ k → F (X ×ᵛ Y) .charge c (f (law₂ c' c'' (cx , x) (cy , y) k)))
          i
      chargeF c (squash x y p q i j) =
        isSet→SquareP
          (λ k l → isProp→isSet
            (isSet× (ℂ .is-set) (isSet× (X .is-set) (Y .is-set))
              (f ((F X ⊗ F Y) .charge c (squash x y p q k l)))
              (F (X ×ᵛ Y) .charge c (f (squash x y p q k l)))))
          (cong (chargeF c) p) (cong (chargeF c) q)
          (λ _ → chargeF c x) (λ _ → chargeF c y)
          i j

  F⊗-bwd : F (X ×ᵛ Y) ⊸ (F X ⊗ F Y)
  F⊗-bwd .U (c , x , y) = inj (0ℂ , x) (0ℂ , y) c
  F⊗-bwd .charge c (c' , x , y) = refl

par : cmp (F X) → cmp (F Y) → cmp (F (X ×ᵛ Y))
par ex ey = F⊗-fwd .U (ex ∥ ey)


⊤ : 𝒞
⊤ = F 1ᵛ

map₂ : ∀ {A₁ A₂ B₁ B₂}
  → (A₁ ⊸ B₁)
  → (A₂ ⊸ B₂)
  → (A₁ ⊗ A₂ ⊸ B₁ ⊗ B₂)
map₂ {A₁} {A₂} {B₁} {B₂} f g =
  record { U = h ; charge = h-charge }
  where
    h : A₁ U⊗ A₂ → B₁ U⊗ B₂
    h (inj a b c) = inj (f .U a) (g .U b) c
    h (law₁ c c' a b i) =
      ( inj (f .U (A₁ .charge c' a)) (g .U b) c
      ≡⟨ cong (λ a' → inj a' (g .U b) c) (f .charge c' a) ⟩
        inj (B₁ .charge c' (f .U a)) (g .U b) c
      ≡⟨ law₁ c c' (f .U a) (g .U b) ⟩
        inj (f .U a) (g .U b) (c +ℂ c')
      ∎) i
    h (law₂ c c' a b i) =
      ( inj (f .U a) (g .U (A₂ .charge c' b)) c
      ≡⟨ cong (λ b' → inj (f .U a) b' c) (g .charge c' b) ⟩
        inj (f .U a) (B₂ .charge c' (g .U b)) c
      ≡⟨ law₂ c c' (f .U a) (g .U b) ⟩
        inj (f .U a) (g .U b) (c +ℂ c')
      ∎) i
    h (squash x y p q i j) =
      squash (h x) (h y) (cong h p) (cong h q) i j

    h-charge
      : (c : val ℂ) (x : A₁ U⊗ A₂)
      → h ((A₁ ⊗ A₂) .charge c x) ≡ (B₁ ⊗ B₂) .charge c (h x)
    h-charge c (inj a b c') = refl
    h-charge c (law₁ c₁ c' a b i) =
      isSet→isSet'
        squash
        (h-charge c (inj (A₁ .charge c' a) b c₁))
        (h-charge c (inj a b (c₁ +ℂ c')))
        (λ k → h ((A₁ ⊗ A₂) .charge c (law₁ c₁ c' a b k)))
        (λ k → (B₁ ⊗ B₂) .charge c (h (law₁ c₁ c' a b k)))
        i
    h-charge c (law₂ c₁ c' a b i) =
      isSet→isSet'
        squash
        (h-charge c (inj a (A₂ .charge c' b) c₁))
        (h-charge c (inj a b (c₁ +ℂ c')))
        (λ k → h ((A₁ ⊗ A₂) .charge c (law₂ c₁ c' a b k)))
        (λ k → (B₁ ⊗ B₂) .charge c (h (law₂ c₁ c' a b k)))
        i
    h-charge c (squash x y p q i j) =
      isSet→SquareP
        (λ k l → isProp→isSet
          (squash
            (h ((A₁ ⊗ A₂) .charge c (squash x y p q k l)))
            ((B₁ ⊗ B₂) .charge c (h (squash x y p q k l)))))
        (cong (h-charge c) p)
        (cong (h-charge c) q)
        (λ _ → h-charge c x)
        (λ _ → h-charge c y)
        i j

opaque
  unfolding F  -- TODO: remove?

  ⊗-identityʳ : A ⊗ ⊤ ≡ A
  ⊗-identityʳ {A = A} =
    𝒞-path
      (𝒱-path (ua tensor⊤≃))
      (charge-path tensor⊤≃ ((A ⊗ ⊤) .charge) (A .charge) fwd-charge)
    where
      fwd : A U⊗ ⊤ → cmp A
      fwd (inj a b c) = bind' {X = 1ᵛ} {A = A} (λ _ → A .charge c a) .U b
      fwd (law₁ c c' a b i) =
        ( bind' {X = 1ᵛ} {A = A} (λ _ → A .charge c (A .charge c' a)) .U b
        ≡⟨ cong (λ f → bind' {X = 1ᵛ} {A = A} f .U b)
              (funExt λ _ → sym (A .charge/+ {a = a} {c₁ = c} {c₂ = c'})) ⟩
          bind' {X = 1ᵛ} {A = A} (λ _ → A .charge (c +ℂ c') a) .U b
        ∎) i
      fwd (law₂ c c' a b i) =
        ( bind' {X = 1ᵛ} {A = A} (λ _ → A .charge c a) .U (⊤ .charge c' b)
        ≡⟨ sym (bind'-charge {X = 1ᵛ} {A = A} (λ _ → A .charge c a) c' b) ⟩
          bind' {X = 1ᵛ} {A = A} (λ _ → A .charge c' (A .charge c a)) .U b
        ≡⟨ cong (λ f → bind' {X = 1ᵛ} {A = A} f .U b)
              (funExt λ _ → sym (A .charge/+ {a = a} {c₁ = c'} {c₂ = c})) ⟩
          bind' {X = 1ᵛ} {A = A} (λ _ → A .charge (c' +ℂ c) a) .U b
        ≡⟨ cong (λ d → bind' {X = 1ᵛ} {A = A} (λ _ → A .charge d a) .U b)
              (+ℂ-comm c' c) ⟩
          bind' {X = 1ᵛ} {A = A} (λ _ → A .charge (c +ℂ c') a) .U b
        ∎) i
      fwd (squash e e' h h' i j) =
        A .U .is-set (fwd e) (fwd e') (cong fwd h) (cong fwd h') i j

      -- type annotation purpose
      module _ where
        inj⊤ : cmp A → cmp ⊤ → val ℂ → A U⊗ ⊤
        inj⊤ = inj

        law₁⊤
          : (c c' : val ℂ) (a : cmp A) (b : cmp ⊤)
          → inj⊤ (A .charge c' a) b c ≡ inj⊤ a b (c +ℂ c')
        law₁⊤ = law₁

        law₂⊤
          : (c c' : val ℂ) (a : cmp A) (b : cmp ⊤)
          → inj⊤ a (⊤ .charge c' b) c ≡ inj⊤ a b (c +ℂ c')
        law₂⊤ = law₂

        squash⊤ : isSet (A U⊗ ⊤)
        squash⊤ = squash

      fwd-charge
        : (c : val ℂ) (x : A U⊗ ⊤)
        → fwd ((A ⊗ ⊤) .charge c x) ≡ A .charge c (fwd x)
      fwd-charge c (inj a (cb , tt) c') =
          A .charge cb (A .charge (c +ℂ c') a)
        ≡⟨ cong (A .charge cb) (A .charge/+ {a = a} {c₁ = c} {c₂ = c'}) ⟩
          A .charge cb (A .charge c (A .charge c' a))
        ≡⟨ CHARGE {A = A} cb .charge c (A .charge c' a) ⟩
          A .charge c (A .charge cb (A .charge c' a))
        ∎
      fwd-charge c (law₁ c₁ c' a b i) =
        isSet→isSet'
          (A .U .is-set)
          (fwd-charge c (inj⊤ (A .charge c' a) b c₁))
          (fwd-charge c (inj⊤ a b (c₁ +ℂ c')))
          (λ k → fwd ((A ⊗ ⊤) .charge c (law₁⊤ c₁ c' a b k)))
          (λ k → A .charge c (fwd (law₁⊤ c₁ c' a b k)))
          i
      fwd-charge c (law₂ c₁ c' a b i) =
        isSet→isSet'
          (A .U .is-set)
          (fwd-charge c (inj⊤ a (⊤ .charge c' b) c₁))
          (fwd-charge c (inj⊤ a b (c₁ +ℂ c')))
          (λ k → fwd ((A ⊗ ⊤) .charge c (law₂⊤ c₁ c' a b k)))
          (λ k → A .charge c (fwd (law₂⊤ c₁ c' a b k)))
          i
      fwd-charge c (squash x y p q i j) =
        isSet→SquareP
          (λ k l → isProp→isSet
            (A .U .is-set
              (fwd ((A ⊗ ⊤) .charge c (squash⊤ x y p q k l)))
              (A .charge c (fwd (squash⊤ x y p q k l)))))
          (cong (fwd-charge c) p)
          (cong (fwd-charge c) q)
          (λ _ → fwd-charge c x)
          (λ _ → fwd-charge c y)
          i j

      bwd : cmp A → A U⊗ ⊤
      bwd a = inj⊤ a (ret {X = 1ᵛ} tt) 0ℂ

      fwd-bwd : section fwd bwd
      fwd-bwd a =
          bind' {X = 1ᵛ} {A = A} (λ _ → A .charge 0ℂ a) .U (ret {X = 1ᵛ} tt)
        ≡⟨ bind'/β {X = 1ᵛ} {A = A} ⟩
          A .charge 0ℂ a
        ≡⟨ A .charge/0 {a = a} ⟩
          a
        ∎

      bwd-fwd : retract fwd bwd
      bwd-fwd (inj a (cb , tt) c) =
          inj⊤ (A .charge cb (A .charge c a)) (ret {X = 1ᵛ} tt) 0ℂ
        ≡⟨ cong (λ z → inj⊤ z (ret {X = 1ᵛ} tt) 0ℂ)
              (sym (A .charge/+ {a = a} {c₁ = cb} {c₂ = c})) ⟩
          inj⊤ (A .charge (cb +ℂ c) a) (ret {X = 1ᵛ} tt) 0ℂ
        ≡⟨ law₁⊤ 0ℂ (cb +ℂ c) a (ret {X = 1ᵛ} tt) ⟩
          inj⊤ a (ret {X = 1ᵛ} tt) (0ℂ +ℂ (cb +ℂ c))
        ≡⟨ cong (inj⊤ a (ret {X = 1ᵛ} tt)) (+ℂ-identityˡ (cb +ℂ c)) ⟩
          inj⊤ a (ret {X = 1ᵛ} tt) (cb +ℂ c)
        ≡⟨ cong (inj⊤ a (ret {X = 1ᵛ} tt)) (+ℂ-comm cb c) ⟩
          inj⊤ a (ret {X = 1ᵛ} tt) (c +ℂ cb)
        ≡⟨ sym (law₂⊤ c cb a (ret {X = 1ᵛ} tt)) ⟩
          inj⊤ a (⊤ .charge cb (ret {X = 1ᵛ} tt)) c
        ≡⟨ cong (λ d → inj⊤ a (d , tt) c) (+ℂ-identityʳ cb) ⟩
          inj⊤ a (cb , tt) c
        ∎
      bwd-fwd (law₁ c c' a b i) =
        isSet→isSet'
          squash⊤
          (bwd-fwd (inj⊤ (A .charge c' a) b c))
          (bwd-fwd (inj⊤ a b (c +ℂ c')))
          (λ k → bwd (fwd (law₁⊤ c c' a b k)))
          (law₁⊤ c c' a b)
          i
      bwd-fwd (law₂ c c' a b i) =
        isSet→isSet'
          squash⊤
          (bwd-fwd (inj⊤ a (⊤ .charge c' b) c))
          (bwd-fwd (inj⊤ a b (c +ℂ c')))
          (λ k → bwd (fwd (law₂⊤ c c' a b k)))
          (law₂⊤ c c' a b)
          i
      bwd-fwd (squash x y p q i j) =
        isSet→SquareP
          (λ k l → isProp→isSet
            (squash⊤ (bwd (fwd (squash⊤ x y p q k l))) (squash⊤ x y p q k l)))
          (cong bwd-fwd p)
          (cong bwd-fwd q)
          (λ _ → bwd-fwd x)
          (λ _ → bwd-fwd y)
          i j

      tensor⊤≃ : (A U⊗ ⊤) ≃ cmp A
      tensor⊤≃ = isoToEquiv (iso fwd bwd fwd-bwd bwd-fwd)

module _ where
  opaque
    unfolding Glueᶜ'

    pot-tensor : (A ⊗ (▷'[ c ] B)) ≡ (▷'[ c ] (A ⊗ B))
    pot-tensor {A = A} {c = c} {B = B} =
      𝒞-path
        (𝒱-path (ua pot-tensor≃))
        (charge-path
          pot-tensor≃
          ((A ⊗ (▷'[ c ] B)) .charge)
          ((▷'[ c ] (A ⊗ B)) .charge)
          fwd-charge)
      where
        injAB : cmp A → cmp B → val ℂ → A U⊗ B
        injAB = inj

        injA▷B : cmp A → cmp (▷'[ c ] B) → val ℂ → A U⊗ (▷'[ c ] B)
        injA▷B = inj

        unit▷ : cmp B → cmp (▷'[ c ] B)
        unit▷ b .• = η• b
        unit▷ b .◦ _ = B .charge c b
        unit▷ b .•→◦ = refl

        unit▷-path
          : (b : cmp B) (q◦ : cmp (◯ᶜ B))
          → (r : (λ _ → B .charge c b) ≡ q◦)
          → unit▷ b
            ≡ record { • = η• b ; ◦ = q◦ ; •→◦ = cong η• r }
        unit▷-path b q◦ r i .• = η• b
        unit▷-path b q◦ r i .◦ = r i
        unit▷-path b q◦ r i .•→◦ =
          isProp→PathP
            (λ i → ●ᶜ (◯ᶜ B) .U .is-set
              (●ᶜ.map (CHARGE c ⨾ᶜ η◦ᶜ {A = B}) .U (unit▷-path b q◦ r i .•))
              (η• (unit▷-path b q◦ r i .◦)))
            (unit▷ b .•→◦)
            (cong η• r)
            i

        unit▷-charge
          : (e : val ℂ) (b : cmp B)
          → unit▷ (B .charge e b) ≡ (▷'[ c ] B) .charge e (unit▷ b)
        unit▷-charge e b i .• = η• (B .charge e b)
        unit▷-charge e b i .◦ _ = CHARGE {A = B} c .charge e b i
        unit▷-charge e b i .•→◦ =
          isProp→PathP
            (λ i → ●ᶜ (◯ᶜ B) .U .is-set
              (●ᶜ.map (CHARGE c ⨾ᶜ η◦ᶜ {A = B}) .U (unit▷-charge e b i .•))
              (η• (unit▷-charge e b i .◦)))
            (unit▷ (B .charge e b) .•→◦)
            ((▷'[ c ] B) .charge e (unit▷ b) .•→◦)
            i

        tensor-unit▷ : A U⊗ B → A U⊗ (▷'[ c ] B)
        tensor-unit▷ (inj a b d) = injA▷B a (unit▷ b) d
        tensor-unit▷ (law₁ d e a b i) =
          law₁ d e a (unit▷ b) i
        tensor-unit▷ (law₂ d e a b i) =
          ( injA▷B a (unit▷ (B .charge e b)) d
          ≡⟨ cong (λ q → injA▷B a q d) (unit▷-charge e b) ⟩
            injA▷B a ((▷'[ c ] B) .charge e (unit▷ b)) d
          ≡⟨ law₂ d e a (unit▷ b) ⟩
            injA▷B a (unit▷ b) (d +ℂ e)
          ∎) i
        tensor-unit▷ (squash x y p q i j) =
          squash
            (tensor-unit▷ x)
            (tensor-unit▷ y)
            (cong tensor-unit▷ p)
            (cong tensor-unit▷ q)
            i j

        unit▷∗ : ⟨ ABS ⟩ → cmp B → cmp (▷'[ c ] B)
        unit▷∗ p b .• = ∗ p
        unit▷∗ p b .◦ _ = b
        unit▷∗ p b .•→◦ = sym (law (λ _ → b) p)

        unit▷∗-path
          : (p : ⟨ ABS ⟩) (q◦ : cmp (◯ᶜ B))
          → (qcoh : ∗ p ≡ η• q◦)
          → unit▷∗ p (q◦ p)
            ≡ record { • = ∗ p ; ◦ = q◦ ; •→◦ = qcoh }
        unit▷∗-path p q◦ qcoh i .• = ∗ p
        unit▷∗-path p q◦ qcoh i .◦ =
          (funExt λ abs → cong q◦ (ABS .snd p abs)) i
        unit▷∗-path p q◦ qcoh i .•→◦ =
          isProp→PathP
            (λ i → ●ᶜ (◯ᶜ B) .U .is-set
              (●ᶜ.map (CHARGE c ⨾ᶜ η◦ᶜ {A = B}) .U (unit▷∗-path p q◦ qcoh i .•))
              (η• (unit▷∗-path p q◦ qcoh i .◦)))
            (unit▷∗ p (q◦ p) .•→◦)
            qcoh
            i

        unit▷∗-η-path
          : (b : cmp B) (p : ⟨ ABS ⟩) (q◦ : cmp (◯ᶜ B))
          → unit▷∗ p (q◦ p)
            ≡ record
              { • = η• b
              ; ◦ = q◦
              ; •→◦ =
                  ●-unlex
                    {x = λ _ → B .charge c b}
                    {x' = q◦}
                    (∗ p)
              }
        unit▷∗-η-path b p q◦ i .• = law b p (~ i)
        unit▷∗-η-path b p q◦ i .◦ =
          (funExt λ abs → cong q◦ (ABS .snd p abs)) i
        unit▷∗-η-path b p q◦ i .•→◦ =
          isProp→PathP
            (λ i → ●ᶜ (◯ᶜ B) .U .is-set
              (●ᶜ.map (CHARGE c ⨾ᶜ η◦ᶜ {A = B}) .U (unit▷∗-η-path b p q◦ i .•))
              (η• (unit▷∗-η-path b p q◦ i .◦)))
            (unit▷∗ p (q◦ p) .•→◦)
            (●-unlex {x = λ _ → B .charge c b} {x' = q◦} (∗ p))
            i

        unit▷∗-charge
          : (p : ⟨ ABS ⟩) (e : val ℂ) (b : cmp B)
          → unit▷∗ p (B .charge e b) ≡ (▷'[ c ] B) .charge e (unit▷∗ p b)
        unit▷∗-charge p e b i .• = ∗ p
        unit▷∗-charge p e b i .◦ _ = B .charge e b
        unit▷∗-charge p e b i .•→◦ =
          isProp→PathP
            (λ i → ●ᶜ (◯ᶜ B) .U .is-set
              (●ᶜ.map (CHARGE c ⨾ᶜ η◦ᶜ {A = B}) .U (unit▷∗-charge p e b i .•))
              (η• (unit▷∗-charge p e b i .◦)))
            (unit▷∗ p (B .charge e b) .•→◦)
            ((▷'[ c ] B) .charge e (unit▷∗ p b) .•→◦)
            i

        tensor-star▷ : ⟨ ABS ⟩ → A U⊗ B → A U⊗ (▷'[ c ] B)
        tensor-star▷ p (inj a b d) = injA▷B a (unit▷∗ p b) d
        tensor-star▷ p (law₁ d e a b i) =
          law₁ d e a (unit▷∗ p b) i
        tensor-star▷ p (law₂ d e a b i) =
          ( injA▷B a (unit▷∗ p (B .charge e b)) d
          ≡⟨ cong (λ q → injA▷B a q d) (unit▷∗-charge p e b) ⟩
            injA▷B a ((▷'[ c ] B) .charge e (unit▷∗ p b)) d
          ≡⟨ law₂ d e a (unit▷∗ p b) ⟩
            injA▷B a (unit▷∗ p b) (d +ℂ e)
          ∎) i
        tensor-star▷ p (squash x y r s i j) =
          squash
            (tensor-star▷ p x)
            (tensor-star▷ p y)
            (cong (tensor-star▷ p) r)
            (cong (tensor-star▷ p) s)
            i j

        unit▷-star
          : (p : ⟨ ABS ⟩) (b : cmp B)
          → unit▷ b ≡ unit▷∗ p (B .charge c b)
        unit▷-star p b i .• = law b p i
        unit▷-star p b i .◦ _ = B .charge c b
        unit▷-star p b i .•→◦ =
          isProp→PathP
            (λ i → ●ᶜ (◯ᶜ B) .U .is-set
              (●ᶜ.map (CHARGE c ⨾ᶜ η◦ᶜ {A = B}) .U (unit▷-star p b i .•))
              (η• (unit▷-star p b i .◦)))
            (unit▷ b .•→◦)
            (unit▷∗ p (B .charge c b) .•→◦)
            i

        tensor-unit▷-star-charge
          : (p : ⟨ ABS ⟩) (x : A U⊗ B)
          → tensor-unit▷ x ≡ tensor-star▷ p ((A ⊗ B) .charge c x)
        tensor-unit▷-star-charge p (inj a b d) =
            injA▷B a (unit▷ b) d
          ≡⟨ cong (λ q → injA▷B a q d) (unit▷-star p b) ⟩
            injA▷B a (unit▷∗ p (B .charge c b)) d
          ≡⟨ cong (λ q → injA▷B a q d) (unit▷∗-charge p c b) ⟩
            injA▷B a ((▷'[ c ] B) .charge c (unit▷∗ p b)) d
          ≡⟨ law₂ d c a (unit▷∗ p b) ⟩
            injA▷B a (unit▷∗ p b) (d +ℂ c)
          ≡⟨ cong (injA▷B a (unit▷∗ p b)) (+ℂ-comm d c) ⟩
            injA▷B a (unit▷∗ p b) (c +ℂ d)
          ∎
        tensor-unit▷-star-charge p (law₁ d e a b i) =
          isSet→isSet'
            squash
            (tensor-unit▷-star-charge p (injAB (A .charge e a) b d))
            (tensor-unit▷-star-charge p (injAB a b (d +ℂ e)))
            (λ k → tensor-unit▷ (law₁ d e a b k))
            (λ k → tensor-star▷ p ((A ⊗ B) .charge c (law₁ d e a b k)))
            i
        tensor-unit▷-star-charge p (law₂ d e a b i) =
          isSet→isSet'
            squash
            (tensor-unit▷-star-charge p (injAB a (B .charge e b) d))
            (tensor-unit▷-star-charge p (injAB a b (d +ℂ e)))
            (λ k → tensor-unit▷ (law₂ d e a b k))
            (λ k → tensor-star▷ p ((A ⊗ B) .charge c (law₂ d e a b k)))
            i
        tensor-unit▷-star-charge p (squash x y r s i j) =
          isSet→SquareP
            (λ k l → isProp→isSet
              (squash
                (tensor-unit▷ (squash x y r s k l))
                (tensor-star▷ p ((A ⊗ B) .charge c (squash x y r s k l)))))
            (cong (tensor-unit▷-star-charge p) r)
            (cong (tensor-unit▷-star-charge p) s)
            (λ _ → tensor-unit▷-star-charge p x)
            (λ _ → tensor-unit▷-star-charge p y)
            i j

        fwd-law₁-•
          : (d e : val ℂ) (a : cmp A) (q : cmp (▷'[ c ] B))
          → ●ᵛ.map (λ b → injAB (A .charge e a) b d) (q .•)
            ≡ ●ᵛ.map (λ b → injAB a b (d +ℂ e)) (q .•)
        fwd-law₁-• d e a q =
          cong (λ f → ●ᵛ.map f (q .•)) (funExt λ b → law₁ d e a b)

        open⊗ : cmp A → val ℂ → cmp (◯ᶜ B) → cmp (◯ᶜ (A ⊗ B))
        open⊗ a d b◦ abs = injAB a (b◦ abs) d

        fwd-law₁-◦
          : (d e : val ℂ) (a : cmp A) (q : cmp (▷'[ c ] B))
          → open⊗ (A .charge e a) d (q .◦)
            ≡ open⊗ a (d +ℂ e) (q .◦)
        fwd-law₁-◦ d e a q =
          funExt {A = ⟨ ABS ⟩} {B = λ _ _ → A U⊗ B} λ abs →
            law₁ d e a (q .◦ abs)

        fwd-law₂-•
          : (d e : val ℂ) (a : cmp A) (q : cmp (▷'[ c ] B))
          → ●ᵛ.map (λ b → injAB a b d) (●ᶜ B .charge e (q .•))
            ≡ ●ᵛ.map (λ b → injAB a b (d +ℂ e)) (q .•)
        fwd-law₂-• d e a q =
            ●ᵛ.map (λ b → injAB a b d) (●ᶜ B .charge e (q .•))
          ≡⟨ cong (●ᵛ.map (λ b → injAB a b d)) (●ᶜ-charge-map {A = B} e (q .•)) ⟩
            ●ᵛ.map (λ b → injAB a b d) (●ᵛ.map (B .charge e) (q .•))
          ≡⟨ ●ᵛ.map-∘ (B .charge e) (λ b → injAB a b d) (q .•) ⟩
            ●ᵛ.map (λ b → injAB a (B .charge e b) d) (q .•)
          ≡⟨ cong (λ f → ●ᵛ.map f (q .•)) (funExt λ b → law₂ d e a b) ⟩
            ●ᵛ.map (λ b → injAB a b (d +ℂ e)) (q .•)
          ∎

        fwd-law₂-◦
          : (d e : val ℂ) (a : cmp A) (q : cmp (▷'[ c ] B))
          → open⊗ a d (((▷'[ c ] B) .charge e q) .◦)
            ≡ open⊗ a (d +ℂ e) (q .◦)
        fwd-law₂-◦ d e a q =
          funExt {A = ⟨ ABS ⟩} {B = λ _ _ → A U⊗ B} λ abs →
            law₂ d e a (q .◦ abs)

        fwd : A U⊗ (▷'[ c ] B) → cmp (▷'[ c ] (A ⊗ B))
        fwd (inj a q d) .• = ●ᵛ.map (λ b → injAB a b d) (q .•)
        fwd (inj a q d) .◦ abs = injAB a (q .◦ abs) d
        fwd (inj a q d) .•→◦ =
            ●ᶜ.map (CHARGE c ⨾ᶜ η◦ᶜ {A = A ⊗ B}) .U
              (●ᵛ.map (λ b → injAB a b d) (q .•))
          ≡⟨ ●ᵛ.map-∘
                (λ b → injAB a b d)
                ((CHARGE c ⨾ᶜ η◦ᶜ {A = A ⊗ B}) .U)
                (q .•) ⟩
            ●ᵛ.map
              (((CHARGE c ⨾ᶜ η◦ᶜ {A = A ⊗ B}) .U) ∘ (λ b → injAB a b d))
              (q .•)
          ≡⟨ cong (λ f → ●ᵛ.map f (q .•))
                (funExt {A = cmp B} {B = λ _ _ → cmp (◯ᶜ (A ⊗ B))} λ b →
                  funExt {A = ⟨ ABS ⟩} {B = λ _ _ → A U⊗ B} λ abs →
                    injAB a b (c +ℂ d)
                  ≡⟨ cong (injAB a b) (+ℂ-comm c d) ⟩
                    injAB a b (d +ℂ c)
                  ≡⟨ sym (law₂ d c a b) ⟩
                    injAB a (B .charge c b) d
                  ∎) ⟩
            ●ᵛ.map
              (open⊗ a d
                ∘ ((CHARGE c ⨾ᶜ η◦ᶜ {A = B}) .U))
              (q .•)
          ≡⟨ sym (●ᵛ.map-∘
                ((CHARGE c ⨾ᶜ η◦ᶜ {A = B}) .U)
                (open⊗ a d)
                (q .•)) ⟩
            ●ᵛ.map (open⊗ a d)
              (●ᶜ.map (CHARGE c ⨾ᶜ η◦ᶜ {A = B}) .U (q .•))
          ≡⟨ cong (●ᵛ.map (open⊗ a d)) (q .•→◦) ⟩
            η• (open⊗ a d (q .◦))
          ∎
        fwd (law₁ d e a q i) .• =
          fwd-law₁-• d e a q i
        fwd (law₁ d e a q i) .◦ abs =
          fwd-law₁-◦ d e a q i abs
        fwd (law₁ d e a q i) .•→◦ =
          isProp→PathP
            (λ i → ●ᶜ (◯ᶜ (A ⊗ B)) .U .is-set
              (●ᶜ.map (CHARGE c ⨾ᶜ η◦ᶜ {A = A ⊗ B}) .U (fwd-law₁-• d e a q i))
              (η• (fwd-law₁-◦ d e a q i)))
            (fwd (inj (A .charge e a) q d) .•→◦)
            (fwd (inj a q (d +ℂ e)) .•→◦)
            i
        fwd (law₂ d e a q i) .• =
          fwd-law₂-• d e a q i
        fwd (law₂ d e a q i) .◦ abs =
          fwd-law₂-◦ d e a q i abs
        fwd (law₂ d e a q i) .•→◦ =
          isProp→PathP
            (λ i → ●ᶜ (◯ᶜ (A ⊗ B)) .U .is-set
              (●ᶜ.map (CHARGE c ⨾ᶜ η◦ᶜ {A = A ⊗ B}) .U (fwd-law₂-• d e a q i))
              (η• (fwd-law₂-◦ d e a q i)))
            (fwd (inj a ((▷'[ c ] B) .charge e q) d) .•→◦)
            (fwd (inj a q (d +ℂ e)) .•→◦)
            i
        fwd (squash x y p q i j) =
          (▷'[ c ] (A ⊗ B)) .U .is-set
            (fwd x)
            (fwd y)
            (cong fwd p)
            (cong fwd q)
            i j

        rhs◦ : cmp (A ⊗ B) → cmp (◯ᶜ (A ⊗ B))
        rhs◦ = (CHARGE c ⨾ᶜ η◦ᶜ {A = A ⊗ B}) .U

        rhsα : cmp (●ᶜ (A ⊗ B)) → cmp (●ᶜ (◯ᶜ (A ⊗ B)))
        rhsα = ●ᶜ.map (CHARGE c ⨾ᶜ η◦ᶜ {A = A ⊗ B}) .U

        bwd-from-fiber
          : (q◦ : cmp (◯ᶜ (A ⊗ B)))
          → ● (fiber rhs◦ q◦)
          → A U⊗ (▷'[ c ] B)
        bwd-from-fiber q◦ =
          ind
            (λ _ → A U⊗ (▷'[ c ] B))
            (λ (x , _) → tensor-unit▷ x)
            (λ p → tensor-star▷ p (q◦ p))
            (λ (x , x-coh) p →
                tensor-unit▷ x
              ≡⟨ tensor-unit▷-star-charge p x ⟩
                tensor-star▷ p ((A ⊗ B) .charge c x)
              ≡⟨ cong (tensor-star▷ p) (funExt⁻ x-coh p) ⟩
                tensor-star▷ p (q◦ p)
              ∎)

        bwd-fiber
          : (q : cmp (▷'[ c ] (A ⊗ B)))
          → ● (fiber rhs◦ (q .◦))
        bwd-fiber q = ●-fiber-in rhs◦ (q .◦) (q .• , q .•→◦)

        bwd : cmp (▷'[ c ] (A ⊗ B)) → A U⊗ (▷'[ c ] B)
        bwd q = bwd-from-fiber (q .◦) (bwd-fiber q)

        fiber-in-fst
          : (q◦ : cmp (◯ᶜ (A ⊗ B)))
          → (x• : cmp (●ᶜ (A ⊗ B)))
          → (x-coh : rhsα x• ≡ η• q◦)
          → ●ᵛ.map (λ (r : fiber rhs◦ q◦) → r .fst)
              (●-fiber-in rhs◦ q◦ (x• , x-coh))
            ≡ x•
        fiber-in-fst q◦ =
          ind R η•-case ∗-case law-case
          where
            R : cmp (●ᶜ (A ⊗ B)) → Type
            R x• =
              (x-coh : rhsα x• ≡ η• q◦)
              → ●ᵛ.map (λ (r : fiber rhs◦ q◦) → r .fst)
                  (●-fiber-in rhs◦ q◦ (x• , x-coh))
                ≡ x•

            η•-case : (x : A U⊗ B) → R (η• x)
            η•-case x x-coh =
                ●ᵛ.map (λ (r : fiber rhs◦ q◦) → r .fst)
                  (●-fiber-in rhs◦ q◦ (η• x , x-coh))
              ≡⟨ ●ᵛ.map-∘ (λ r → x , r) (λ (r : fiber rhs◦ q◦) → r .fst) (●-lex x-coh) ⟩
                ●ᵛ.map (λ _ → x) (●-lex x-coh)
              ≡⟨ ●-map-const x (●-lex x-coh) ⟩
                η• x
              ∎

            ∗-case : (p : ⟨ ABS ⟩) → R (∗ p)
            ∗-case p x-coh = refl

            law-case
              : (x : A U⊗ B) (p : ⟨ ABS ⟩)
              → PathP (λ i → R (law x p i)) (η•-case x) (∗-case p)
            law-case x p =
              funext-dep-i0 λ x-coh →
                isProp→PathP
                  (λ i → isProp→isSet (●-isProp p)
                    (●ᵛ.map (λ (r : fiber rhs◦ q◦) → r .fst)
                      (●-fiber-in rhs◦ q◦ (law x p i , coe0→i (λ j → rhsα (law x p j) ≡ η• q◦) i x-coh)))
                    (law x p i))
                  (η•-case x x-coh)
                  (∗-case p (coe0→1 (λ i → rhsα (law x p i) ≡ η• q◦) x-coh))

        fwd-tensor-unit▷-•
          : (x : A U⊗ B)
          → fwd (tensor-unit▷ x) .• ≡ η• x
        fwd-tensor-unit▷-• (inj a b d) = refl
        fwd-tensor-unit▷-• (law₁ d e a b i) =
          isSet→isSet'
            (●ᶜ (A ⊗ B) .U .is-set)
            (fwd-tensor-unit▷-• (injAB (A .charge e a) b d))
            (fwd-tensor-unit▷-• (injAB a b (d +ℂ e)))
            (λ k → fwd (tensor-unit▷ (law₁ d e a b k)) .•)
            (λ k → η• (law₁ d e a b k))
            i
        fwd-tensor-unit▷-• (law₂ d e a b i) =
          isSet→isSet'
            (●ᶜ (A ⊗ B) .U .is-set)
            (fwd-tensor-unit▷-• (injAB a (B .charge e b) d))
            (fwd-tensor-unit▷-• (injAB a b (d +ℂ e)))
            (λ k → fwd (tensor-unit▷ (law₂ d e a b k)) .•)
            (λ k → η• (law₂ d e a b k))
            i
        fwd-tensor-unit▷-• (squash x y p q i j) =
          isSet→SquareP
            (λ k l → isProp→isSet
              (●ᶜ (A ⊗ B) .U .is-set
                (fwd (tensor-unit▷ (squash x y p q k l)) .•)
                (η• (squash x y p q k l))))
            (cong fwd-tensor-unit▷-• p)
            (cong fwd-tensor-unit▷-• q)
            (λ _ → fwd-tensor-unit▷-• x)
            (λ _ → fwd-tensor-unit▷-• y)
            i j

        fwd-tensor-unit▷-◦
          : (x : A U⊗ B)
          → fwd (tensor-unit▷ x) .◦ ≡ rhs◦ x
        fwd-tensor-unit▷-◦ (inj a b d) =
          funExt λ abs →
              injAB a (B .charge c b) d
            ≡⟨ law₂ d c a b ⟩
              injAB a b (d +ℂ c)
            ≡⟨ cong (injAB a b) (+ℂ-comm d c) ⟩
              injAB a b (c +ℂ d)
            ∎
        fwd-tensor-unit▷-◦ (law₁ d e a b i) =
          isSet→isSet'
            (◯ᶜ (A ⊗ B) .U .is-set)
            (fwd-tensor-unit▷-◦ (injAB (A .charge e a) b d))
            (fwd-tensor-unit▷-◦ (injAB a b (d +ℂ e)))
            (λ k → fwd (tensor-unit▷ (law₁ d e a b k)) .◦)
            (λ k → rhs◦ (law₁ d e a b k))
            i
        fwd-tensor-unit▷-◦ (law₂ d e a b i) =
          isSet→isSet'
            (◯ᶜ (A ⊗ B) .U .is-set)
            (fwd-tensor-unit▷-◦ (injAB a (B .charge e b) d))
            (fwd-tensor-unit▷-◦ (injAB a b (d +ℂ e)))
            (λ k → fwd (tensor-unit▷ (law₂ d e a b k)) .◦)
            (λ k → rhs◦ (law₂ d e a b k))
            i
        fwd-tensor-unit▷-◦ (squash x y p q i j) =
          isSet→SquareP
            (λ k l → isProp→isSet
              (◯ᶜ (A ⊗ B) .U .is-set
                (fwd (tensor-unit▷ (squash x y p q k l)) .◦)
                (rhs◦ (squash x y p q k l))))
            (cong fwd-tensor-unit▷-◦ p)
            (cong fwd-tensor-unit▷-◦ q)
            (λ _ → fwd-tensor-unit▷-◦ x)
            (λ _ → fwd-tensor-unit▷-◦ y)
            i j

        fwd-tensor-star▷-•
          : (p : ⟨ ABS ⟩) (x : A U⊗ B)
          → fwd (tensor-star▷ p x) .• ≡ ∗ p
        fwd-tensor-star▷-• p (inj a b d) = refl
        fwd-tensor-star▷-• p (law₁ d e a b i) =
          isSet→isSet'
            (●ᶜ (A ⊗ B) .U .is-set)
            (fwd-tensor-star▷-• p (injAB (A .charge e a) b d))
            (fwd-tensor-star▷-• p (injAB a b (d +ℂ e)))
            (λ k → fwd (tensor-star▷ p (law₁ d e a b k)) .•)
            (λ _ → ∗ p)
            i
        fwd-tensor-star▷-• p (law₂ d e a b i) =
          isSet→isSet'
            (●ᶜ (A ⊗ B) .U .is-set)
            (fwd-tensor-star▷-• p (injAB a (B .charge e b) d))
            (fwd-tensor-star▷-• p (injAB a b (d +ℂ e)))
            (λ k → fwd (tensor-star▷ p (law₂ d e a b k)) .•)
            (λ _ → ∗ p)
            i
        fwd-tensor-star▷-• p (squash x y r s i j) =
          isSet→SquareP
            (λ k l → isProp→isSet
              (●ᶜ (A ⊗ B) .U .is-set
                (fwd (tensor-star▷ p (squash x y r s k l)) .•)
                (∗ p)))
            (cong (fwd-tensor-star▷-• p) r)
            (cong (fwd-tensor-star▷-• p) s)
            (λ _ → fwd-tensor-star▷-• p x)
            (λ _ → fwd-tensor-star▷-• p y)
            i j

        fwd-tensor-star▷-◦
          : (p : ⟨ ABS ⟩) (x : A U⊗ B)
          → fwd (tensor-star▷ p x) .◦ ≡ η◦ᶜ {A = A ⊗ B} .U x
        fwd-tensor-star▷-◦ p (inj a b d) = refl
        fwd-tensor-star▷-◦ p (law₁ d e a b i) =
          isSet→isSet'
            (◯ᶜ (A ⊗ B) .U .is-set)
            (fwd-tensor-star▷-◦ p (injAB (A .charge e a) b d))
            (fwd-tensor-star▷-◦ p (injAB a b (d +ℂ e)))
            (λ k → fwd (tensor-star▷ p (law₁ d e a b k)) .◦)
            (λ k → η◦ᶜ {A = A ⊗ B} .U (law₁ d e a b k))
            i
        fwd-tensor-star▷-◦ p (law₂ d e a b i) =
          isSet→isSet'
            (◯ᶜ (A ⊗ B) .U .is-set)
            (fwd-tensor-star▷-◦ p (injAB a (B .charge e b) d))
            (fwd-tensor-star▷-◦ p (injAB a b (d +ℂ e)))
            (λ k → fwd (tensor-star▷ p (law₂ d e a b k)) .◦)
            (λ k → η◦ᶜ {A = A ⊗ B} .U (law₂ d e a b k))
            i
        fwd-tensor-star▷-◦ p (squash x y r s i j) =
          isSet→SquareP
            (λ k l → isProp→isSet
              (◯ᶜ (A ⊗ B) .U .is-set
                (fwd (tensor-star▷ p (squash x y r s k l)) .◦)
                (η◦ᶜ {A = A ⊗ B} .U (squash x y r s k l))))
            (cong (fwd-tensor-star▷-◦ p) r)
            (cong (fwd-tensor-star▷-◦ p) s)
            (λ _ → fwd-tensor-star▷-◦ p x)
            (λ _ → fwd-tensor-star▷-◦ p y)
            i j

        fwd-bwd-fiber-•
          : (q◦ : cmp (◯ᶜ (A ⊗ B))) (u : ● (fiber rhs◦ q◦))
          → fwd (bwd-from-fiber q◦ u) .•
            ≡ ●ᵛ.map fst u
        fwd-bwd-fiber-• q◦ (η• (x , x-coh)) = fwd-tensor-unit▷-• x
        fwd-bwd-fiber-• q◦ (∗ p) = fwd-tensor-star▷-• p (q◦ p)
        fwd-bwd-fiber-• q◦ (law (x , x-coh) p i) =
          isSet→isSet'
            (●ᶜ (A ⊗ B) .U .is-set)
            (fwd-bwd-fiber-• q◦ (η• (x , x-coh)))
            (fwd-bwd-fiber-• q◦ (∗ p))
            (λ k → fwd (bwd-from-fiber q◦ (law (x , x-coh) p k)) .•)
            (λ k → ●ᵛ.map (λ (r : fiber rhs◦ q◦) → r .fst) (law (x , x-coh) p k))
            i

        fwd-bwd-fiber-◦
          : (q◦ : cmp (◯ᶜ (A ⊗ B))) (u : ● (fiber rhs◦ q◦))
          → fwd (bwd-from-fiber q◦ u) .◦ ≡ q◦
        fwd-bwd-fiber-◦ q◦ (η• (x , x-coh)) =
            fwd (tensor-unit▷ x) .◦
          ≡⟨ fwd-tensor-unit▷-◦ x ⟩
            rhs◦ x
          ≡⟨ x-coh ⟩
            q◦
          ∎
        fwd-bwd-fiber-◦ q◦ (∗ p) =
            fwd (tensor-star▷ p (q◦ p)) .◦
          ≡⟨ fwd-tensor-star▷-◦ p (q◦ p) ⟩
            η◦ᶜ {A = A ⊗ B} .U (q◦ p)
          ≡⟨ funExt (λ abs → cong q◦ (ABS .snd p abs)) ⟩
            q◦
          ∎
        fwd-bwd-fiber-◦ q◦ (law (x , x-coh) p i) =
          isSet→isSet'
            (◯ᶜ (A ⊗ B) .U .is-set)
            (fwd-bwd-fiber-◦ q◦ (η• (x , x-coh)))
            (fwd-bwd-fiber-◦ q◦ (∗ p))
            (λ k → fwd (bwd-from-fiber q◦ (law (x , x-coh) p k)) .◦)
            (λ _ → q◦)
            i

        fwd-charge-inj-•
          : (e : val ℂ) (a : cmp A) (q : cmp (▷'[ c ] B)) (d : val ℂ)
          → ●ᵛ.map (λ b → injAB a b (e +ℂ d)) (q .•)
            ≡ ●ᶜ (A ⊗ B) .charge e
                (●ᵛ.map (λ b → injAB a b d) (q .•))
        fwd-charge-inj-• e a q d =
            ●ᵛ.map (λ b → injAB a b (e +ℂ d)) (q .•)
          ≡⟨ refl ⟩
            ●ᵛ.map (((A ⊗ B) .charge e) ∘ (λ b → injAB a b d)) (q .•)
          ≡⟨ sym (●ᵛ.map-∘ (λ b → injAB a b d) ((A ⊗ B) .charge e) (q .•)) ⟩
            ●ᵛ.map ((A ⊗ B) .charge e)
              (●ᵛ.map (λ b → injAB a b d) (q .•))
          ≡⟨ sym (●ᶜ-charge-map {A = A ⊗ B} e
                (●ᵛ.map (λ b → injAB a b d) (q .•))) ⟩
            ●ᶜ (A ⊗ B) .charge e
              (●ᵛ.map (λ b → injAB a b d) (q .•))
          ∎

        fwd-charge-inj-◦
          : (e : val ℂ) (a : cmp A) (q : cmp (▷'[ c ] B)) (d : val ℂ)
          → (λ abs → injAB a (q .◦ abs) (e +ℂ d))
            ≡ ◯ᶜ (A ⊗ B) .charge e (λ abs → injAB a (q .◦ abs) d)
        fwd-charge-inj-◦ e a q d = refl

        fwd-charge-inj
          : (e : val ℂ) (a : cmp A) (q : cmp (▷'[ c ] B)) (d : val ℂ)
          → fwd ((A ⊗ (▷'[ c ] B)) .charge e (injA▷B a q d))
            ≡ (▷'[ c ] (A ⊗ B)) .charge e (fwd (injA▷B a q d))
        fwd-charge-inj e a q d i .• = fwd-charge-inj-• e a q d i
        fwd-charge-inj e a q d i .◦ = fwd-charge-inj-◦ e a q d i
        fwd-charge-inj e a q d i .•→◦ =
          isProp→PathP
            (λ i → ●ᶜ (◯ᶜ (A ⊗ B)) .U .is-set
              (●ᶜ.map (CHARGE c ⨾ᶜ η◦ᶜ {A = A ⊗ B}) .U (fwd-charge-inj-• e a q d i))
              (η• (fwd-charge-inj-◦ e a q d i)))
            (fwd ((A ⊗ (▷'[ c ] B)) .charge e (inj a q d)) .•→◦)
            ((▷'[ c ] (A ⊗ B)) .charge e (fwd (inj a q d)) .•→◦)
            i

        fwd-charge
          : (e : val ℂ) (x : A U⊗ (▷'[ c ] B))
          → fwd ((A ⊗ (▷'[ c ] B)) .charge e x)
            ≡ (▷'[ c ] (A ⊗ B)) .charge e (fwd x)
        fwd-charge e (inj a q d) = fwd-charge-inj e a q d
        fwd-charge e (law₁ d e' a q i) =
          isSet→isSet'
            ((▷'[ c ] (A ⊗ B)) .U .is-set)
            (fwd-charge-inj e (A .charge e' a) q d)
            (fwd-charge-inj e a q (d +ℂ e'))
            (λ k → fwd ((A ⊗ (▷'[ c ] B)) .charge e (law₁ d e' a q k)))
            (λ k → (▷'[ c ] (A ⊗ B)) .charge e (fwd (law₁ d e' a q k)))
            i
        fwd-charge e (law₂ d e' a q i) =
          isSet→isSet'
            ((▷'[ c ] (A ⊗ B)) .U .is-set)
            (fwd-charge-inj e a ((▷'[ c ] B) .charge e' q) d)
            (fwd-charge-inj e a q (d +ℂ e'))
            (λ k → fwd ((A ⊗ (▷'[ c ] B)) .charge e (law₂ d e' a q k)))
            (λ k → (▷'[ c ] (A ⊗ B)) .charge e (fwd (law₂ d e' a q k)))
            i
        fwd-charge e (squash x y p q i j) =
          isSet→SquareP
            (λ k l → isProp→isSet
              ((▷'[ c ] (A ⊗ B)) .U .is-set
                (fwd ((A ⊗ (▷'[ c ] B)) .charge e (squash x y p q k l)))
                ((▷'[ c ] (A ⊗ B)) .charge e (fwd (squash x y p q k l)))))
            (cong (fwd-charge e) p)
            (cong (fwd-charge e) q)
            (λ _ → fwd-charge e x)
            (λ _ → fwd-charge e y)
            i j

        fwd-bwd : section fwd bwd
        fwd-bwd q i .• =
          ( fwd (bwd q) .•
          ≡⟨ fwd-bwd-fiber-• (q .◦) (bwd-fiber q) ⟩
            ●ᵛ.map (λ (r : fiber rhs◦ (q .◦)) → r .fst) (bwd-fiber q)
          ≡⟨ fiber-in-fst (q .◦) (q .•) (q .•→◦) ⟩
            q .•
          ∎) i
        fwd-bwd q i .◦ =
          fwd-bwd-fiber-◦ (q .◦) (bwd-fiber q) i
        fwd-bwd q i .•→◦ =
          isProp→PathP
            (λ i → ●ᶜ (◯ᶜ (A ⊗ B)) .U .is-set
              (rhsα (fwd-bwd q i .•))
              (η• (fwd-bwd q i .◦)))
            (fwd (bwd q) .•→◦)
            (q .•→◦)
            i

        bwd-fwd-inj
          : (a : cmp A)
          → (q• : cmp (●ᶜ B))
          → (q◦ : cmp (◯ᶜ B))
          → (qcoh : ●ᶜ.map (CHARGE c ⨾ᶜ η◦ᶜ {A = B}) .U q• ≡ η• q◦)
          → (d : val ℂ)
          → bwd (fwd (injA▷B a (record { • = q• ; ◦ = q◦ ; •→◦ = qcoh }) d))
            ≡ injA▷B a (record { • = q• ; ◦ = q◦ ; •→◦ = qcoh }) d
        bwd-fwd-inj a =
          ind R η•-case ∗-case law-case
          where
            R : cmp (●ᶜ B) → Type
            R q• =
              (q◦ : cmp (◯ᶜ B))
              → (qcoh : ●ᶜ.map (CHARGE c ⨾ᶜ η◦ᶜ {A = B}) .U q• ≡ η• q◦)
              → (d : val ℂ)
              → bwd (fwd (injA▷B a (record { • = q• ; ◦ = q◦ ; •→◦ = qcoh }) d))
                ≡ injA▷B a (record { • = q• ; ◦ = q◦ ; •→◦ = qcoh }) d

            R-isProp : (q• : cmp (●ᶜ B)) → isProp (R q•)
            R-isProp q• f g =
              funExt λ q◦ →
                funExt λ qcoh →
                  funExt λ d →
                    squash
                      (bwd (fwd (injA▷B a (record { • = q• ; ◦ = q◦ ; •→◦ = qcoh }) d)))
                      (injA▷B a (record { • = q• ; ◦ = q◦ ; •→◦ = qcoh }) d)
                      (f q◦ qcoh d)
                      (g q◦ qcoh d)

            η•-case : (b : cmp B) → R (η• b)
            η•-case b q◦ qcoh d =
              subst
                (λ h →
                  bwd (fwd (injA▷B a (record { • = η• b ; ◦ = q◦ ; •→◦ = h }) d))
                  ≡ injA▷B a (record { • = η• b ; ◦ = q◦ ; •→◦ = h }) d)
                (●-unlex-lex qcoh)
                (ind
                  (λ u →
                    bwd (fwd (
                      injA▷B a (record { • = η• b ; ◦ = q◦ ; •→◦ = ●-unlex u }) d))
                    ≡ injA▷B a (record { • = η• b ; ◦ = q◦ ; •→◦ = ●-unlex u }) d)
                  (λ r →
                      bwd (fwd
                        (injA▷B a (record { • = η• b ; ◦ = q◦ ; •→◦ = ●-unlex (η• r) }) d))
                    ≡⟨ cong
                          (λ q → bwd (fwd (injA▷B a q d)))
                          (sym (unit▷-path b q◦ r)) ⟩
                      bwd (fwd (injA▷B a (unit▷ b) d))
                    ≡⟨ refl ⟩
                      injA▷B a (unit▷ b) d
                    ≡⟨ cong (λ q → injA▷B a q d) (unit▷-path b q◦ r) ⟩
                      injA▷B a (record { • = η• b ; ◦ = q◦ ; •→◦ = ●-unlex (η• r) }) d
                    ∎)
                  (λ p →
                      bwd (fwd (
                        injA▷B a (record { • = η• b ; ◦ = q◦ ; •→◦ = ●-unlex (∗ p) }) d))
                    ≡⟨ cong
                          (λ p' → injA▷B a (unit▷∗ p' (q◦ p')) d)
                          (ABS .snd _ p) ⟩
                      injA▷B a (unit▷∗ p (q◦ p)) d
                    ≡⟨ cong (λ q → injA▷B a q d) (unit▷∗-η-path b p q◦) ⟩
                      injA▷B a (record { • = η• b ; ◦ = q◦ ; •→◦ = ●-unlex (∗ p) }) d
                    ∎)
                  (λ r p →
                    isProp→PathP
                      (λ i →
                        (squash
                          (bwd (fwd
                              (injA▷B a (record { • = η• b ; ◦ = q◦ ; •→◦ = ●-unlex (law r p i) }) d)))
                          (injA▷B a (record { • = η• b ; ◦ = q◦ ; •→◦ = ●-unlex (law r p i) }) d)))
                      _ _)
                  (●-lex qcoh))

            ∗-case : (p : ⟨ ABS ⟩) → R (∗ p)
            ∗-case p q◦ qcoh d =
                bwd (fwd (injA▷B a (record { • = ∗ p ; ◦ = q◦ ; •→◦ = qcoh }) d))
              ≡⟨ refl ⟩
                injA▷B a (unit▷∗ p (q◦ p)) d
              ≡⟨ cong (λ q → injA▷B a q d) (unit▷∗-path p q◦ qcoh) ⟩
                injA▷B a (record { • = ∗ p ; ◦ = q◦ ; •→◦ = qcoh }) d
              ∎

            law-case
              : (b : cmp B) (p : ⟨ ABS ⟩)
              → PathP (λ i → R (law b p i)) (η•-case b) (∗-case p)
            law-case b p =
              isProp→PathP (λ i → R-isProp (law b p i)) (η•-case b) (∗-case p)

        bwd-fwd : retract fwd bwd
        bwd-fwd (inj a record { • = q• ; ◦ = q◦ ; •→◦ = qcoh } d) =
          bwd-fwd-inj a q• q◦ qcoh d
        bwd-fwd (law₁ d e a q i) =
          isSet→isSet'
            squash
            (bwd-fwd (injA▷B (A .charge e a) q d))
            (bwd-fwd (injA▷B a q (d +ℂ e)))
            (λ k → bwd (fwd (law₁ d e a q k)))
            (law₁ d e a q)
            i
        bwd-fwd (law₂ d e a q i) =
          isSet→isSet'
            squash
            (bwd-fwd (injA▷B a ((▷'[ c ] B) .charge e q) d))
            (bwd-fwd (injA▷B a q (d +ℂ e)))
            (λ k → bwd (fwd (law₂ d e a q k)))
            (law₂ d e a q)
            i
        bwd-fwd (squash x y p q i j) =
          isSet→SquareP
            (λ k l → isProp→isSet
              (squash
                (bwd (fwd (squash x y p q k l)))
                (squash x y p q k l)))
            (cong bwd-fwd p)
            (cong bwd-fwd q)
            (λ _ → bwd-fwd x)
            (λ _ → bwd-fwd y)
            i j

        pot-tensor≃ : (A U⊗ (▷'[ c ] B)) ≃ cmp (▷'[ c ] (A ⊗ B))
        pot-tensor≃ = isoToEquiv (iso fwd bwd fwd-bwd bwd-fwd)
