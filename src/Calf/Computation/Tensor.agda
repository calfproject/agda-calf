open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence using (ua)
open import Function

module Calf.Computation.Tensor where

open import Calf.Value
open import Calf.Computation
open import Calf.Core.Cost
open import Calf.Value.Product
open import Calf.Value.Sigma
open import Calf.Value.Unit
open import Calf.Computation.Free public

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
map₂ = {!   !}

opaque
  unfolding F

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
  open import Calf.Computation.Potential

  pot-tensor : A ⊗ (▷'[ c ] ⊤) ≡ ▷'[ c ] (A ⊗ ⊤)
  pot-tensor =
    𝒞-path
      (𝒱-path (ua (isoToEquiv (iso fwd bwd {!   !} {!   !}))))
      {!   !}
    where
      fwd : A U⊗ (▷'[ c ] ⊤) → cmp (▷'[ c ] (A ⊗ ⊤))
      fwd = {!   !}

      bwd : cmp (▷'[ c ] (A ⊗ ⊤)) → A U⊗ (▷'[ c ] ⊤)
      bwd = {!   !}
