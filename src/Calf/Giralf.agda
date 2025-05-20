{-# OPTIONS --rewriting --allow-unsolved-metas #-}

open import Algebra.Cost
open import Relation.Binary using (IsPreorder)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; module ≡-Reasoning)

module Calf.Giralf (ℂᶜ : Set) (zeroᶜ : ℂᶜ) (_+ᶜ_ : ℂᶜ → ℂᶜ → ℂᶜ) (isCommutativeMonoid : IsCommutativeMonoid ℂᶜ _+ᶜ_ zeroᶜ) where

record _≤Temporal_ (c c' : ℂᶜ) : Set where
  field
    difference : ℂᶜ
    proof : c +ᶜ difference ≡ c'

isPreorder : IsPreorder _≡_ _≤Temporal_
isPreorder .IsPreorder.isEquivalence = Eq.isEquivalence
isPreorder .IsPreorder.reflexive refl ._≤Temporal_.difference = zeroᶜ
isPreorder .IsPreorder.reflexive refl ._≤Temporal_.proof = IsCommutativeMonoid.identityʳ ℂᶜ isCommutativeMonoid _
isPreorder .IsPreorder.trans x≤y y≤z ._≤Temporal_.difference = x≤y ._≤Temporal_.difference +ᶜ y≤z ._≤Temporal_.difference
isPreorder .IsPreorder.trans {x} {y} {z} x≤y y≤z ._≤Temporal_.proof =
  let open ≡-Reasoning in
  begin
    x +ᶜ (x≤y ._≤Temporal_.difference +ᶜ y≤z ._≤Temporal_.difference)
  ≡⟨ IsCommutativeMonoid.assoc ℂᶜ isCommutativeMonoid _ _ _ ⟨
    (x +ᶜ x≤y ._≤Temporal_.difference) +ᶜ y≤z ._≤Temporal_.difference
  ≡⟨ Eq.cong (_+ᶜ _) (_≤Temporal_.proof x≤y) ⟩
    y +ᶜ y≤z ._≤Temporal_.difference
  ≡⟨ _≤Temporal_.proof y≤z ⟩
    z
  ∎

open import Algebra.Bundles using (CommutativeSemigroup)

commutativeSemigroup : CommutativeSemigroup _ _
commutativeSemigroup .CommutativeSemigroup.Carrier = ℂᶜ
commutativeSemigroup .CommutativeSemigroup._≈_ = _≡_
commutativeSemigroup .CommutativeSemigroup._∙_ = _+ᶜ_
commutativeSemigroup .CommutativeSemigroup.isCommutativeSemigroup = IsCommutativeMonoid.isCommutativeSemigroup ℂᶜ isCommutativeMonoid

open import Algebra.Properties.CommutativeSemigroup commutativeSemigroup using (interchange)

costMonoid : CostMonoid
costMonoid .CostMonoid.ℂ = ℂᶜ
costMonoid .CostMonoid.zero = zeroᶜ
costMonoid .CostMonoid._+_ = _+ᶜ_
costMonoid .CostMonoid._≤_ = _≤Temporal_
costMonoid .CostMonoid.isCostMonoid .IsCostMonoid.isMonoid = IsCommutativeMonoid.isMonoid isCommutativeMonoid
costMonoid .CostMonoid.isCostMonoid .IsCostMonoid.isPreorder = isPreorder
costMonoid .CostMonoid.isCostMonoid .IsCostMonoid.isMonotone .IsMonotone.∙-mono-≤ x≤y u≤v ._≤Temporal_.difference = x≤y ._≤Temporal_.difference +ᶜ u≤v ._≤Temporal_.difference
costMonoid .CostMonoid.isCostMonoid .IsCostMonoid.isMonotone .IsMonotone.∙-mono-≤ {x} {y} {u} {v} x≤y u≤v ._≤Temporal_.proof =
  let open ≡-Reasoning in
  begin
    (x +ᶜ u) +ᶜ (x≤y ._≤Temporal_.difference +ᶜ u≤v ._≤Temporal_.difference)
  ≡⟨ interchange x u (x≤y ._≤Temporal_.difference) (u≤v ._≤Temporal_.difference) ⟩
    (x +ᶜ x≤y ._≤Temporal_.difference) +ᶜ (u +ᶜ u≤v ._≤Temporal_.difference)
  ≡⟨ Eq.cong₂ _+ᶜ_ (x≤y ._≤Temporal_.proof) (u≤v ._≤Temporal_.proof) ⟩
    y +ᶜ v
  ∎

open CostMonoid costMonoid


open import Calf.Prelude
open import Calf.CBPV
open import Calf.Directed
open import Calf.Step costMonoid
open import Calf.Data.Product
open import Calf.Data.Sum as Sum
open import Calf.Data.List


open import Function using (_∘_; const)

zero/min : (c : ℂ) → zero ≤ c
zero/min c ._≤Temporal_.difference = c
zero/min c ._≤Temporal_.proof = +-identityˡ c

+-comm : (a b : ℂ) → a + b ≡ b + a
+-comm = IsCommutativeMonoid.comm isCommutativeMonoid

+-mono : ∀ {a a' b b'} → (a ≤ a') → (b ≤ b') → ((a + b) ≤ (a' + b'))
+-mono = isCostMonoid .IsCostMonoid.isMonotone .IsMonotone.∙-mono-≤

open import Algebra using (CommutativeMonoid)

comm-monoid : CommutativeMonoid _ _
comm-monoid .CommutativeMonoid.Carrier = ℂ
comm-monoid .CommutativeMonoid._≈_ = _≡_
comm-monoid .CommutativeMonoid._∙_ = _+_
comm-monoid .CommutativeMonoid.ε = zero
comm-monoid .CommutativeMonoid.isCommutativeMonoid = isCommutativeMonoid

open import Data.Fin as Fin using (Fin)
open import Algebra.Solver.CommutativeMonoid comm-monoid using (prove; Expr; var; id; _⊕_)
open import Data.Nat.Base using (ℕ; z≤n; s≤s)
open import Data.Vec.Base as Vec using (Vec; replicate; toList)
module SolverHelp where
  v₁ : ∀ {n : ℕ} → Expr (ℕ.suc n)
  v₁ {n} = var (Fin.zero)
  v₂ : ∀ {n : ℕ} → Expr (ℕ.suc (ℕ.suc n))
  v₂ {n} = var (Fin.suc Fin.zero)
  v₃ : ∀ {n : ℕ} → Expr (ℕ.suc (ℕ.suc (ℕ.suc n)))
  v₃ {n} = var (Fin.suc (Fin.suc Fin.zero))
  v₄ : ∀ {n : ℕ} → Expr (ℕ.suc (ℕ.suc (ℕ.suc (ℕ.suc n))))
  v₄ {n} = var (Fin.suc (Fin.suc (Fin.suc Fin.zero)))


open import Data.List.Base as List
open import Data.Maybe.Base as Maybe
module Perm-Split {E : Set} {n : ℕ} (_≡⋎_ : E → List E → Set) where
  data _≡⊔_ : List E → Vec (List E) n → Set where
    base : [] ≡⊔ Vec.tabulate λ _ → []
    to : ∀ {Δ Δs A} (As : Vec (Maybe E) n)
      → A ≡⋎ catMaybes (toList As)
      → Δ ≡⊔ Δs
      → (A ∷ Δ) ≡⊔ Vec.zipWith (λ Δᵢ → maybe (_∷ Δᵢ) Δᵢ) Δs As

  _≡⋎ᵐ_ : (List E × ℂ) → Vec (List E × ℂ) n → Set
  (Δ , q) ≡⋎ᵐ Δqs =
    let Δs , qs = Vec.unzip Δqs in
    (Δ ≡⊔ Δs) × (Vec.foldr′ _+_ zero qs ≤ q)

shift : ℂ × ℂ → ℂ × ℂ
shift (p₁ , p₂) = (p₁ + p₂ , p₂)

record Giralf : Set₁ where
  𝓥 : Set
  𝓥 = tp⁺

  valᵍ : 𝓥 → Set
  valᵍ = val

  field
    𝓒 : Set
    _⨾_⊢_ : List 𝓒 → ℂ → 𝓒 → Set

    _≡ᶜ⋎_ : 𝓒 → List 𝓒 → Set

  _≡⋎ᵐ_ : ∀ {n} → (List 𝓒 × ℂ) → Vec (List 𝓒 × ℂ) n → Set
  _≡⋎ᵐ_ = Perm-Split._≡⋎ᵐ_ _≡ᶜ⋎_

  cmpᵍ : 𝓒 → Set
  cmpᵍ A = [] ⨾ zero ⊢ A

  _⊸_ : 𝓒 → 𝓒 → 𝓥
  A ⊸ B = meta⁺ ([ A ] ⨾ zero ⊢ B)

  Uᵍ : 𝓒 → 𝓥
  Uᵍ A = meta⁺ (cmpᵍ A)

  field
    idᵍ : ∀ {Δ q A}
      → (Δ , q) ≡⋎ᵐ Vec.[ ([ A ] , zero) ]
      → Δ ⨾ q ⊢ A

    charge : ∀ {Δ Δ' q q' A} (p : ℂ)
      → (Δ , q) ≡⋎ᵐ Vec.[ (Δ' , q' + p) ]
      → Δ' ⨾ q' ⊢ A
      → Δ ⨾ q ⊢ A

    Fᵍ : 𝓥 → 𝓒
    retᵍ : ∀ {Δ q X}
      → (Δ , q) ≡⋎ᵐ Vec.[]
      → valᵍ X
      → Δ ⨾ q ⊢ (Fᵍ X)
    bindᵍ : ∀ {Δ Δ₁ Δ₂ q q₁ q₂ X A}
      → (Δ , q) ≡⋎ᵐ ((Δ₁ , q₁) Vec.∷ Vec.[ (Δ₂ , q₂) ])
      → Δ₁ ⨾ q₁ ⊢ (Fᵍ X)
      → (valᵍ X → Δ₂ ⨾ q₂ ⊢ A)
      → Δ ⨾ q ⊢ A

    _⋊ᵍ_ : ℂ → 𝓒 → 𝓒
    store : ∀ {Δ Δ' q q' A} (p : ℂ)
      → (Δ , q) ≡⋎ᵐ Vec.[ (Δ' , q' + p) ]
      → Δ' ⨾ q' ⊢ A
      → Δ ⨾ q ⊢ (p ⋊ᵍ A)
    release : ∀ {Δ Δ₁ Δ₂ p q q₁ q₂ A B}
      → (Δ , q) ≡⋎ᵐ ((Δ₁ , q₁) Vec.∷ Vec.[ (Δ₂ , q₂) ])
      → Δ₁ ⨾ q₁ ⊢ (p ⋊ᵍ A)
      → (A ∷ Δ₂) ⨾ p + q₂ ⊢ B
      → Δ ⨾ q ⊢ B

    ⊥ᵍ : 𝓒
    absurdᵍ : ∀ {Δ Δ' q q' C}
      → (Δ , q) ≡⋎ᵐ Vec.[ (Δ' , q') ]
      → Δ' ⨾ q' ⊢ ⊥ᵍ
      → Δ ⨾ q ⊢ C

    _⊎ᵍ_ : 𝓒 → 𝓒 → 𝓒
    inj₁ᵍ : ∀ {Δ Δ' q q' A B}
      → (Δ , q) ≡⋎ᵐ Vec.[ (Δ' , q') ]
      → Δ' ⨾ q' ⊢ A
      → Δ ⨾ q ⊢ (A ⊎ᵍ B)
    inj₂ᵍ : ∀ {Δ Δ' q q' A B}
      → (Δ , q) ≡⋎ᵐ Vec.[ (Δ' , q') ]
      → Δ' ⨾ q' ⊢ B
      → Δ ⨾ q ⊢ (A ⊎ᵍ B)
    caseᵍ : ∀ {Δ Δ₁ Δ₂ q q₁ q₂ A B C}
      → (Δ , q) ≡⋎ᵐ ((Δ₁ , q₁) Vec.∷ Vec.[ (Δ₂ , q₂) ])
      → Δ₁ ⨾ q₁ ⊢ (A ⊎ᵍ B)
      → (A ∷ Δ₂) ⨾ q₂ ⊢ C
      → (B ∷ Δ₂) ⨾ q₂ ⊢ C
      → Δ ⨾ q ⊢ C

    ⊤ᵍ : 𝓒
    trivᵍ : ∀ {Δ q}
      → (Δ , q) ≡⋎ᵐ Vec.[]
      → Δ ⨾ q ⊢ ⊤ᵍ
    checkᵍ : ∀ {Δ Δ₁ Δ₂ q q₁ q₂ C}
      → (Δ , q) ≡⋎ᵐ ((Δ₁ , q₁) Vec.∷ Vec.[ (Δ₂ , q₂) ])
      → Δ₁ ⨾ q₁ ⊢ ⊤ᵍ
      → Δ₂ ⨾ q₂ ⊢ C
      → Δ ⨾ q ⊢ C

    _⊗ᵍ_ : 𝓒 → 𝓒 → 𝓒
    tensorᵍ : ∀ {Δ Δ₁ Δ₂ q q₁ q₂ A B}
      → (Δ , q) ≡⋎ᵐ ((Δ₁ , q₁) Vec.∷ Vec.[ (Δ₂ , q₂) ])
      → Δ₁ ⨾ q₁ ⊢ A
      → Δ₂ ⨾ q₂ ⊢ B
      → Δ ⨾ q ⊢ (A ⊗ᵍ B)
    splitᵍ : ∀ {Δ Δ₁ Δ₂ q q₁ q₂ A B C}
      → (Δ , q) ≡⋎ᵐ ((Δ₁ , q₁) Vec.∷ Vec.[ (Δ₂ , q₂) ])
      → Δ₁ ⨾ q₁ ⊢ (A ⊗ᵍ B)
      → (A ∷ B ∷ Δ₂) ⨾ q₂ ⊢ C
      → Δ ⨾ q ⊢ C

    listᵍ : (ℂ × ℂ) → 𝓒 → 𝓒
    nilᵍ : ∀ {Δ q A ps}
      → (Δ , q) ≡⋎ᵐ Vec.[]
      → Δ ⨾ q ⊢ (listᵍ ps A)
    consᵍ : ∀ {Δ Δ₁ Δ₂ q q₁ q₂ A ps}
      → (Δ , q) ≡⋎ᵐ ((Δ₁ , q₁ + ps .proj₁) Vec.∷ Vec.[ (Δ₂ , q₂) ])
      → Δ₁ ⨾ q₁ ⊢ A
      → Δ₂ ⨾ q₂ ⊢ listᵍ (shift ps) A
      → Δ ⨾ q ⊢ listᵍ ps A
    foldrᵍ : ∀ {Δ Δ' q q' A ps} {B : ℂ × ℂ → 𝓒}
      → (Δ , q) ≡⋎ᵐ Vec.[ (Δ' , q') ]
      → Δ' ⨾ q' ⊢ listᵍ ps A
      → (∀ {rs} → cmpᵍ (B rs))
      → (∀ {rs} → ((B (shift rs)) ∷ A ∷ []) ⨾ (rs .proj₁) ⊢ B rs)
      → Δ ⨾ q ⊢ B ps

  variable
    X Y Z : 𝓥
    A B C : 𝓒
    p q r : ℂ


_⊸F_ : tp⁺ → tp⁺ → Set
X ⊸F Y = cmp (X ⇀ F Y)

record PotentialFunction : Set where
  field
    ₀ : tp⁺
    Φᶜ : val ₀ → ℂ
  Φ : ₀ ⊸F ₀
  Φ a = step (F _) (Φᶜ a) (ret a)
open PotentialFunction

_⇒_ : tp⁺ → tp⁺ → Set
X ⇒ Y = val X → val Y

record Square (A : PotentialFunction) (q : ℂ) (B : PotentialFunction) : Set where
  field
    top : A .₀ ⊸F B .₀
    bot : A .₀ ⇒ B .₀
    square :
      (a : val (A .₀)) →
        bind (F _) (top a) (Φ B) ≤⁻[ F _ ] bind (F _) (Φ A a) (step (F _) q ∘ ret ∘ bot)
open Square


weaken-pot : ∀ {A} (q : ℂ) → Square A q A
weaken-pot _ .top = ret
weaken-pot _ .bot = Function.id
weaken-pot {A} q .square a = bind-monoʳ-≤⁻ (Φ A a) (λ a → step-monoˡ-≤⁻ (ret a) (zero/min q))

step-ret-congˡ : ∀ {X c d} → (v : val X) → (c ≡ d) → (step (F X) c (ret v) ≡ step (F X) d (ret v))
step-ret-congˡ v = Eq.cong (λ c → step (F _) c (ret v))


_⋎_⨾□_ : ∀ {A B C p q r} → r ≡ p + q → Square A p B → Square B q C → Square A r C
(s ⋎ e ⨾□ f) .top a = bind (F _) (e .top a) (f .top)
(s ⋎ e ⨾□ f) .bot = (f .bot) ∘ (e .bot)
(_⋎_⨾□_ {A} {B} {C} {p} {q} {r} s e f) .square a =
  let open ≤⁻-Reasoning (F _) in
  begin
    bind (F _) (e .top a) (λ b → bind (F _) (f .top b) (Φ C))
  ≲⟨ bind-monoʳ-≤⁻ (e .top a) (f .square) ⟩
    bind (F _) (e .top a) (λ b → bind (F _) (Φ B b) (step (F _) q ∘ ret ∘ f .bot))
  ≡⟨⟩
    bind (F _) (bind (F _) (e .top a) (Φ B)) (step (F _) q ∘ ret ∘ f .bot)
  ≲⟨ bind-monoˡ-≤⁻ (step (F _) q ∘ ret ∘ f .bot) (e .square a) ⟩
    bind {B .₀} (F _) (bind (F _) (Φ A a) (step (F _) p ∘ ret ∘ e .bot)) (step (F _) q ∘ ret ∘ f .bot)
  ≡⟨ step-ret-congˡ _ (Eq.trans (+-assoc _ _ _) (Eq.cong (_ +_) (Eq.sym s))) ⟩
    step (F _) (A .Φᶜ a + r) (ret (f .bot (e .bot a)))
  ∎


-- Define tensor first, which is needed for contexts
_⊗_ : PotentialFunction → PotentialFunction → PotentialFunction
_⊗_ A B .₀ = A .₀ ×⁺ B .₀
_⊗_ A B .Φᶜ (a , b) = (A .Φᶜ a) + (B .Φᶜ b)

⊤ : PotentialFunction
⊤ .₀ = unit
⊤ .Φᶜ triv = zero


Tensorfy : List PotentialFunction → PotentialFunction
Tensorfy Δ = List.foldr _⊗_ ⊤ Δ

MultiSquare : List PotentialFunction → ℂ → PotentialFunction → Set
MultiSquare Δ = Square (Tensorfy Δ)

constᵍ : ∀ {A} → (a : val (A .₀)) → MultiSquare [] (A .Φᶜ a) A
constᵍ a .top triv = ret a
constᵍ a .bot triv = a
constᵍ _ .square triv = ≤⁻-refl


import Data.List.Relation.Unary.All as All
record _≡⋎_ (A : PotentialFunction) (As : List PotentialFunction) : Set where
  field
    ₀≡ : All.All (λ Aᵢ → A .₀ ≡ Aᵢ .₀) As
    shared : (a : val (A .₀)) → foldr _+_ zero (All.reduce (λ {Aᵢ} ₀≡ᵢ → Aᵢ .Φᶜ (Eq.subst val ₀≡ᵢ a)) ₀≡) ≤ A .Φᶜ a
open _≡⋎_


import Data.Vec.Relation.Unary.All as VecAll
import Data.Maybe.Relation.Unary.All as MaybeAll

module Perm-Split-Φ {n : ℕ} where
  import Data.Vec.Relation.Unary.All.Properties as VAllP
  import Data.List.Relation.Unary.All.Properties as LAllP
  open Perm-Split {PotentialFunction} {n} _≡⋎_

  --  why isn't this in the stdlib?
  All-catMaybes⁻ : ∀ {xs} {P : PotentialFunction → Set} → All.All P (catMaybes xs) → All.All (MaybeAll.All P) xs
  All-catMaybes⁻ {xs = []} All.[] = All.[]
  All-catMaybes⁻ {xs = just x ∷ xs} (px All.∷ y) = (MaybeAll.just px) All.∷ All-catMaybes⁻ {xs = xs} y
  All-catMaybes⁻ {xs = nothing ∷ xs} y = MaybeAll.nothing All.∷ All-catMaybes⁻ {xs = xs} y

  as' : ∀ {m} (A : PotentialFunction) (As : Vec (Maybe PotentialFunction) m)
    → All.All (λ Aᵢ → A .₀ ≡ Aᵢ .₀) (catMaybes (toList As))
    → val (A .₀)
    → VecAll.All (MaybeAll.All (λ Aᵢ → val (Aᵢ .₀))) As
  as' _ As ₀≡ a = VAllP.toList⁻ (All-catMaybes⁻ (All.map (λ ₀≡ᵢ → Eq.subst val ₀≡ᵢ a) ₀≡))

  f : ∀ {Δᵢ : List PotentialFunction} {Aᵢ : Maybe PotentialFunction}
    → val (Tensorfy Δᵢ .₀)
    → MaybeAll.All (λ Aᵢ → val (Aᵢ .₀)) Aᵢ
    → val (Tensorfy (maybe (_∷ Δᵢ) Δᵢ Aᵢ) .₀)
  f {Δᵢ} {just _} δᵢ (MaybeAll.just aᵢ) = (aᵢ , δᵢ)
  f {Δᵢ} {nothing} δᵢ MaybeAll.nothing = δᵢ


  permute : ∀ {Δ Δs} → Δ ≡⊔ Δs → val (Tensorfy Δ .₀) → VecAll.All (λ Δᵢ → val (Tensorfy Δᵢ .₀)) Δs
  permute base triv = VAllP.tabulate⁺ λ _ → triv
  permute (to {A = A} As s S) (a , δ) = VecAll.zipWith f (permute S δ) (as' A As (s .₀≡) a)

  permute-Φ : ∀ {Δ Δs}
    → (S : Δ ≡⊔ Δs)
    → (δ : val (Tensorfy Δ .₀))
    → Vec.foldr′ _+_ zero (VecAll.reduce (λ {Δᵢ} → Tensorfy Δᵢ .Φᶜ) (permute S δ)) ≤ (Tensorfy Δ .Φᶜ δ)

  permute-Φ base δ =
    let open ≡-Reasoning in ≤-reflexive Function.$
    begin
      Vec.foldr′ _+_ zero (VecAll.reduce (λ {Δᵢ} → Tensorfy Δᵢ .Φᶜ) (VAllP.tabulate⁺ {n = n} (λ _ → triv)))
    ≡⟨ Eq.cong (Vec.foldr′ _+_ zero) (lemma₁ {n}) ⟩
      Vec.foldr′ _+_ zero (Vec.tabulate {n = n} (λ _ → zero))
    ≡⟨ lemma₂ {n} ⟩
      Tensorfy [] .Φᶜ δ
    ∎
    where
      lemma₁ : ∀ {m} → VecAll.reduce (λ {Δᵢ} → Tensorfy Δᵢ .Φᶜ) (VAllP.tabulate⁺ {n = m} {f = (λ _ → [])} (λ _ → triv)) ≡ Vec.tabulate {n = m} (λ _ → zero)
      lemma₁ {ℕ.zero} = refl
      lemma₁ {ℕ.suc m} = Eq.cong₂ Vec._∷_ refl (lemma₁ {m})

      lemma₂ : ∀ {m} → Vec.foldr′ _+_ zero (Vec.tabulate {n = m} (λ _ → zero)) ≡ zero
      lemma₂ {ℕ.zero} = refl
      lemma₂ {ℕ.suc m} = Eq.trans (Eq.cong (zero +_) (lemma₂ {m})) (+-identityʳ _)

  permute-Φ (to {Δ} {Δs} {A} As s S) (a , δ) =
    let open ≤-Reasoning in
    begin
      Vec.foldr′ _+_ zero (VecAll.reduce (λ {Δᵢ} → Tensorfy Δᵢ .Φᶜ) (VecAll.zipWith f (permute S δ) (as' A As (s .₀≡) a)))
    ≡⟨ lemma (permute S δ) (s .₀≡) ⟩
      foldr _+_ zero (All.reduce (λ {Aᵢ} ₀≡ᵢ → Aᵢ .Φᶜ (Eq.subst val ₀≡ᵢ a)) (s .₀≡))
      +
      Vec.foldr′ _+_ zero (VecAll.reduce (λ {Δᵢ} → Tensorfy Δᵢ .Φᶜ) (permute S δ))
    ≲⟨ +-mono (s .shared a) (permute-Φ S δ) ⟩
      A .Φᶜ a + Tensorfy Δ .Φᶜ δ
    ≡⟨⟩
      Tensorfy (A ∷ Δ) .Φᶜ (a , δ)
    ∎
    where
      lemma : ∀ {m Δs As}
        → (δs : VecAll.All (λ Δᵢ → val (Tensorfy Δᵢ .₀)) Δs)
        → (₀≡ : All.All (λ Aᵢ → A .₀ ≡ Aᵢ .₀) (catMaybes (toList As)))
        → Vec.foldr′ _+_ zero (VecAll.reduce (λ {Δᵢ} → Tensorfy Δᵢ .Φᶜ) (VecAll.zipWith f {n = m} δs (as' A As ₀≡ a)))
          ≡ foldr _+_ zero (All.reduce (λ {Aᵢ} ₀≡ᵢ → Aᵢ .Φᶜ (Eq.subst val ₀≡ᵢ a)) ₀≡)
          + Vec.foldr′ _+_ zero (VecAll.reduce (λ {Δᵢ} → Tensorfy Δᵢ .Φᶜ) δs)
      lemma {ℕ.zero} {Vec.[]} {Vec.[]} VecAll.[] All.[] = Eq.sym (+-identityʳ _)
      lemma {ℕ.suc m} {Δᵢ Vec.∷ Δs} {just Aᵢ Vec.∷ As} (δᵢ VecAll.∷ δs) (₀≡ᵢ All.∷ ₀≡) =
        let helper a b c d =
              let open SolverHelp in
              prove 4 ((v₁ ⊕ v₂) ⊕ (v₃ ⊕ v₄)) ((v₁ ⊕ v₃) ⊕ (v₂ ⊕ v₄))
              (a Vec.∷ b Vec.∷ c Vec.∷ d Vec.∷ Vec.[])
        in
        let open ≡-Reasoning in
        begin
          (Aᵢ .Φᶜ (Eq.subst val ₀≡ᵢ a) + Tensorfy Δᵢ .Φᶜ δᵢ) +
          Vec.foldr′ _+_ zero
            (VecAll.reduce (λ {Δᵢ} → Tensorfy Δᵢ .Φᶜ)
            (VecAll.zipWith (λ v v₁ → f v v₁) δs (as' A As ₀≡ a)))
        ≡⟨ Eq.cong (_ +_) (lemma {m} {Δs} {As} δs ₀≡) ⟩
          (Aᵢ .Φᶜ (Eq.subst val ₀≡ᵢ a) + Tensorfy Δᵢ .Φᶜ δᵢ) + (
            foldr _+_ zero (All.reduce (λ {Aᵢ} ₀≡ᵢ → Aᵢ .Φᶜ (Eq.subst val ₀≡ᵢ a)) ₀≡) +
            Vec.foldr′ _+_ zero (VecAll.reduce (λ {Δᵢ} → Tensorfy Δᵢ .Φᶜ) δs))
        ≡⟨ helper _ _ _ _ ⟩
          (Aᵢ .Φᶜ (Eq.subst val ₀≡ᵢ a) +
          foldr _+_ zero (All.reduce (λ {Aᵢ} ₀≡ᵢ → Aᵢ .Φᶜ (Eq.subst val ₀≡ᵢ a)) ₀≡))
          +
          (Tensorfy Δᵢ .Φᶜ δᵢ +
          Vec.foldr′ _+_ zero (VecAll.reduce (λ {Δᵢ} → Tensorfy Δᵢ .Φᶜ) δs))
        ∎
      lemma {ℕ.suc m} {Δᵢ Vec.∷ Δs} {nothing Vec.∷ As} (δᵢ VecAll.∷ δs) ₀≡ =
        let helper a b c =
              let open SolverHelp in
              prove 3 (v₁ ⊕ (v₂ ⊕ v₃)) (v₂ ⊕ (v₁ ⊕ v₃))
              (a Vec.∷ b Vec.∷ c Vec.∷ Vec.[])
        in
        let open ≡-Reasoning in
        begin
          Tensorfy Δᵢ .Φᶜ δᵢ +
          Vec.foldr′ _+_ zero
            (VecAll.reduce (λ {Δᵢ} → Tensorfy Δᵢ .Φᶜ)
            (VecAll.zipWith (λ v v₁ → f v v₁) δs (as' A As ₀≡ a)))
        ≡⟨ Eq.cong (_ +_) (lemma {m} {Δs} {As} δs ₀≡) ⟩
          (Tensorfy Δᵢ .Φᶜ δᵢ) + (
            foldr _+_ zero (All.reduce (λ {Aᵢ} ₀≡ᵢ → Aᵢ .Φᶜ (Eq.subst val ₀≡ᵢ a)) ₀≡) +
            Vec.foldr′ _+_ zero (VecAll.reduce (λ {Δᵢ} → Tensorfy Δᵢ .Φᶜ) δs))
        ≡⟨ helper _ _ _ ⟩
          (foldr _+_ zero (All.reduce (λ {Aᵢ} ₀≡ᵢ → Aᵢ .Φᶜ (Eq.subst val ₀≡ᵢ a)) ₀≡))
          +
          (Tensorfy Δᵢ .Φᶜ δᵢ + Vec.foldr′ _+_ zero (VecAll.reduce (λ {Δᵢ} → Tensorfy Δᵢ .Φᶜ) δs))
        ∎
open Perm-Split-Φ using (permute; permute-Φ)



module Perm-Split-Φ₂ where
  open Perm-Split {n = 2} _≡⋎_

  split : ∀ {Δ Δ₁ Δ₂} → Δ ≡⊔ (Δ₁ Vec.∷ Vec.[ Δ₂ ]) → val (Tensorfy Δ .₀) → val (Tensorfy Δ₁ .₀) × val (Tensorfy Δ₂ .₀)
  split s δ with permute s δ
  ... | (δ₁ VecAll.∷ δ₂ VecAll.∷ VecAll.[]) = δ₁ , δ₂

  split-Φ : ∀ {Δ Δ₁ Δ₂}
    → (s : Δ ≡⊔ (Δ₁ Vec.∷ Vec.[ Δ₂ ]))
    → (δ : val (Tensorfy Δ .₀))
    → ((let δ₁ , δ₂ = split s δ in Tensorfy Δ₁ .Φᶜ δ₁ + Tensorfy Δ₂ .Φᶜ δ₂) ≤ Tensorfy Δ .Φᶜ δ)
  split-Φ {Δ} {Δ₁} {Δ₂} s δ = ≤-trans (≤-reflexive (Eq.sym help)) (permute-Φ s δ)
    where
      help : Vec.foldr′ _+_ zero (VecAll.reduce (λ {Δᵢ} → Tensorfy Δᵢ .Φᶜ) (permute s δ)) ≡ (let δ₁ , δ₂ = split s δ in Tensorfy Δ₁ .Φᶜ δ₁ + Tensorfy Δ₂ .Φᶜ δ₂)
      help with permute s δ
      ... | (δ₁ VecAll.∷ δ₂ VecAll.∷ VecAll.[]) = Eq.cong ((Tensorfy Δ₁ .Φᶜ δ₁) +_) (+-identityʳ _)
open Perm-Split-Φ₂

module Perm-Split-Φ₁ where
  open Perm-Split {n = 1} _≡⋎_

  weaken : ∀ {Δ Δ'} → Δ ≡⊔ (Vec.[ Δ' ]) → val (Tensorfy Δ .₀) → val (Tensorfy Δ' .₀)
  weaken s δ with permute s δ
  ... | δ' VecAll.∷ VecAll.[] = δ'

  weaken-Φ : ∀ {Δ Δ'}
    → (s : Δ ≡⊔ Vec.[ Δ' ])
    → (δ : val (Tensorfy Δ .₀))
    → (Tensorfy Δ' .Φᶜ (weaken s δ) ≤ Tensorfy Δ .Φᶜ δ)
  weaken-Φ {Δ} {Δ'} s δ = ≤-trans (≤-reflexive (Eq.sym help)) (permute-Φ s δ)
    where
      help : Vec.foldr′ _+_ zero (VecAll.reduce (λ {Δᵢ} → Tensorfy Δᵢ .Φᶜ) (permute s δ)) ≡ (Tensorfy Δ' .Φᶜ (weaken s δ))
      help with permute s δ
      ... | (δ' VecAll.∷ VecAll.[]) = +-identityʳ _
open Perm-Split-Φ₁

-- cut
_⋎_⨾□ᵐ_ : ∀ {Δ Δ₁ Δ₂ q q₁ q₂ A B}
  → Perm-Split._≡⋎ᵐ_ {n = 2} _≡⋎_ (Δ , q) ((Δ₁ , q₁) Vec.∷ Vec.[ (Δ₂ , q₂) ])
  → MultiSquare Δ₁ q₁ A
  → MultiSquare (A ∷ Δ₂) q₂ B
  → MultiSquare Δ q B
((s , _) ⋎ e ⨾□ᵐ f) .top δ =
  let δ₁ , δ₂ = split s δ in
  bind (F _) (e .top δ₁) (λ a → f .top (a , δ₂))
((s , _) ⋎ e ⨾□ᵐ f) .bot δ =
  let δ₁ , δ₂ = split s δ in
  f .bot (e .bot δ₁ , δ₂)
(_⋎_⨾□ᵐ_ {Δ} {Δ₁} {Δ₂} {q} {q₁} {q₂} {A} {B} (s , t) e f) .square δ =
  let δ₁ , δ₂ = split s δ in
  let helper a b c d =
        let open SolverHelp in
        prove 4 ((v₁ ⊕ v₂) ⊕ (v₃ ⊕ v₄)) ((v₁ ⊕ v₃) ⊕ (v₂ ⊕ v₄))
        (a Vec.∷ b Vec.∷ c Vec.∷ d Vec.∷ Vec.[])
  in
  let open ≤⁻-Reasoning (F _) in
  begin
    bind (F _) (e .top δ₁) (λ a → bind (F _) (f .top (a , δ₂)) (Φ B))
  ≲⟨ bind-monoʳ-≤⁻ (e .top δ₁) (λ a → f .square (a , δ₂)) ⟩
    bind (F _) (e .top δ₁) (λ a → step (F _) (A .Φᶜ a + Tensorfy Δ₂ .Φᶜ δ₂ + q₂) (ret (f .bot (a , δ₂))))
  ≡⟨ Eq.cong (bind (F _) (e .top δ₁)) (funext (λ a → step-ret-congˡ _ (+-assoc _ _ _))) ⟩
    bind (F _) (bind (F _) (e .top δ₁) (Φ A)) (λ a → step (F _) (Tensorfy Δ₂ .Φᶜ δ₂ + q₂) (ret (f .bot (a , δ₂))))
  ≲⟨ bind-monoˡ-≤⁻ (λ a' → step (F _) _ (ret _)) (e .square δ₁) ⟩
    bind {A .₀} (F _)
      (step (F _) (Tensorfy Δ₁ .Φᶜ δ₁ + q₁) (ret (e .bot δ₁)))
      (λ a → step (F _) (Tensorfy Δ₂ .Φᶜ δ₂ + q₂) (ret (f .bot (a , δ₂))))
  ≡⟨⟩
    step (F _)
      (Tensorfy Δ₁ .Φᶜ δ₁ + q₁ + (Tensorfy Δ₂ .Φᶜ δ₂ + q₂))
      (ret (f .bot (e .bot δ₁ , δ₂)))
  ≡⟨ step-ret-congˡ _ (helper _ _ _ _) ⟩
    step (F _)
      ((Tensorfy Δ₁ .Φᶜ δ₁ + Tensorfy Δ₂ .Φᶜ δ₂) + (q₁ + q₂))
      (ret (f .bot (e .bot δ₁ , δ₂)))
  ≲⟨ step-monoˡ-≤⁻ (ret _) (+-mono (split-Φ s δ) (≤-trans (≤-reflexive (Eq.cong (q₁ +_) (Eq.sym (+-identityʳ _)))) t)) ⟩
    step (F _)
      (Tensorfy Δ .Φᶜ δ + q)
      (ret (f .bot (e .bot δ₁ , δ₂)))
  ∎


-- weaken
_W_ : ∀ {Δ Δ' q q' A}
  → Perm-Split._≡⋎ᵐ_ {n = 1} _≡⋎_ (Δ , q) Vec.[ (Δ' , q') ]
  → MultiSquare Δ' q' A
  → MultiSquare Δ q A
((s , _) W e) .top δ = e .top (weaken s δ)
((s , _) W e) .bot δ = e .bot  (weaken s δ)
((s , t) W e) .square δ = ≤⁻-trans (e .square (weaken s δ)) (step-monoˡ-≤⁻ (ret _) (+-mono (weaken-Φ s δ) (≤-trans (≤-reflexive (Eq.sym (+-identityʳ _))) t)))

_Wₗ_ : ∀ {Δ q A}
  → Perm-Split._≡⋎ᵐ_ {n = 0} _≡⋎_ (Δ , q) Vec.[]
  → MultiSquare [] zero A
  → MultiSquare Δ q A
(_ Wₗ e) .top _ = e .top triv
(_ Wₗ e) .bot _ = e .bot triv
(_ Wₗ e) .square δ = ≤⁻-trans (e .square triv) (step-monoˡ-≤⁻ (ret _) (zero/min (_ + _)))


giralf-list : ℂ × ℂ → PotentialFunction → PotentialFunction
giralf-list _ A .₀ = list (A .₀)
giralf-list _ A .Φᶜ [] = zero
giralf-list (p₁ , p₂) A .Φᶜ (h ∷ t) = p₁ + A .Φᶜ h + giralf-list (shift (p₁ , p₂)) A .Φᶜ t


open Giralf
giralf : Giralf

giralf .𝓒 = PotentialFunction
giralf ._⨾_⊢_ = MultiSquare
giralf ._≡ᶜ⋎_ = _≡⋎_

giralf .idᵍ {Δ} {q} {A} s = s W lemma
  where
    lemma : MultiSquare [ A ] zero A
    lemma .top (a , _) = ret a
    lemma .bot (a , _) = a
    lemma .square (a , _) = ≤⁻-reflexive (step-ret-congˡ a (Eq.sym (+-identityʳ _)))


-- Charge effect
giralf .charge {A = A} p s e = s W (refl ⋎ e ⨾□ lemma)
  where
    lemma : Square A p A
    lemma .top = step (F _) p ∘ ret
    lemma .bot = Function.id
    lemma .square a = ≤⁻-reflexive (step-ret-congˡ _ (+-comm _ _))


-- F type
giralf .Fᵍ X .₀ = X
giralf .Fᵍ X .Φᶜ _ = zero
giralf .retᵍ {q} {X} s x = s Wₗ constᵍ x
giralf .bindᵍ {Δ₂ = Δ₂} {q₂ = q₂} {X} {A} s e e' = s ⋎ e ⨾□ᵐ lemma
  where
    lemma : MultiSquare ((giralf .Fᵍ X) ∷ Δ₂) q₂ A
    lemma .top (x , δ₂) = e' x .top δ₂
    lemma .bot (x , δ₂) = e' x .bot δ₂
    lemma .square (x , δ₂) = ≤⁻-trans (e' x .square δ₂) (≤⁻-reflexive (step-ret-congˡ _ (Eq.cong (_+ q₂) (Eq.sym (+-identityˡ _)))))


-- Potential
giralf ._⋊ᵍ_ p A .₀ = A .₀
giralf ._⋊ᵍ_ p A .Φᶜ a = p + A .Φᶜ a
giralf .store {A = A} p s e = s W (refl ⋎ e ⨾□ store-square)
  where
    store-square : Square A p (giralf ._⋊ᵍ_ p A)
    store-square .top = ret
    store-square .bot = Function.id
    store-square .square a = ≤⁻-reflexive (step-ret-congˡ _ (+-comm _ _))
giralf .release {Δ₂ = Δ₂} {p} {q₂ = q₂} {A} {B} s e e' = s ⋎ e ⨾□ᵐ lemma
  where
    lemma : MultiSquare ((giralf ._⋊ᵍ_ p A) ∷ Δ₂) q₂ B
    lemma .top = e' .top
    lemma .bot = e' .bot
    lemma .square (a , δ₂) =
      let helper a b c d =
            let open SolverHelp in
            prove 4 ((v₁ ⊕ v₂) ⊕ (v₃ ⊕ v₄)) (((v₃ ⊕ v₁) ⊕ v₂) ⊕ v₄)
            (a Vec.∷ b Vec.∷ c Vec.∷ d Vec.∷ Vec.[])
      in
      let open ≤⁻-Reasoning (F _) in
      begin
        bind (F _) (e' .top (a , δ₂)) (Φ B)
      ≲⟨ e' .square (a , δ₂) ⟩
         step (F _) (A .Φᶜ a + Tensorfy Δ₂ .Φᶜ δ₂ + (p + q₂)) (ret (e' .bot (a , δ₂)))
      ≡⟨ step-ret-congˡ _ (helper _ _ _ _) ⟩
        step (F _) (p + A .Φᶜ a + Tensorfy Δ₂ .Φᶜ δ₂ + q₂) (ret (e' .bot (a , δ₂)))
      ∎

-- Void and Sum
giralf .⊥ᵍ .₀ = ⊥⁺
giralf .⊥ᵍ .Φᶜ ()
giralf .absurdᵍ {C = C} s e = s W (Eq.sym (+-identityʳ _) ⋎ e ⨾□ lemma)
  where
    lemma : Square (giralf .⊥ᵍ) zero C
    lemma .top ()
    lemma .bot ()
    lemma .square ()

giralf ._⊎ᵍ_ A B .₀ = A .₀ ⊎⁺ B .₀
giralf ._⊎ᵍ_ A B .Φᶜ = [ A .Φᶜ , B .Φᶜ ]′
giralf .inj₁ᵍ {Δ' = Δ'} {q' = q'} {A} {B} s e = s W lemma
  where
    lemma : MultiSquare Δ' q' (giralf ._⊎ᵍ_ A B)
    lemma .top δ = bind (F _) (e .top δ) λ a → ret (inj₁ a)
    lemma .bot = inj₁ ∘ e .bot
    lemma .square δ = bind-monoˡ-≤⁻ (ret ∘ inj₁) (e .square δ)
giralf .inj₂ᵍ {Δ' = Δ'} {q' = q'} {A} {B} s e = s W lemma
  where
    lemma : MultiSquare Δ' q' (giralf ._⊎ᵍ_ A B)
    lemma .top δ = bind (F _) (e .top δ) λ b → ret (inj₂ b)
    lemma .bot = inj₂ ∘ e .bot
    lemma .square δ = bind-monoˡ-≤⁻ (ret ∘ inj₂) (e .square δ)
giralf .caseᵍ {Δ₂ = Δ₂} {q₂ = q₂} {A} {B} {C} s e e₁ e₂ = s ⋎ e ⨾□ᵐ lemma
  where
    lemma : MultiSquare ((giralf ._⊎ᵍ_ A B) ∷ Δ₂) q₂ C
    lemma .top (inj₁ a , δ₂) = e₁ .top (a , δ₂)
    lemma .top (inj₂ b , δ₂) = e₂ .top (b , δ₂)
    lemma .bot (inj₁ a , δ₂) = e₁ .bot (a , δ₂)
    lemma .bot (inj₂ b , δ₂) = e₂ .bot (b , δ₂)
    lemma .square (inj₁ a , δ₂) = e₁ .square (a , δ₂)
    lemma .square (inj₂ b , δ₂) = e₂ .square (b , δ₂)


-- Top and Tensor Product
giralf .⊤ᵍ = ⊤
giralf .trivᵍ {q} s = s Wₗ constᵍ triv
giralf .checkᵍ {Δ₂ = Δ₂} {q₂ = q₂} {C} s e e' = s ⋎ e ⨾□ᵐ lemma
  where
    lemma : MultiSquare (⊤ ∷ Δ₂) q₂ C
    lemma .top (triv , δ₂) = e' .top δ₂
    lemma .bot (triv , δ₂) = e' .bot δ₂
    lemma .square (triv , δ₂) = ≤⁻-trans (e' .square δ₂) (≤⁻-reflexive (step-ret-congˡ _ (Eq.cong (_+ q₂) (Eq.sym (+-identityˡ _)))))

giralf ._⊗ᵍ_ = _⊗_
giralf .tensorᵍ {Δ₂ = Δ₂} {q₂ = q₂} {A} {B} s e₁ e₂ = s ⋎ e₁ ⨾□ᵐ lemma
  where
    lemma : MultiSquare (A ∷ Δ₂) q₂ (A ⊗ B)
    lemma .top (a , δ₂) = bind (F _) (e₂ .top δ₂) λ b → ret (a , b)
    lemma .bot (a , δ₂) = (a , e₂ .bot δ₂)
    lemma .square (a , δ₂) =
      let helper a b c =
            let open SolverHelp in
            prove 3 ((v₁ ⊕ v₂) ⊕ v₃) ((v₃ ⊕ v₁) ⊕ v₂)
            (a Vec.∷ b Vec.∷ c Vec.∷ Vec.[])
      in
      let open ≤⁻-Reasoning (F _) in
      begin
        bind (F _) (e₂ .top δ₂) (λ b → Φ (A ⊗ B) (a , b))
      ≡⟨ Eq.cong (bind (F _) (e₂ .top δ₂)) (funext (λ _ → step-ret-congˡ _ (+-comm _ _))) ⟩
        bind (F _)
          (bind (F _) (e₂ .top δ₂) (Φ B))
          (λ b → step (F _) (A .Φᶜ a) (ret (a , b)))
      ≲⟨ bind-monoˡ-≤⁻ (λ b → step (F _) _ (ret _)) (e₂ .square δ₂) ⟩
        bind (F _)
          (step (F (B .₀)) (Tensorfy Δ₂ .Φᶜ δ₂ + q₂) (ret (e₂ .bot δ₂)))
          (λ b → step (F _) (A .Φᶜ a) (ret (a , b)))
      ≡⟨ step-ret-congˡ _ (helper _ _ _) ⟩
        step (F _) (A .Φᶜ a + Tensorfy Δ₂ .Φᶜ δ₂ + q₂) (ret (a , e₂ .bot δ₂))
      ∎
giralf .splitᵍ {Δ₂ = Δ₂} {q₂ = q₂} {A} {B} {C} s e e' = s ⋎ e ⨾□ᵐ lemma
  where
    lemma : MultiSquare ((giralf ._⊗ᵍ_ A B) ∷ Δ₂) q₂ C
    lemma .top ((a , b) , δ₂) = e' .top (a , (b , δ₂))
    lemma .bot ((a , b) , δ₂) = e' .bot (a , (b , δ₂))
    lemma .square ((a , b) , δ₂) =
      ≤⁻-trans (e' .square (a , (b , δ₂))) (≤⁻-reflexive (step-ret-congˡ _ (Eq.cong (_+ q₂) (Eq.sym (+-assoc _ _ _)))))


-- Lists
giralf .listᵍ = giralf-list
giralf .nilᵍ s = s Wₗ constᵍ []
giralf .consᵍ {Δ = Δ} {A = A} {ps} s eₕ eₜ = (Eq.sym (+-identityʳ _)) ⋎ (giralf .tensorᵍ s (refl ⋎ eₕ ⨾□ lemma₁) eₜ) ⨾□ lemma₂
  where
    lemma₁ : Square A (ps .proj₁) (giralf ._⋊ᵍ_ (ps .proj₁) A)
    lemma₁ .top = ret
    lemma₁ .bot = Function.id
    lemma₁ .square a = ≤⁻-reflexive (step-ret-congˡ _ (+-comm _ _))

    lemma₂ : Square ((giralf ._⋊ᵍ_ (ps .proj₁) A) ⊗ (giralf-list (shift ps) A)) zero (giralf-list ps A)
    lemma₂ .top (h , t) = ret (h ∷ t)
    lemma₂ .bot (h , t) = h ∷ t
    lemma₂ .square (h , t) = ≤⁻-refl

giralf .foldrᵍ {A = A} {ps} {B} s e e[] e∷ = s W ((Eq.sym (+-identityʳ _)) ⋎ e ⨾□ lemma)
  where
    lemma : ∀ {rs} → Square (giralf-list rs A) zero (B rs)
    lemma .top [] = e[] .top triv
    lemma .top (h ∷ t) = bind (F _) (lemma .top t) (λ b' → e∷ .top ((b' , h , triv)))
    lemma .bot [] = e[] .bot triv
    lemma .bot (h ∷ t) = e∷ .bot (lemma .bot t , h , triv)
    lemma .square [] = e[] .square triv
    lemma {rs} .square (h ∷ t) =
      let helper₁ a b c =
            let open SolverHelp in
            prove 3 ((v₁ ⊕ (v₂ ⊕ id)) ⊕ v₃) (v₁ ⊕ (v₂ ⊕ v₃))
            (a Vec.∷ b Vec.∷ c Vec.∷ Vec.[])
      in
      let helper₂ a b c =
            let open SolverHelp in
            prove 3 (v₁ ⊕ (v₂ ⊕ v₃)) ((v₃ ⊕ v₂) ⊕ v₁)
            (a Vec.∷ b Vec.∷ c Vec.∷ Vec.[])
      in
      let open ≤⁻-Reasoning (F _) in
      begin
        (
          bind (F _) (lemma .top t) λ b →
          bind (F _) (e∷ .top (b , h , triv)) (Φ (B rs))
        )
      ≲⟨ bind-monoʳ-≤⁻ (lemma .top t) (λ b → e∷ .square (b , h , triv)) ⟩
        (
          bind (F _) (lemma .top t) λ b →
          bind (F _) (Φ ((B (shift rs)) ⊗ (A ⊗ ⊤)) (b , h , triv)) (step (F _) (rs .proj₁) ∘ ret ∘ e∷ .bot)
        )
      ≡⟨ Eq.cong (bind (F _) (lemma {shift rs} .top t)) (funext λ b → step-ret-congˡ _ (helper₁ _ _ _)) ⟩
        bind (F _)
          (bind (F _) (lemma .top t) (Φ (B (shift rs))))
          (
            λ b' →
            bind (F _) (Φ A h) λ h' →
            step (F _) (rs .proj₁) (ret (e∷ .bot (b' , h' , triv)))
          )
      ≲⟨ bind-monoˡ-≤⁻ (λ b' → bind (F _) (Φ A h) (λ h' → step (F _) (rs .proj₁) (ret (e∷ .bot (b' , h' , triv))))) (lemma {shift rs} .square t) ⟩
        bind (F _)
          (bind (F (B (shift rs) .₀)) (Φ (giralf-list (shift rs) A) t) (ret ∘ lemma .bot))
          (
            λ b' →
            bind (F _) (Φ A h) λ h' →
            step (F _) (rs .proj₁) (ret (e∷ .bot (b' , h' , triv)))
          )
      ≡⟨ step-ret-congˡ (lemma .bot (h ∷ t)) (helper₂ _ _ _) ⟩
        bind (F _)
          (Φ (giralf-list rs A) (h ∷ t))
          (ret ∘ lemma .bot)
      ∎
