{-# OPTIONS --type-in-type #-}

module Examples.SequenceV where

open import Cubical.Foundations.Function
open import Cubical.Foundations.Path
open import Cubical.Foundations.Univalence
import Cubical.Data.List.Properties as List
import Cubical.Data.Nat.Properties as Nat
import Cubical.Data.Bool.Properties as Bool


open import Cubical.Data.Sigma using (map-snd; ΣPathP; Σ-contractFst; Σ-cong-snd)

open import Calf.Core.Abstract
open import Calf.Value hiding (empty)
open import Calf.Value.Abstraction
open import Calf.Value.Glue using (fracture-isEquiv)
open import Calf.Value.List
open import Calf.Value.Nat
open import Calf.Value.Bool
open import Calf.Value.Product
open import Calf.Value.Sigma
open import Calf.Value.Open
open import Calf.Value.Closed as ●
open import Calf.Value.Empty
open import Calf.Value.Unit

_≗_ : X → X → 𝒱
x ≗ x' = ◯ (x ≡ x')

isContr◦ : 𝒱 → 𝒱
isContr◦ X = Σ[ x ∈ X ] (∀ x' → x ≗ x')

module _ (E : 𝒱) (isSetE : isSet E) where

  record MonoidOn : 𝒱 where
    field
      Carrier : 𝒱
      is-set : isSet Carrier
      empty : Carrier
      append : Carrier → Carrier → Carrier
      identityˡ : (x : Carrier) → append empty x ≗ x
      identityʳ : (x : Carrier) → append x empty ≗ x
      assoc : (x y z : Carrier) → append (append x y) z ≗ append x (append y z)

    field
      singleton : E → Carrier
  open MonoidOn public


  record Hom (M N : MonoidOn) : 𝒱 where
    field
      Carrier : M .Carrier → N .Carrier
      empty : Carrier (M .empty) ≗ N .empty
      append : ∀ m m' → Carrier (M .append m m') ≗ N .append (Carrier m) (Carrier m')
      singleton : ∀ e → Carrier (M .singleton e) ≗ N .singleton e
  open Hom public

  Hom-path
    : {M N : MonoidOn} {f f' : Hom M N}
    → ((m : M .Carrier) → f .Carrier m ≡ f' .Carrier m)
    → f ≡ f'
  Hom-path p i .Carrier = funExt p i
  Hom-path {M} {N} {f} {f'} p i .empty abs =
    isProp→PathP
      (λ i → N .is-set (funExt p i (M .empty)) (N .empty))
      (f .empty abs) (f' .empty abs)
      i
  Hom-path {M} {N} {f} {f'} p i .append m m' abs =
    isProp→PathP
      (λ i →
         N .is-set (funExt p i (M .append m m'))
         (N .append (funExt p i m) (funExt p i m')))
      (f .append m m' abs) (f' .append m m' abs)
    i
  Hom-path {M} {N} {f} {f'} p i .singleton e abs =
    isProp→PathP
      (λ i → N .is-set (funExt p i (M .singleton e)) (N .singleton e))
      (f .singleton e abs) (f' .singleton e abs)
      i

  record Sequence : 𝒱 where
    field
      monoid-on : MonoidOn
      mapreduce : (M : MonoidOn) → isContr◦ (Hom monoid-on M)
  open Sequence public

  module Examples (S : Sequence) where
    T : 𝒱
    T = S .monoid-on .Carrier

    -- reverse empty = empty
    -- reverse (append s₁ s₂) = append (reverse s₂) (reverse s₁)
    -- reverse (singleton e) = singleton e

    rev : T → T
    rev =
      S .mapreduce
        (record
           { Carrier = T
           ; is-set = S .monoid-on .is-set
           ; empty = S .monoid-on .empty
           ; append = λ s₁ s₂ → S .monoid-on .append s₂ s₁
           ; identityˡ = S .monoid-on .identityʳ
           ; identityʳ = S .monoid-on .identityˡ
           ; assoc = λ s₁ s₂ s₃ → sym ∘ S .monoid-on .assoc s₃ s₂ s₁
           ; singleton = S .monoid-on .singleton
           })
        .fst
        .Carrier

    rev-rev : ∀ s → rev (rev s) ≗ s
    rev-rev = {!   !}

  list-sequence : Sequence
  list-sequence .monoid-on .Carrier = List E
  list-sequence .monoid-on .is-set = isSetList isSetE
  list-sequence .monoid-on .empty = []
  list-sequence .monoid-on .append = _++_
  list-sequence .monoid-on .identityˡ _ abs = refl
  list-sequence .monoid-on .identityʳ _ abs = List.++-unit-r _
  list-sequence .monoid-on .assoc l _ _ abs = List.++-assoc l _ _
  list-sequence .monoid-on .singleton = [_]
  list-sequence .mapreduce M .fst .Carrier =
    foldr
      (λ e m → M .append (M .singleton e) m)
      (M .empty)
  list-sequence .mapreduce M .fst .empty abs = refl
  list-sequence .mapreduce M .fst .append m m' abs = sym (append-lemma m m' abs)
    where
      append-lemma :
        (m m' : list-sequence .monoid-on .Carrier) →
          M .append (list-sequence .mapreduce M .fst .Carrier m)
            (list-sequence .mapreduce M .fst .Carrier m')
          ≗
          list-sequence .mapreduce M .fst .Carrier
            (list-sequence .monoid-on .append m m')
      append-lemma [] m' abs =
        M .identityˡ (list-sequence .mapreduce M .fst .Carrier m') abs
      append-lemma (x ∷ m) m' abs =
          M .append (list-sequence .mapreduce M .fst .Carrier (x ∷ m))
           (list-sequence .mapreduce M .fst .Carrier m')
        ≡⟨
           M .assoc (M .singleton x)
             (list-sequence .mapreduce M .fst .Carrier m)
             (list-sequence .mapreduce M .fst .Carrier m') abs
         ⟩
          M .append (M .singleton x)
            (M .append (list-sequence .mapreduce M .fst .Carrier m)
            (list-sequence .mapreduce M .fst .Carrier m'))
        ≡⟨ cong (M .append (M .singleton x)) (append-lemma m m' abs) ⟩
          list-sequence .mapreduce M .fst .Carrier
           (list-sequence .monoid-on .append (x ∷ m) m')
        ∎
  list-sequence .mapreduce M .fst .singleton = λ e → M .identityʳ (M .singleton e)
  list-sequence .mapreduce M .snd f abs = Hom-path carrier-lemma
    where
      carrier-lemma :  (l : List E) →
        foldr (λ e → M .append (M .singleton e)) (M .empty) l ≡
        f .Carrier l
      carrier-lemma [] = sym (f .empty abs)
      carrier-lemma (x ∷ xs) =
          list-sequence .mapreduce M .fst .Carrier (x ∷ xs)
        ≡⟨ cong (λ hole →
                   M .append hole (list-sequence .mapreduce M .fst .Carrier xs))
                (sym (f .singleton x abs))
         ⟩
          M .append (f .Carrier (list-sequence .monoid-on .singleton x))
            (list-sequence .mapreduce M .fst .Carrier xs)
        ≡⟨ ( cong (λ hole → M .append (f .Carrier [ x ]) hole) (carrier-lemma xs)) ⟩
          M .append (f .Carrier [ x ]) (f .Carrier xs)
        ≡⟨ ( sym (f .append [ x ] xs abs)) ⟩
          f .Carrier (x ∷ xs)
        ∎


  module Tree where
    module Abstraction where
      data Tree : 𝒱 where
        leaf : E → Tree
        null : Tree
        node : Tree → Tree → Tree

      χ : Tree → List E
      χ (leaf e) = [ e ]
      χ null = []
      χ (node t₁ t₂) = χ t₁ ++ χ t₂

      module TreePath where

        Cover : Tree → Tree → 𝒱
        Cover (leaf e1) (leaf e2) = e1 ≡ e2
        Cover null null = 1ᵛ
        Cover (node t1 t2) (node t1' t2') = Cover t1 t1' × Cover t2 t2'
        Cover (leaf _) null = 0ᵛ
        Cover (leaf _) (node _ _) = 0ᵛ
        Cover null (leaf _) = 0ᵛ
        Cover null (node _ _) = 0ᵛ
        Cover (node _ _) (leaf _) = 0ᵛ
        Cover (node _ _) null = 0ᵛ

        reflCode : (t : Tree) → Cover t t
        reflCode (leaf _) = refl
        reflCode null = tt
        reflCode (node t1 t2) = reflCode t1 , reflCode t2

        encode : (t1 t2 : Tree) → (p : t1 ≡ t2) → Cover t1 t2
        encode t1 _ = J (λ t2 _ → Cover t1 t2) (reflCode t1)

        encodeRefl : (t : Tree) → encode t t refl ≡ reflCode t
        encodeRefl t1 = JRefl (λ t2 _ → Cover t1 t2) (reflCode t1)

        decode : (t1 t2 : Tree) → Cover t1 t2 → t1 ≡ t2
        decode (leaf e1) (leaf e2) p = cong leaf p
        decode null null _ = refl
        decode (node t1 t2) (node t1' t2') (p1 , p2) =
          cong₂ node (decode t1 t1' p1) (decode t2 t2' p2)
        decode (leaf _) null ()
        decode (leaf _) (node _ _) ()
        decode null (leaf _) ()
        decode null (node _ _) ()
        decode (node _ _) (leaf _) ()
        decode (node _ _) null ()

        decodeRefl : (t : Tree) → decode t t (reflCode t) ≡ refl
        decodeRefl (leaf e) = refl
        decodeRefl null = refl
        decodeRefl (node t1 t2) =
          cong₂ (λ p1 p2 → cong₂ node p1 p2) (decodeRefl t1) (decodeRefl t2)

        decodeEncode : (t1 t2 : Tree) → (p : t1 ≡ t2)
          → decode t1 t2 (encode t1 t2 p) ≡ p
        decodeEncode t1 _ =
          J (λ t2 p → decode t1 t2 (encode t1 t2 p) ≡ p)
            (cong (decode t1 t1) (encodeRefl t1) ∙ decodeRefl t1 )

        isOfHLevelCover : (n : HLevel) (p : isOfHLevel (suc (suc n)) E)
          (t1 t2 : Tree) → isOfHLevel (suc n) (Cover t1 t2)
        isOfHLevelCover n p (leaf e1) (leaf e2) = p e1 e2
        isOfHLevelCover n p null null = (isProp→isOfHLevelSuc n isProp1ᵛ)
        isOfHLevelCover n p (node t1 t2) (node t1' t2') =
          isOfHLevelΣ (suc n) (isOfHLevelCover n p t1 t1')
            (λ _ → isOfHLevelCover n p t2 t2')
        isOfHLevelCover n p (leaf _) null = (isProp→isOfHLevelSuc n isProp0ᵛ)
        isOfHLevelCover n p (leaf _) (node _ _) = (isProp→isOfHLevelSuc n isProp0ᵛ)
        isOfHLevelCover n p null (leaf _) = (isProp→isOfHLevelSuc n isProp0ᵛ)
        isOfHLevelCover n p null (node _ _) = (isProp→isOfHLevelSuc n isProp0ᵛ)
        isOfHLevelCover n p (node _ _) (leaf _) = (isProp→isOfHLevelSuc n isProp0ᵛ)
        isOfHLevelCover n p (node _ _) null = (isProp→isOfHLevelSuc n isProp0ᵛ)

      isOfHLevelTree : (n : HLevel) → isOfHLevel (suc (suc n)) E
        → isOfHLevel (suc (suc n)) Tree
      isOfHLevelTree n ofLevel t1 t2 =
        isOfHLevelRetract (suc n)
          (TreePath.encode t1 t2)
          (TreePath.decode t1 t2)
          (TreePath.decodeEncode t1 t2)
          (TreePath.isOfHLevelCover n ofLevel t1 t2)

      isSetTree : isSet E → isSet Tree
      isSetTree = isOfHLevelTree 0

      tree-sequence : Sequence
      tree-sequence .monoid-on .Carrier = Abstraction χ
      tree-sequence .monoid-on .is-set =
        isSetAbstraction (isSetTree isSetE) (isSetList isSetE)
      tree-sequence .monoid-on .empty = triangle χ null [] refl
      tree-sequence .monoid-on .append = square₂ χ χ χ node _++_ λ _ _ → refl
      tree-sequence .monoid-on .identityˡ x abs = Abstraction-path-open abs refl
      tree-sequence .monoid-on .identityʳ = {!   !}
      tree-sequence .monoid-on .assoc = {!   !}
      tree-sequence .monoid-on .singleton = {!   !}
      tree-sequence .mapreduce = {!   !}

    module Quotient where
      data Tree• : 𝒱 where
        leaf : E → Tree•
        null : Tree•
        node : Tree• → Tree• → Tree•
        identityˡ• : ∀ t → node null t ≗ t
        identityʳ• : ∀ t → node t null ≗ t
        assoc• : ∀ t₁ t₂ t₃ → node (node t₁ t₂) t₃ ≗ node t₁ (node t₂ t₃)
        squash : isSet Tree•

      tree-sequence : Sequence
      tree-sequence .monoid-on .Carrier = Tree•
      tree-sequence .monoid-on .is-set = squash
      tree-sequence .monoid-on .empty = null
      tree-sequence .monoid-on .append = node
      tree-sequence .monoid-on .identityˡ = identityˡ•
      tree-sequence .monoid-on .identityʳ = {!   !}
      tree-sequence .monoid-on .assoc = {!   !}
      tree-sequence .monoid-on .singleton = leaf
      tree-sequence .mapreduce = {!   !}

  module RedBlackTree where
    data Color : 𝒱 where
      red black : Color

    variable
      c₁ c₂ c : Color
      n₁ n₂ n : ℕ

    data LeafInvariant : Color → ℕ → 𝒱 where
      black : LeafInvariant black zero

    data Invariant : (c₁ c₂ c : Color) (n₁ n₂ n : ℕ) → 𝒱 where
      black : Invariant c₁ c₂ black n n (suc n)
      red : Invariant black black red n n n

    module Abstraction where
      data IRBT : Color → ℕ → 𝒱 where
        leaf : LeafInvariant c n → E → IRBT c n
        null : LeafInvariant c n → IRBT c n
        node :
            Invariant c₁ c₂ c n₁ n₂ n
          → IRBT c₁ n₁ → IRBT c₂ n₂ → IRBT c n

      RBT : 𝒱
      RBT = Σ[ c ∈ Color ] Σ[ n ∈ ℕ ] IRBT c n

      elements : IRBT c n → List E
      elements (leaf _ e) = [ e ]
      elements (null _) = []
      elements (node _ t₁ t₂) = elements t₁ ++ elements t₂

      χ : RBT → List E
      χ (_ , _ , t) = elements t

      rbt-sequence : Sequence
      rbt-sequence .monoid-on .Carrier = Abstraction χ
      rbt-sequence .monoid-on .is-set = isSetAbstraction {!   !} (isSetList isSetE)
      rbt-sequence .monoid-on .empty = {!   !}
      rbt-sequence .monoid-on .append = {! node ?  !}
      rbt-sequence .monoid-on .identityˡ = {!   !}
      rbt-sequence .monoid-on .identityʳ = {!   !}
      rbt-sequence .monoid-on .assoc = {!   !}
      rbt-sequence .monoid-on .singleton = {!   !}
      rbt-sequence .mapreduce = {!   !}

    module Quotient where
      LeafInvariant• : ● Color → ● ℕ → 𝒱
      LeafInvariant• c• n• = {!   !}

      Invariant• : (c₁• c₂• c• : ● Color) (n₁• n₂• n• : ● ℕ) → 𝒱
      Invariant• = {!   !}

      variable
        c₁• c₂• c• : ● Color
        n₁• n₂• n• : ● ℕ

      data Tree• : ● Color → ● ℕ → 𝒱 where
        leaf : LeafInvariant• c• n• → E → Tree• c• n•
        null : LeafInvariant• c• n• → Tree• c• n•
        node :
            Invariant• c₁• c₂• c• n₁• n₂• n•
          → Tree• c₁• n₁• → Tree• c₂• n₂• → Tree• c• n•
        identityˡ• : ∀ inv linv t
          → node {c₁•} {c•} {c•} {n₁•} {n•} {n•} inv (null linv) t ≗ t
        identityʳ• : {!   !}
        assoc• : {!   !}
        squash : isSet (Tree• c₁• n₁•)

      RBT• : 𝒱
      RBT• = Σ[ c• ∈ ● Color ] Σ[ n• ∈ ● ℕ ] Tree• c• n•

      rbt-sequence : Sequence
      rbt-sequence .monoid-on .Carrier = RBT•
      rbt-sequence .monoid-on .is-set =
        isSetΣ (isSet● {!   !}) λ _ →
        isSetΣ (isSet● isSetℕ) λ _ →
        squash
      rbt-sequence .monoid-on .empty = η• black , η• zero , null {!   !}
      rbt-sequence .monoid-on .append = {!   !}
      rbt-sequence .monoid-on .identityˡ = {!   !}
      rbt-sequence .monoid-on .identityʳ = {!   !}
      rbt-sequence .monoid-on .assoc = {!   !}
      rbt-sequence .monoid-on .singleton = {!   !}
      rbt-sequence .mapreduce = {!   !}


demo : List ℕ
demo =
  M.rev (app (sing 1) (sing 7))
  where
    S = list-sequence ℕ isSetℕ -- Tree.Quotient.tree-sequence ℕ isSetℕ
    app = S .monoid-on .append
    sing = S .monoid-on .singleton
    emp = S .monoid-on .empty
    module M = Examples ℕ isSetℕ S
