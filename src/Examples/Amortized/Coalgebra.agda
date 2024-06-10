{-# OPTIONS --rewriting #-}

module Examples.Amortized.Coalgebra where

open import Algebra.Cost

costMonoid = ℕ-CostMonoid
open CostMonoid costMonoid using (ℂ)

open import Calf costMonoid
open import Calf.Data.Product
open import Data.Sum using ([_,_])
open import Calf.Data.Bool
open import Calf.Data.Maybe
open import Calf.Data.Nat as Nat using (ℕ; zero; suc; 2+; nat; _+_; _∸_; pred; _*_; _^_; _>_; _⊔_)
import Data.Nat.Properties as Nat
open import Calf.Data.List
open import Data.Nat.PredExp2
import Data.List.Properties as List
open import Calf.Data.Equality as Eq using (_≡_; refl; _≡⁺_; ≡⁺-syntax; _≡⁻_; ≡⁻-syntax; module ≡-Reasoning)
open import Function hiding (_⇔_)
open import Relation.Nullary


record Functor : Set where
  field
    ₀ : tp⁻ → tp⁻
    ₁ : (cmp X → cmp Y) → cmp (₀ X) → cmp (₀ Y)
open Functor

record Coalgebra (H⁻ : Functor) : Set where
  field
    Carrier : tp⁻
    coalg : cmp Carrier → cmp (H⁻ .₀ Carrier)

_≥⁻_ : cmp X → cmp X → □
e₁ ≥⁻ e₂ = e₂ ≤⁻ e₁

record CoalgebraMorphism {H⁻ : Functor} (χ ψ : Coalgebra H⁻) : Set where
  open Coalgebra
  field
    Φ : cmp (χ .Carrier) → cmp (ψ .Carrier)
    coalg : (ψ .coalg ∘ Φ) ≡ (H⁻ .₁ Φ ∘ χ .coalg)



module Weekly (A : tp⁺) where
  H⁻ : Functor
  H⁻ .₀ X = X
  H⁻ .₁ Φ x = Φ x

  spec : Coalgebra H⁻
  Coalgebra.Carrier spec = F unit
  Coalgebra.coalg spec e =
    bind (F _) e λ _ →
    step (F _) 1 (ret triv)

  open import Data.Fin
  import Data.Fin.Properties as Fin

  aux : Fin 7 → cmp (F (meta⁺ (Fin 7)))
  aux zero = step (F _) 7 (ret (suc (suc (suc (suc (suc (suc zero)))))))
  aux (suc n) = ret (inject₁ n)

  impl : Coalgebra H⁻
  Coalgebra.Carrier impl = F (meta⁺ (Fin 7))
  Coalgebra.coalg impl e = bind (F _) e aux

  amortized-analysis : CoalgebraMorphism impl spec
  CoalgebraMorphism.Φ amortized-analysis e =
    bind (F _) e λ n →
    step (F _) (7 ∸ toℕ n) (ret triv)
  CoalgebraMorphism.coalg amortized-analysis =
    funext λ e → Eq.cong (bind (F _) e) (funext lemma)
    where
      lemma : (n : Fin 7) →
        step (F _) ((7 ∸ toℕ n) Nat.+ 1) (ret triv) ≡
        (bind (F _) (aux n) λ n' → step (F _) (7 ∸ toℕ n') (ret triv))
      lemma zero = Eq.refl
      lemma (suc n) = Eq.cong (λ x → step (F _) x (ret triv)) $
        let open ≡-Reasoning in
        begin
          (6 ∸ toℕ n) Nat.+ 1
        ≡⟨ Nat.+-comm _ 1 ⟩
          1 Nat.+ (6 ∸ toℕ n)
        ≡⟨ Nat.+-∸-assoc 1 (Fin.toℕ≤n n) ⟨
          (1 Nat.+ 6) ∸ toℕ n
        ≡⟨⟩
          7 ∸ toℕ n
        ≡⟨ Eq.cong (7 ∸_) (Fin.toℕ-inject₁ n) ⟨
          7 ∸ toℕ (inject₁ n)
        ∎


n≤2n∸1 : ∀ n → {{Nat.NonZero n}} → n Nat.≤ 2 * n ∸ 1
n≤2n∸1 (suc n) rewrite Nat.+-identityʳ n = Nat.m≤n+m (suc n) n

2*n≡n+n : ∀ n → 2 * n ≡ n + n
2*n≡n+n n = Eq.cong (n +_) (Nat.+-identityʳ n)

2*n∸n≡n : ∀ n → 2 * n ∸ n ≡ n
2*n∸n≡n n =
  let open ≡-Reasoning in
  begin
    2 * n ∸ n
  ≡⟨ Eq.cong (_∸ n) (2*n≡n+n n) ⟩
    n + n ∸ n
  ≡⟨ Nat.+-∸-assoc n (Nat.≤-refl {n}) ⟩
    n + (n ∸ n)
  ≡⟨ Eq.cong (n +_) (Nat.n∸n≡0 n) ⟩
    n + 0
  ≡⟨ Nat.+-identityʳ n ⟩
    n
  ∎

suc[2pred[n]]≡pred[2n] : ∀ n → {{Nat.NonZero n}} → suc (2 * pred n) ≡ pred (2 * n)
suc[2pred[n]]≡pred[2n] n =
  let open ≡-Reasoning in
  begin
    suc (2 * pred n)
  ≡⟨ Eq.cong suc (2*n≡n+n (pred n)) ⟩
    suc (pred n + pred n)
  ≡⟨⟩
    suc (pred n) + pred n
  ≡⟨ Eq.cong (_+ pred n) (Nat.suc-pred n) ⟩
    n + pred n
  ≡⟨ Nat.+-∸-assoc n (Nat.>-nonZero⁻¹ n) ⟨
    pred (n + n)
  ≡⟨ Eq.cong pred (2*n≡n+n n) ⟨
    pred (2 * n)
  ∎


module DynamicArray (A : tp⁺) where
  H⁻ : Functor
  H⁻ .₀ X = Π A λ _ → X
  H⁻ .₁ Φ x a = Φ (x a)

  spec : Coalgebra H⁻
  Coalgebra.Carrier spec = F unit
  Coalgebra.coalg spec e a =
    bind (F _) e λ _ →
    step (F _) 3 (ret triv)


  X₀ = (Σ⁺ nat λ log[s] → Σ⁺ (list A) λ l → meta⁺ (pred[2^ log[s] ] Nat.≤ length l × length l Nat.< pred[2^ suc log[s] ]))

  empty : val X₀
  empty = 0 , [] , Nat.z≤n , Nat.s≤s Nat.z≤n

  aux : val X₀ → cmp (Π A λ _ → F X₀)
  aux (log[s] , l , h₀ , h₁) a with suc (length l) Nat.≟ pred[2^ suc log[s] ]
  ... | no ¬h' =
    step (F _) 1 $
    ret (log[s] , a ∷ l , Nat.m≤n⇒m≤1+n h₀ , Nat.≤∧≢⇒< h₁ ¬h')
  ... | yes h' =
    step (F _) (2 + length (a ∷ l)) $
    ret (suc log[s] , a ∷ l , Nat.≤-reflexive (Eq.sym h') , lemma₁)
    where
      lemma₁ : length (a ∷ l) Nat.< pred[2^ suc (suc log[s]) ]
      lemma₁ =
        let open Nat.≤-Reasoning in
        begin-strict
          length (a ∷ l)
        ≡⟨⟩
          suc (length l)
        <⟨ Nat.s<s h₁ ⟩
          suc (pred (2 ^ suc log[s]))
        ≡⟨ Nat.suc-pred (2 ^ suc log[s]) {{Nat.m^n≢0 2 (suc log[s])}} ⟩
          2 ^ suc log[s]
        ≤⟨ n≤2n∸1 (2 ^ suc log[s]) {{Nat.m^n≢0 2 (suc log[s])}} ⟩
          2 * 2 ^ suc log[s] ∸ 1
        ≡⟨⟩
          2 ^ suc (suc log[s]) ∸ 1
        ≡⟨⟩
          pred[2^ suc (suc log[s]) ]
        ∎

  impl : Coalgebra H⁻
  Coalgebra.Carrier impl = F X₀
  Coalgebra.coalg impl e a = bind (F _) e λ x₀ → aux x₀ a

  open import Tactic.Cong

  amortized-analysis : CoalgebraMorphism impl spec
  CoalgebraMorphism.Φ amortized-analysis e =
    bind (F _) e λ (log[s] , l , _) →
    step (F _) (suc (2 * length l) ∸ pred[2^ suc log[s] ]) (ret triv)
  CoalgebraMorphism.coalg amortized-analysis =
    funext λ e → funext λ a → Eq.cong (bind (F _) e) (funext (lemma a))
    where
      lemma : (a : val A) (x₀@(log[s] , l , _) : val X₀) →
        step (F unit) ((suc (2 * length l) ∸ pred[2^ suc log[s] ]) + 3) (ret triv) ≡
        (bind (F _) (aux x₀ a) λ (log[s]' , l' , _) → step (F _) (suc (2 * length l') ∸ pred[2^ suc log[s]' ]) (ret triv))
      lemma a (log[s] , l , h₀ , h₁) with suc (length l) Nat.≟ pred[2^ suc log[s] ]
      ... | no ¬h' = Eq.cong (λ c → step (F _) c (ret triv)) $
        let
          h₀' : pred[2^ suc log[s] ] Nat.≤ suc (2 * length l)
          h₀' =
            let open Nat.≤-Reasoning in
            begin
              pred[2^ suc log[s] ]
            ≡⟨⟩
              pred (2 * 2 ^ log[s])
            ≡⟨ suc[2pred[n]]≡pred[2n] (2 ^ log[s]) {{Nat.m^n≢0 2 log[s]}} ⟨
              suc (2 * pred[2^ log[s] ])
            ≤⟨ Nat.s≤s (Nat.*-monoʳ-≤ 2 h₀) ⟩
              suc (2 * length l)
            ∎
        in
        let open ≡-Reasoning in
        begin
          (suc (2 * length l) ∸ pred[2^ suc log[s] ]) + 3
        ≡⟨ Nat.+-comm _ 3 ⟩
          3 + (suc (2 * length l) ∸ pred[2^ suc log[s] ])
        ≡⟨⟩
          1 + (2 + (suc (2 * length l) ∸ pred[2^ suc log[s] ]))
        ≡⟨ Eq.cong (1 +_) (Nat.+-∸-assoc 2 {suc (2 * length l)} {pred[2^ suc log[s] ]} h₀') ⟨
          1 + (suc (2 + 2 * length l) ∸ pred[2^ suc log[s] ])
        ≡⟨ Eq.cong (λ c → 1 + (suc c ∸ pred[2^ suc log[s] ])) (Nat.*-distribˡ-+ 2 1 (length l)) ⟨
          1 + (suc (2 * suc (length l)) ∸ pred[2^ suc log[s] ])
        ≡⟨⟩
          1 + (suc (2 * length (a ∷ l)) ∸ pred[2^ suc log[s] ])
        ∎
      ... | yes h' = Eq.cong (λ c → step (F _) c (ret triv)) $
        let open ≡-Reasoning in
        begin
          (suc (2 * length l) ∸ pred[2^ suc log[s] ]) + 3
        ≡⟨ Nat.+-comm _ 3 ⟩
          3 + (suc (2 * length l) ∸ pred[2^ suc log[s] ])
        ≡⟨ cong! h' ⟨
          3 + (suc (2 * length l) ∸ length (a ∷ l))
        ≡⟨⟩
          3 + (2 * length l ∸ length l)
        ≡⟨ Eq.cong (3 +_) (2*n∸n≡n (length l)) ⟩
          3 + length l
        ≡⟨⟩
          2 + length (a ∷ l)
        ≡⟨ Nat.+-identityʳ _ ⟨
          (2 + length (a ∷ l)) + 0
        ≡⟨ cong! (Nat.n∸n≡0 (suc (2 * length (a ∷ l)))) ⟨
          (2 + length (a ∷ l)) + (suc (2 * length (a ∷ l)) ∸ suc (2 * length (a ∷ l)))
        ≡⟨ cong! h' ⟩
          (2 + length (a ∷ l)) + (suc (2 * length (a ∷ l)) ∸ suc (2 * pred[2^ suc log[s] ]))
        ≡⟨ cong! (suc[2pred[n]]≡pred[2n] (2 ^ suc log[s]) {{Nat.m^n≢0 2 (suc log[s])}}) ⟩
          (2 + length (a ∷ l)) + (suc (2 * length (a ∷ l)) ∸ pred (2 * 2 ^ (suc log[s])))
        ≡⟨⟩
          (2 + length (a ∷ l)) + (suc (2 * length (a ∷ l)) ∸ pred[2^ suc (suc log[s]) ])
        ∎



_⊎⁻_ : tp⁻ → tp⁻ → tp⁻
X ⊎⁻ Y = Σ⁻ bool (if_then Y else X)


module Stack (A : tp⁺) where
  H⁻ : Functor
  H⁻ .₀ X = prod⁻ (Π A λ _ → X) ((A ⋉ X) ⊎⁻ F unit)
  proj₁ (H⁻ .₁ Φ x) a = Φ (proj₁ x a)
  proj₂ (H⁻ .₁ Φ x) with proj₂ x
  ... | false , a , x = false , a , Φ x
  ... | true  , e     = true  , e

  spec-aux : (l : val (list A)) → cmp ((A ⋉ F (list A)) ⊎⁻ F unit)
  spec-aux []      = true  , ret triv
  spec-aux (x ∷ l) = false , x , ret l

  spec : Coalgebra H⁻
  Coalgebra.Carrier spec = F (list A)
  proj₁ (Coalgebra.coalg spec e) a =
    bind (F _) e λ l →
    step (F _) 3 $
    ret (a ∷ l)
  proj₂ (Coalgebra.coalg spec e) =
    bind ((A ⋉ F _) ⊎⁻ F unit) e λ l →
    step ((A ⋉ F _) ⊎⁻ F unit) 2 $
    spec-aux l


  X₀ = Σ⁺ nat λ log[s] → Σ⁺ (list A) λ l → meta⁺ (pred[2^ log[s] ] Nat.≤ length l × length l Nat.< pred[2^ 2+ log[s] ])

  empty : val X₀
  empty = 0 , [] , Nat.z≤n , Nat.s≤s Nat.z≤n

  aux₁ : val X₀ → cmp (Π A λ _ → F X₀)
  aux₁ (log[s] , l , h₀ , h₁) a with suc (length l) Nat.≟ pred[2^ 2+ log[s] ]
  ... | no ¬h' =
    step (F _) 1 $
    ret (log[s] , a ∷ l , Nat.m≤n⇒m≤1+n h₀ , Nat.≤∧≢⇒< h₁ ¬h')
  ... | yes h' =
    step (F _) (2 + length (a ∷ l)) $
    ret (suc log[s] , a ∷ l , Nat.≤-trans (pred[2^]-mono (Nat.n≤1+n (suc log[s]))) (Nat.≤-reflexive (Eq.sym h')) , lemma₁)
    where
      lemma₁ : length (a ∷ l) Nat.< pred[2^ 2+ (suc log[s]) ]
      lemma₁ =
        let open Nat.≤-Reasoning in
        begin-strict
          length (a ∷ l)
        ≡⟨⟩
          suc (length l)
        <⟨ Nat.s<s h₁ ⟩
          suc (pred (2 ^ 2+ log[s]))
        ≡⟨ Nat.suc-pred (2 ^ 2+ log[s]) {{Nat.m^n≢0 2 (2+ log[s])}} ⟩
          2 ^ 2+ log[s]
        ≤⟨ n≤2n∸1 (2 ^ 2+ log[s]) {{Nat.m^n≢0 2 (2+ log[s])}} ⟩
          2 * 2 ^ 2+ log[s] ∸ 1
        ≡⟨⟩
          2 ^ 2+ (suc log[s]) ∸ 1
        ≡⟨⟩
          pred[2^ 2+ (suc log[s]) ]
        ∎

  aux₂ : val X₀ → cmp ((A ⋉ F X₀) ⊎⁻ F unit)
  aux₂ (log[s] , [] , h₀ , h₁) = true , ret triv
  aux₂ (log[s] , l@(a ∷ l') , h₀ , h₁) with length l Nat.≟ pred[2^ log[s] ]
  ... | no ¬h' =
    false , a , ret (log[s] , l' , Nat.s≤s⁻¹ (Nat.≤∧≢⇒< h₀ (Eq.≢-sym ¬h')) , Nat.≤-trans (Nat.n≤1+n (length l)) h₁)
  aux₂ (suc log[s] , l@(a ∷ l') , h₀ , h₁) | yes h' =
    false , a , ret (log[s] , l' , lemma₂ , Nat.≤-trans (Nat.≤-reflexive h') (pred[2^]-mono (Nat.n≤1+n (suc log[s]))))
    where
      lemma₂ : pred[2^ log[s] ] Nat.≤ length l'
      lemma₂ =
        let open Nat.≤-Reasoning in
        begin
          pred[2^ log[s] ]
        ≤⟨ Nat.m≤m+n pred[2^ log[s] ] pred[2^ log[s] ] ⟩
          pred[2^ log[s] ] + pred[2^ log[s] ]
        ≡⟨⟩
          pred (suc (pred[2^ log[s] ] + pred[2^ log[s] ]))
        ≡⟨ Eq.cong pred (pred[2^suc[n]] log[s]) ⟩
          pred pred[2^ suc log[s] ]
        ≤⟨ Nat.pred-mono-≤ h₀ ⟩
          length l'
        ∎


  impl : Coalgebra H⁻
  Coalgebra.Carrier impl = F X₀
  proj₁ (Coalgebra.coalg impl e) a = bind (F _) e λ x₀ → aux₁ x₀ a
  proj₂ (Coalgebra.coalg impl e) = bind ((A ⋉ F X₀) ⊎⁻ F unit) e aux₂

  amortized-analysis : CoalgebraMorphism impl spec
  CoalgebraMorphism.Φ amortized-analysis e =
    bind (F _) e λ (log[s] , l , h₀ , h₁) →
    step (F _) ((suc (2 * length l) ∸ pred[2^ 2+ log[s] ]) ⊔ (pred[2^ suc log[s] ] ∸ length l)) (ret l)
  CoalgebraMorphism.coalg amortized-analysis =
    funext λ e → Eq.cong₂ _,_ (funext λ a → Eq.cong (bind (F _) e) (funext (lemma₁ a))) (lemma₂ e)
    where
      lemma₁ : (a : val A) (x₀@(log[s] , l , _) : val X₀) →
        step (F _) (((suc (2 * length l) ∸ pred[2^ 2+ log[s] ]) ⊔ (pred[2^ suc log[s] ] ∸ length l)) + 3) (ret (a ∷ l)) ≡
        (bind (F _) (aux₁ x₀ a) λ (log[s]' , l' , _) → step (F _) (suc (2 * length l') ∸ pred[2^ 2+ log[s]' ] ⊔ (pred[2^ suc log[s]' ] ∸ length l')) (ret l'))
      lemma₁ a (log[s] , l , h₀ , h₁) with suc (length l) Nat.≟ pred[2^ 2+ log[s] ]
      ... | no ¬h' = Eq.cong (λ c → step (F _) c (ret (a ∷ l))) $
        let open Nat.≤-Reasoning in
        let
          baz : pred[2^ 2+ log[s] ] Nat.≤ suc (2 * length l)
          baz =
            begin
              pred[2^ 2+ log[s] ]
            ≡⟨⟩
              2 ^ (2+ log[s]) ∸ 1
            ≤⟨ {!   !} ⟩
              suc (2 ^ (suc log[s]) ∸ 2)
            ≡⟨ Eq.cong suc (Nat.*-distribˡ-∸ 2 (2 ^ log[s]) 1) ⟨
              suc (2 * (2 ^ log[s] ∸ 1))
            ≡⟨⟩
              suc (2 * pred[2^ log[s] ])
            ≤⟨ Nat.s≤s (Nat.*-monoʳ-≤ 2 h₀) ⟩
              suc (2 * length l)
            ∎

          foo : 2 + (suc (2 * length l) ∸ pred[2^ 2+ log[s] ]) ≡ suc (2 * length (a ∷ l)) ∸ pred[2^ 2+ log[s] ]
          foo =
            begin-equality
              2 + (suc (2 * length l) ∸ pred[2^ 2+ log[s] ])
            ≡⟨ Nat.+-∸-assoc 2 {suc (2 * length l)} {pred[2^ 2+ log[s] ]} baz ⟨
              (3 + 2 * length l) ∸ pred[2^ 2+ log[s] ]
            ≡⟨ Eq.cong (λ c → suc c ∸ pred[2^ 2+ log[s] ]) (Nat.*-distribˡ-+ 2 1 (length l)) ⟨
              suc (2 * length (a ∷ l)) ∸ pred[2^ 2+ log[s] ]
            ∎

          bar : 2 + (pred[2^ suc log[s] ] ∸ length l) ≡ pred[2^ suc log[s] ] ∸ length (a ∷ l)
          bar =
            begin-equality
              {!   !}
            ≡⟨ {!   !} ⟩
              {!   !}
            ∎
        in
        begin-equality
          ((suc (2 * length l) ∸ pred[2^ 2+ log[s] ]) ⊔ (pred[2^ suc log[s] ] ∸ length l)) + 3
        ≡⟨ Nat.+-comm _ 3 ⟩
          3 + ((suc (2 * length l) ∸ pred[2^ 2+ log[s] ]) ⊔ (pred[2^ suc log[s] ] ∸ length l))
        ≡⟨⟩
          1 + (2 + ((suc (2 * length l) ∸ pred[2^ 2+ log[s] ]) ⊔ (pred[2^ suc log[s] ] ∸ length l)))
        ≡⟨ Eq.cong (1 +_) (Nat.+-distribˡ-⊔ 2 (suc (2 * length l) ∸ pred[2^ 2+ log[s] ]) (pred[2^ suc log[s] ] ∸ length l)) ⟩
          1 + ((2 + (suc (2 * length l) ∸ pred[2^ 2+ log[s] ])) ⊔ (2 + (pred[2^ suc log[s] ] ∸ length l)))
        -- ≡⟨ Eq.cong (1 +_) (Nat.+-∸-assoc 2 {suc (2 * length l)} {pred[2^ suc log[s] ]} h₀') ⟨
        --   1 + (suc (2 + 2 * length l) ∸ pred[2^ suc log[s] ])
        -- ≡⟨ Eq.cong (λ c → 1 + (suc c ∸ pred[2^ suc log[s] ])) (Nat.*-distribˡ-+ 2 1 (length l)) ⟨
        --   1 + (suc (2 * suc (length l)) ∸ pred[2^ suc log[s] ])
        ≡⟨ Eq.cong (1 +_) (Eq.cong₂ _⊔_ foo bar) ⟩
          1 + ((suc (2 * length (a ∷ l)) ∸ pred[2^ 2+ log[s] ]) ⊔ (pred[2^ suc log[s] ] ∸ length (a ∷ l)))
        ∎
      ... | yes h' = {!   !}

      lemma₂ : (e : cmp (F X₀)) → {!   !} ≡ {!   !}
      lemma₂ = {!   !}
