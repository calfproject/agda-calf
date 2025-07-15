{-# OPTIONS --rewriting #-}

-- open import Examples.Sorting.Sequential.Comparable

module Examples.Scan where 

-- NOTE: getting rid of comparable causes errors with A and also + for some reason??

-- open Comparable M
-- open import Examples.Sorting.Sequential.Core M

open import Algebra.Cost

parCostMonoid = ℕ²-ParCostMonoid
open ParCostMonoid parCostMonoid

open import Calf costMonoid
open import Calf.Parallel parCostMonoid
open import Calf.Data.Nat
open import Calf.Data.List using (list; []; _∷_; _∷ʳ_; [_]; length; _++_; reverse ; splitAt  ) renaming ( map to listmap )
open import Calf.Data.IsBounded costMonoid
open import Calf.Data.IsBoundedG costMonoid
open import Calf.Data.Product 

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; _≢_; module ≡-Reasoning)
open import Data.Nat as Nat using (_+_; _⊔_)
open import Data.List.Properties using (length-++)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_; prep; refl; ↭-sym)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties using (↭-length)


open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; module ≡-Reasoning)
open import Data.Sum using (inj₁; inj₂)
open import Function
import Data.Nat.Properties as N
open import Data.Nat.Square
open import Data.Nat.Log2


record ◯-isMonoid {A : tp⁺} (f : cmp (Π (A ×⁺ A) (λ _ → F A))) (ε : val A) : Set where 
  field 
    identityʳ : {a : val A} → ◯ ( f(a , ε) ≡ ret a)
    identityˡ : {a : val A} → ◯ ( f(ε , a) ≡ ret a )
    assoc : {a b c : val A} → ◯ ((bind (F _) (f (a , b)) λ left → f (left , c)) ≡ (bind (F _) (f (b , c)) λ right → f (a , right)))

record ◯-Monoid (A : tp⁺) : Set where 
  field 
    f : cmp (Π (A ×⁺ A) (λ _ → F A))
    identity : val A 
    isMonoid : ◯-isMonoid f identity

scan/bruteforce/help : {A : tp⁺} → cmp (Π (U (Π (A ×⁺ A) (λ _ → F A))) (λ _ → Π A (λ _ → (Π (list A) (λ _ →  F (list A ×⁺ A))))))
scan/bruteforce/help f e [] = ret ([] , e)
scan/bruteforce/help f e (x ∷ L) = 
  step (F _) (1 , 1) (bind (F _) (f (e , x)) (λ y → 
    bind (F _) (scan/bruteforce/help f y L) λ { (ys , r) →  
      ret ( e ∷ ys , r )}))

scan/bruteforce : {A : tp⁺} → ◯-Monoid A → cmp (Π (list A)  (λ _ → F (list A ×⁺ A)))
scan/bruteforce M L = scan/bruteforce/help (◯-Monoid.f M) (◯-Monoid.identity M) L

+-0-Monoid : ◯-Monoid nat 
+-0-Monoid .◯-Monoid.f  = λ (m , n) → ret (m + n)
+-0-Monoid .◯-Monoid.identity = 0
+-0-Monoid .◯-Monoid.isMonoid .◯-isMonoid.identityˡ {a} u = refl

+-0-Monoid .◯-Monoid.isMonoid .◯-isMonoid.identityʳ {a} u = Eq.cong ret (N.+-comm a 0)
+-0-Monoid .◯-Monoid.isMonoid .◯-isMonoid.assoc {a} {b} {c} u = Eq.cong ret (N.+-assoc a b c)


-- scan/bruteforce/example : val (U (F (meta⁺ (Σ (Calf.Data.List.List ℕ) (λ x → ℕ)))))
-- scan/bruteforce/example = scan/bruteforce +-0-Monoid ( 1 ∷ 2 ∷ [] )


scan/accum-independent :  (l : val (list A)) → 
                          (f :  cmp (Π (A ×⁺ A) (λ _ → F A))) → 
                          (a : val A) → 
                          ((a b : val A) → IsBounded A (f (a , b)) (0 , 0)) → 
                          IsBounded (list A ×⁺ A) (scan/bruteforce/help f a l) (length l , length l)
scan/accum-independent [] f a h = ≤⁻-refl
scan/accum-independent (x ∷ l) f a h = 
  let open ≤⁻-Reasoning cost in 
  begin 
    step (F _) (1 , 1) (bind (F _) (f (a , x)) (λ res →
      bind (F _) (scan/bruteforce/help f res l) (λ _ → 
        ret triv)))
  ≲⟨ step-monoʳ-≤⁻ ((1 , 1)) 
      (bind-monoʳ-≤⁻ (f (a , x)) 
        (λ res → scan/accum-independent l f res h)) ⟩
    step (F _) ((1 , 1)) 
      (bind (F _) (f (a , x)) (λ res →
        step⋆ (length l , length l)))
  ≲⟨ step-monoʳ-≤⁻ ((1 , 1)) 
      (bind-monoˡ-≤⁻ ((λ res →
        step⋆ (length l , length l))) (h a x)) ⟩
    step (F _) ((1 , 1)) (bind (F _) (step⋆ (0 , 0)) ((λ res →
       step⋆ (length l , length l)))) 
  ≡⟨⟩
    step⋆ (1 + length l , 1 + length l)  
  ∎

scan/bruteforce/cost :  
      (m : ◯-Monoid A) → 
      ((a b : val A) → IsBounded A (◯-Monoid.f m (a , b)) (0 , 0)) → 
      (l : val (list A)) →
      IsBounded (list A ×⁺ A) (scan/bruteforce m l) (length l , length l)
scan/bruteforce/cost m h l = scan/accum-independent l (◯-Monoid.f m) (◯-Monoid.identity m) h

-- reimplemented split from Split.agda in mergesort example

pair : {A : tp⁺} → tp⁺
pair {A} = list A ×⁺ list A

split/type : {A : tp⁺} → val nat → val nat → val (list A) → tp⁺
split/type {A} k k' l = Σ⁺ (pair {A}) λ (l₁ , l₂) → meta⁺ (length l₁ ≡ k × length l₂ ≡ k' × l ↭ (l₁ ++ l₂))

split/clocked : {A : tp⁺} → cmp (Π nat λ k → Π nat λ k' → Π (list A) λ l → Π (meta⁺ (k + k' ≡ length l)) λ _ → F (split/type {A} k k' l))
split/clocked zero    k' l        refl = ret (([] , l) , refl , refl , refl)
split/clocked {A} (suc k) k' (x ∷ xs) h    =
  bind (F (split/type {A} (suc k) k' (x ∷ xs))) (split/clocked {A} k k' xs (N.suc-injective h)) λ ((l₁ , l₂) , h₁ , h₂ , xs↭l₁++l₂) →
  ret ((x ∷ l₁ , l₂) , Eq.cong suc h₁ , h₂ , prep x xs↭l₁++l₂)


split/clocked/cost :  (A : tp⁺) → 
                      (k k' : val nat) → 
                      (l : val (list A)) → 
                      (p : val (meta⁺ (k + k' ≡ length l))) → 
                      IsBounded (split/type {A} k k' l) (split/clocked {A} k k' l p) (0 , 0)
split/clocked/cost A zero k' l refl = ≤⁻-refl
split/clocked/cost A (suc k) k' (x ∷ xs) h = bind-monoˡ-≤⁻ (λ x₁ → ret triv) (split/clocked/cost A k k' xs (N.suc-injective h))


split : (A : tp⁺) → cmp (Π (list A) λ l → F (split/type {A} ⌊ length l /2⌋ ⌈ length l /2⌉ l))
split A l = split/clocked {A} ⌊ length l /2⌋ ⌈ length l /2⌉ l (N.⌊n/2⌋+⌈n/2⌉≡n (length l))


split/cost : (A : tp⁺) → (l : val (list A)) → IsBounded (split/type {A} ⌊ length l /2⌋ ⌈ length l /2⌉ l) (split A l) (0 , 0)
split/cost A l = split/clocked/cost A ⌊ length l /2⌋ ⌈ length l /2⌉ l (N.⌊n/2⌋+⌈n/2⌉≡n (length l))
-- yay for sequences and just taking a smaller slice of the array 

mapList : {A B : tp⁺} → 
  cmp (Π (U (Π A λ _ → F B)) (λ _ → 
       Π (list A) (λ l → 
       F (Σ⁺ (list B) λ l' → meta⁺ (length l ≡ length l')))))
mapList f [] = ret ([] , refl)
mapList {A} {B} f (x ∷ xs) = 
  bind (F _) (mapList {A} {B} f xs) λ (l' , p) → 
    bind (F _) (f x) λ x' → 
      ret (x' ∷ l' , Eq.cong suc p)

-- ideally, we want to express that mapList is parallelizable
mapList/bound : {A : tp⁺} → 
                (l : val (list A)) → 
                (f :  cmp (Π (A ×⁺ A) (λ _ → F A))) → 
                ((a b : val A) → IsBounded A (f (a , b)) (0 , 0)) → 
                (a : val A) → 
                IsBounded  (Σ⁺ (list A) λ l' → meta⁺ (length l ≡ length l')) (mapList {A} (λ x → f (a , x)) l) (0 , 0) 
mapList/bound [] f h a = ≤⁻-refl
mapList/bound {A} (x ∷ l) f h a = 
  let open ≤⁻-Reasoning cost in
  begin
    (bind (F _) (mapList {A} (λ x₁ → f (a , x₁)) l) λ (l' , p) → 
    bind (F _) (f (a , x)) λ x' → 
      ret triv) 
  ≲⟨ bind-monoˡ-≤⁻ ((((λ _ → bind (F (meta⁺ Unit)) (f (a , x)) (λ a₂ → ret triv))))) (mapList/bound l f h a) ⟩ 
    ((bind (F _) (step⋆ (0 , 0) ) λ _ → 
    bind (F _) (f (a , x)) λ x' → 
      ret triv))
  ≲⟨ bind-monoʳ-≤⁻ (step⋆ (0 , 0)) (λ _ → h a x) ⟩ 
    (((bind (F _) (step⋆ (0 , 0) ) λ _ → 
    bind (F _) (step⋆ (0 , 0) ) λ x' → 
      ret triv))) 
  ≡⟨⟩ 
    step⋆ (0 , 0) 
  ∎

-- we def need to express that this is parallelizable
lem : {A : tp⁺} → (l l₁ l₂ l₁' l₂' r' : val (list A)) → 
            l ↭ l₁ ++ l₂ →
            length l₁ ≡ length l₁' →
            length l₂ ≡ length l₂' →
            length l₂' ≡ length r' →
            length l ≡ length (l₁' ++ r')
lem l l₁ l₂ l₁' l₂' r' l↭l₁++l₂ ∣l₁∣≡∣l₁'∣ ∣l₂∣≡∣l₂'∣ ∣l₂'∣≡∣r'∣ = 
  let open ≡-Reasoning in 
  begin 
    length l 
  ≡⟨ ↭-length l↭l₁++l₂ ⟩
    length (l₁ ++ l₂)
  ≡⟨ length-++ l₁ ⟩
    length l₁ + length l₂
  ≡⟨ Eq.cong₂ _+_ ∣l₁∣≡∣l₁'∣ ∣l₂∣≡∣l₂'∣ ⟩
    length l₁' + length l₂'
  ≡⟨ Eq.cong (_ +_) ∣l₂'∣≡∣r'∣ ⟩
    length l₁' + length r'
  ≡⟨ length-++ l₁' ⟨ 
    length (l₁' ++ r')
  ∎

scan/divconq/clocked : 
  (A : tp⁺) → 
  cmp (Π (U (Π (A ×⁺ A) (λ _ → F A))) (λ _ → 
       Π A (λ _ → 
       Π nat λ k →
       Π (list A) (λ l → 
       Π (meta⁺ (⌈log₂ length l ⌉ Nat.≤ k)) λ _ → 
       F (Σ⁺ (list A ×⁺ A) λ (l' , _) → meta⁺ (length l ≡ length l'))))))
scan/divconq/clocked A f e zero []  p = ret (([] , e) , refl)
scan/divconq/clocked A f e zero (x ∷ []) p = ret ((e ∷ [] , x) , refl)
scan/divconq/clocked A f e (suc k) l  p = 
  bind (F _) (split A l) λ ((l₁ , l₂) , length₁ , length₂ , l↭l₁++l₂) → 
    bind (F _)
      (scan/divconq/clocked A f e k l₁ (h₁ l₁ length₁) ∥
       scan/divconq/clocked A f e k l₂ (h₂ l₂ length₂)) λ (((l₁' , b') , ∣l₁∣≡∣l₁'∣) , ((l₂' , c'), ∣l₂∣≡∣l₂'∣)) → 
      step (F _) (length l₂' , 1) ( -- cost of map
        bind (F _) (mapList {A} (λ x → f (b' , x)) l₂') λ (r' , ∣l₂'∣≡∣r'∣) → 
          bind (F _) (f (b' , c')) λ res → 
            step (F _) (length l₁' , 1) ( -- cost of append
              ret ((l₁' ++ r' , res) , 
              lem {A} l l₁ l₂ l₁' l₂' r' l↭l₁++l₂ ∣l₁∣≡∣l₁'∣ ∣l₂∣≡∣l₂'∣ ∣l₂'∣≡∣r'∣
              ))
              )
    where 
      h₁ : (l₁ : val (list A)) (length₁ : length l₁ ≡ ⌊ length l /2⌋) → ⌈log₂ length l₁ ⌉ Nat.≤ k
      h₁ l₁ length₁ =
        let open N.≤-Reasoning in
        (begin
          ⌈log₂ length l₁ ⌉
        ≡⟨ Eq.cong ⌈log₂_⌉ length₁ ⟩
          ⌈log₂ ⌊ length l /2⌋ ⌉
        ≤⟨ log₂-mono (N.⌊n/2⌋≤⌈n/2⌉ (length l)) ⟩
          ⌈log₂ ⌈ length l /2⌉ ⌉
        ≤⟨ log₂-suc (length l) p ⟩
          k
        ∎) 

      h₂ : (l₂ : val (list A)) (length₂ : length l₂ ≡ ⌈ length l /2⌉) → ⌈log₂ length l₂ ⌉ Nat.≤ k
      h₂ l₂ length₂ = 
        let open N.≤-Reasoning in
        (begin
          ⌈log₂ length l₂ ⌉
        ≡⟨ Eq.cong ⌈log₂_⌉ length₂ ⟩
          ⌈log₂ ⌈ length l /2⌉ ⌉
        ≤⟨ log₂-suc (length l) p ⟩
          k
        ∎)

scan/divconq : ◯-Monoid A → (cmp  (Π (list A)  (λ _ → F (list A ×⁺ A))))
scan/divconq {A} M L = 
    bind (F _) 
      (scan/divconq/clocked A (◯-Monoid.f M) (◯-Monoid.identity M) ⌈log₂ length L ⌉ L N.≤-refl) 
        (λ (L , p) → ret L)

scan/divconq/clocked/cost : 
  {A : tp⁺} →
  (f :  cmp (Π (A ×⁺ A) (λ _ → F A))) → 
  ((a b : val A) → IsBounded A (f (a , b)) (0 , 0)) → 
  (e : val A) → 
  (k : val nat) → 
  (l : val (list A)) →
  (h : val (meta⁺ (⌈log₂ length l ⌉ Nat.≤ k))) →  
  IsBounded (Σ⁺ (list A ×⁺ A) λ (l' , _) → meta⁺ (length l ≡ length l')) 
    (scan/divconq/clocked A f e k l h) 
    ((k + 1) * length l , 2 * k)
scan/divconq/clocked/cost f p e zero [] h = ≤⁻-refl
scan/divconq/clocked/cost f p e zero (x ∷ []) h = step⋆-mono-≤⁻ {c' = (1 , 0)} (z≤n , z≤n)
scan/divconq/clocked/cost {A} f p e (suc k) l h = 
  let open ≤⁻-Reasoning cost in 
    begin 
     (bind (F _) (split A l) (λ ((l₁ , l₂) , length₁ , length₂ , l↭l₁++l₂) → 
         bind (F _)
           (scan/divconq/clocked A f e k l₁ _ ∥
           scan/divconq/clocked A f e k l₂  _) λ (((l₁' , b') , ∣l₁∣≡∣l₁'∣) , ((l₂' , c'), ∣l₂∣≡∣l₂'∣)) → 
           step (F _) (length l₂' , 1) ( 
             bind (F _) (mapList {A} (λ x → f (b' , x)) l₂') λ (r' , ∣l₂'∣≡∣r'∣) → 
               bind (F _) (f (b' , c')) λ res → 
                 step (F _) (length l₁' , 1) ( 
                   ret _))))
  ≲⟨  (bind-monoʳ-≤⁻ (split A l) 
       λ ((l₁ , l₂) , length₁ , length₂ , l↭l₁++l₂) → 
         bind-monoʳ-≤⁻ ((scan/divconq/clocked A f e k l₁ _ ∥
           scan/divconq/clocked A f e k l₂ _)) 
             λ (((l₁' , b') , ∣l₁∣≡∣l₁'∣) , ((l₂' , c'), ∣l₂∣≡∣l₂'∣)) → 
                step-monoʳ-≤⁻ ((length l₂' , 1)) 
                 (bind-monoʳ-≤⁻ ((mapList {A} (λ x → f (b' , x)) l₂')) 
                   (λ (r' , ∣l₂'∣≡∣r'∣) → bind-monoˡ-≤⁻ (λ res → 
                step (F _) (length l₁' , 1) ( 
                 ret triv)) (p b' c')))) ⟩ 
    (bind (F _) (split A l) (λ ((l₁ , l₂) , length₁ , length₂ , l↭l₁++l₂) → 
         bind (F _)
           (scan/divconq/clocked A f e k l₁ _ ∥
           scan/divconq/clocked A f e k l₂  _) λ (((l₁' , b') , ∣l₁∣≡∣l₁'∣) , ((l₂' , c'), ∣l₂∣≡∣l₂'∣)) → 
           step (F _) (length l₂' , 1) ( 
             bind (F _) (mapList {A} (λ x → f (b' , x)) l₂') λ (r' , ∣l₂'∣≡∣r'∣) → 
                 step (F _) (length l₁' , 1) ( 
                   ret _))))
  ≲⟨ bind-monoʳ-≤⁻ (split A l) 
      (λ ((l₁ , l₂) , length₁ , length₂ , l↭l₁++l₂) → 
        bind-monoʳ-≤⁻ (scan/divconq/clocked A f e k l₁ _ ∥
           scan/divconq/clocked A f e k l₂ _) 
            λ (((l₁' , b') , ∣l₁∣≡∣l₁'∣) , ((l₂' , c'), ∣l₂∣≡∣l₂'∣)) → 
              step-monoʳ-≤⁻ ((length l₂' , 1)) 
                (bind-monoˡ-≤⁻ (λ x → step (F _) (length l₁' , 1) (ret _)) (mapList/bound l₂' f p b')))  ⟩ 
   bind (F _) (split A l) (λ ((l₁ , l₂) , length₁ , length₂ , l↭l₁++l₂) → 
    bind (F _) (scan/divconq/clocked A f e k l₁ _ ∥
           scan/divconq/clocked A f e k l₂  _) 
            λ (((l₁' , b') , ∣l₁∣≡∣l₁'∣) , ((l₂' , c'), ∣l₂∣≡∣l₂'∣)) → 
              step⋆ ((length l₂' + length l₁' , 2)))
  ≲⟨ bind-monoʳ-≤⁻ (split A l) (λ ((l₁ , l₂) , length₁ , length₂ , l↭l₁++l₂) → 
        bind-monoʳ-≤⁻ (scan/divconq/clocked A f e k l₁ _ ∥
           scan/divconq/clocked A f e k l₂  _) 
            λ (((l₁' , b') , ∣l₁∣≡∣l₁'∣) , ((l₂' , c'), ∣l₂∣≡∣l₂'∣)) → 
              step⋆-mono-≤⁻ {c = (length l₂' + length l₁' , 2)} 
                {c' = (length l₂ + length l₁ , 2)} 
                ( N.+-mono-≤ (N.≤-reflexive (Eq.sym  ∣l₂∣≡∣l₂'∣)) 
                  (N.≤-reflexive (Eq.sym ∣l₁∣≡∣l₁'∣)) , N.≤-refl)) ⟩
    bind (F _) (split A l) (λ ((l₁ , l₂) , length₁ , length₂ , l↭l₁++l₂) → 
    bind (F _) (scan/divconq/clocked A f e k l₁ _ ∥
           scan/divconq/clocked A f e k l₂  _) 
            λ (((l₁' , b') , ∣l₁∣≡∣l₁'∣) , ((l₂' , c'), ∣l₂∣≡∣l₂'∣)) → 
              step⋆ ((length l₂ + length l₁ , 2))) 
  ≲⟨ bind-monoʳ-≤⁻ (split A l) (λ ((l₁ , l₂) , length₁ , length₂ , l↭l₁++l₂) → 
      bind-monoˡ-≤⁻ (λ x → step⋆ ((length l₂ + length l₁ , 2))) 
        (bound/par {e₁ = scan/divconq/clocked A f e k l₁ _} 
          {e₂ = scan/divconq/clocked A f e k l₂  _} 
          {c₁ = ((k + 1) * (length l₁)  , 2 * k)} 
          {c₂ = ((k + 1) * (length l₂)  , 2 * k)} 
          (scan/divconq/clocked/cost {A} f p e k l₁ _) 
          (scan/divconq/clocked/cost {A} f p e k l₂ _)))  ⟩ 
      bind (F _) (split A l) (λ ((l₁ , l₂) , length₁ , length₂ , l↭l₁++l₂) → 
    bind (F _) (step⋆ ( (k + 1) * (length l₁) + (k + 1) * (length l₂) , 2 * k ⊔ 2 * k  ) ) 
            λ _ → 
              step⋆ ((length l₂ + length l₁ , 2)))
  ≡⟨⟩ 
   bind (F _) (split A l) (λ ((l₁ , l₂) , length₁ , length₂ , l↭l₁++l₂) → 
      step⋆ ( (k + 1) * (length l₁) + (k + 1) * (length l₂) + (length l₂ + length l₁) , (2 * k ⊔ 2 * k) + 2 ))
  ≡⟨ Eq.cong (bind (F _) (split A l)) (funext (λ ((l₁ , l₂) , length₁ , length₂ , l↭l₁++l₂) → 
      Eq.cong step⋆ 
        (Eq.cong₂ _,_ (Eq.sym 
        (N.+-assoc ((k + 1) * (length l₁) + (k + 1) * (length l₂)) (length l₂) (length l₁))) 
        (Eq.cong (_+ 2) (N.⊔-idem (2 * k)))))) 
      ⟩ 
     bind (F _) (split A l) (λ ((l₁ , l₂) , length₁ , length₂ , l↭l₁++l₂) → 
      step⋆ ( (k + 1) * (length l₁) + (k + 1) * (length l₂) + length l₂ + length l₁ , 2 * k + 2 ))
  ≲⟨ bind-monoʳ-≤⁻ (split A l) (λ ((l₁ , l₂) , length₁ , length₂ , l↭l₁++l₂) → 
    step⋆-mono-≤⁻ 
    {c = ( (k + 1) * (length l₁) + (k + 1) * (length l₂) + length l₂ + length l₁ , 2 * k + 2 )} 
      {c' = ( (k + 1) * (length l₁ + length l₂) + length l₂ + length l₁ , 2 * k + 2 )}
      ( N.+-monoˡ-≤ (length l₁) (N.+-monoˡ-≤ (length l₂) 
        (N.≤-reflexive (Eq.sym (N.*-distribˡ-+ (k + 1) (length l₁) (length l₂))))) 
          , N.≤-refl))  ⟩ 
    bind (F _) (split A l) (λ ((l₁ , l₂) , length₁ , length₂ , l↭l₁++l₂) → 
      step⋆ ( (k + 1) * (length l₁ + length l₂) + length l₂ + length l₁ , 2 * k + 2 ))
  ≲⟨ bind-monoʳ-≤⁻ (split A l) 
    (λ ((l₁ , l₂) , length₁ , length₂ , l↭l₁++l₂) → 
      step⋆-mono-≤⁻ {c = ( (k + 1) * (length l₁ + length l₂) + length l₂ + length l₁ , 2 * k + 2 )}
      {c' = ( (k + 1) * (length (l₁ ++ l₂)) + length l₂ + length l₁ , 2 * k + 2 )}
      ( N.+-monoˡ-≤ (length l₁) (N.+-monoˡ-≤ (length l₂) 
        (N.*-monoʳ-≤ (k + 1) (N.≤-reflexive (Eq.sym (length-++ l₁))))) , N.≤-refl))  ⟩ 
   bind (F _) (split A l) (λ ((l₁ , l₂) , length₁ , length₂ , l↭l₁++l₂) → 
    step⋆ ( (k + 1) * (length (l₁ ++ l₂)) + length l₂ + length l₁ , 2 * k + 2 ))
  ≲⟨ bind-monoʳ-≤⁻ (split A l) 
    (λ ((l₁ , l₂) , length₁ , length₂ , l↭l₁++l₂) → 
      step⋆-mono-≤⁻ 
        {c = ( (k + 1) * (length (l₁ ++ l₂)) + length l₂ + length l₁ , 2 * k + 2 )}
        {c' = ( (k + 1) * (length l) + length l₂ + length l₁ , 2 * k + 2 )} 
          (N.+-monoˡ-≤ (length l₁) (N.+-monoˡ-≤ (length l₂) 
            (N.*-monoʳ-≤ (k + 1) (N.≤-reflexive (↭-length (↭-sym l↭l₁++l₂))))) , N.≤-refl))  ⟩ 
    bind (F _) (split A l) (λ ((l₁ , l₂) , length₁ , length₂ , l↭l₁++l₂) → 
    step⋆ ( (k + 1) * (length l) + length l₂ + length l₁ , 2 * k + 2 )) 
  ≲⟨ bind-monoʳ-≤⁻ (split A l) 
    (λ ((l₁ , l₂) , length₁ , length₂ , l↭l₁++l₂) → 
      step⋆-mono-≤⁻ 
        (N.≤-reflexive (N.+-assoc ((k + 1) * (length l)) (length l₂) (length l₁)) 
          , N.≤-refl))  ⟩ 
  bind (F _) (split A l) (λ ((l₁ , l₂) , length₁ , length₂ , l↭l₁++l₂) → 
    step⋆ ( (k + 1) * (length l) + (length l₂ + length l₁) , 2 * k + 2 )) 
  ≲⟨ bind-monoʳ-≤⁻ (split A l) 
    (λ ((l₁ , l₂) , length₁ , length₂ , l↭l₁++l₂) → 
      step⋆-mono-≤⁻ (N.+-monoʳ-≤ ((k + 1) * (length l)) 
        (N.≤-reflexive (N.+-comm (length l₂) (length l₁)) ) , N.≤-refl))  ⟩ 
  bind (F _) (split A l) (λ ((l₁ , l₂) , length₁ , length₂ , l↭l₁++l₂) → 
    step⋆ ( (k + 1) * (length l) + (length l₁ + length l₂) , 2 * k + 2 )) 
  ≲⟨ bind-monoʳ-≤⁻ (split A l) 
      (λ ((l₁ , l₂) , length₁ , length₂ , l↭l₁++l₂) → 
        step⋆-mono-≤⁻ (N.+-monoʳ-≤ ((k + 1) * (length l)) 
          (N.≤-reflexive (Eq.sym (length-++ l₁))) , N.≤-refl))  ⟩ 
  bind (F _) (split A l) (λ ((l₁ , l₂) , length₁ , length₂ , l↭l₁++l₂) → 
    step⋆ ( (k + 1) * (length l) + (length (l₁ ++ l₂)) , 2 * k + 2 )) 
  ≲⟨ bind-monoʳ-≤⁻ (split A l) 
    (λ ((l₁ , l₂) , length₁ , length₂ , l↭l₁++l₂) → 
      step⋆-mono-≤⁻ (N.+-monoʳ-≤ ((k + 1) * (length l)) 
        (N.≤-reflexive (↭-length (↭-sym l↭l₁++l₂))) , N.≤-refl))  ⟩ 
  bind (F _) (split A l) (λ ((l₁ , l₂) , length₁ , length₂ , l↭l₁++l₂) → 
    step⋆ ( (k + 1) * (length l) + (length l) , 2 * k + 2 )) 
  ≲⟨ bind-monoˡ-≤⁻ (λ x → step⋆ ( (k + 1) * (length l) + (length l) , 2 * k + 2 )) (split/cost A l)  ⟩ 
    step⋆ ( (k + 1) * (length l) + (length l) , 2 * k + 2 ) 
  ≲⟨ step⋆-mono-≤⁻ (N.≤-reflexive (N.+-comm ((k + 1) * length l) (length l)) , N.≤-reflexive (arithmetic k)) ⟩ 
    step⋆ (length l + (k + 1) * length l , suc (k + suc (k + zero))) 
  ∎
  where 
    arithmetic : (k : val nat) → (k + (k + 0)) + 2 ≡ 1 + (k + (1 + (k + 0)))
    arithmetic k = 
      let open ≡-Reasoning in 
      begin 
        (k + (k + 0)) + 2 
      ≡⟨ N.+-comm (k + (k + 0)) 2 ⟩
        (1 + 1) + (k + (k + 0))
      ≡⟨ N.+-assoc 1 1 (k + (k + 0)) ⟩ 
        1 + (1 + (k + (k + 0)))
      ≡⟨ Eq.cong (1 +_) (N.+-assoc 1 k (k + 0)) ⟩
        1 + ((1 + k) + (k + 0))
      ≡⟨ Eq.cong (λ c → 1 + (c + (k + 0))) (N.+-comm 1 k) ⟩ 
        1 + ((k + 1) + (k + 0))
      ≡⟨ Eq.cong (1 +_) (N.+-assoc k 1 (k + 0)) ⟩ 
        1 + (k + (1 + (k + 0)))
      ∎





scan/divconq/cost : 
  (m : ◯-Monoid A) → 
  (l : val (list A)) →
  ((a b : val A) → IsBounded A ( (◯-Monoid.f) m (a , b)) (0 , 0)) → 
  IsBounded (list A ×⁺ A) (scan/divconq m l) ((⌈log₂ length l ⌉ + 1) * length l , 2 * ⌈log₂ length l ⌉)
scan/divconq/cost m l p = scan/divconq/clocked/cost (◯-Monoid.f m) p (◯-Monoid.identity m) ⌈log₂ length l ⌉ l N.≤-refl



-- scan/example : cmp (Π (list nat)  (λ _ → F (list nat ×⁺ nat)))
-- scan/example l = scan/bruteforce +-0-Monoid l 

-- scan/example' : cmp (Π (list nat)  (λ _ → F (list nat ×⁺ nat)))
-- scan/example' l = scan/divconq +-0-Monoid l 


-- ex = {! scan/example' (1 ∷ 2 ∷ 5 ∷ []) !} 



-- -- scan/divconq/correct : (M : ◯-Monoid A) → ◯ (scan/divconq M ≡ scan/bruteforce M)
-- -- scan/divconq/correct M = {!  !}


contract :  {A : tp⁺} → 
            cmp (Π (U (Π (A ×⁺ A) (λ _ → F A))) λ _ → 
                 Π (list A) (λ l → 
                 F (Σ⁺ (list A) λ l' → meta⁺ ( ⌈ length l /2⌉ ≡ length l' ) )))
                 -- should be ⌈ length l / 2 ⌉, but this doesnt work for some reason  
contract f [] = ret ([] , Eq.refl)
contract f (x ∷ []) = ret (x ∷ [] , refl) -- impossible to do the proofs without ceil 
contract f (x ∷ y ∷ l) = 
  bind (F _) (f (x , y)) (λ x₁ → 
    bind (F _) (contract f l) (λ (l' , p) → 
      ret (x₁ ∷ l' , Eq.cong suc p)) ) 

                 
-- contract should include a proof that this is half the length? 

contract/bound : {A : tp⁺} → 
                (l : val (list A)) → 
                (f :  cmp (Π (A ×⁺ A) (λ _ → F A))) → 
                ((a b : val A) → IsBounded A (f (a , b)) (0 , 0)) → 
                IsBounded  (Σ⁺ (list A) λ l' → meta⁺ (⌈ length l /2⌉ ≡ length l')) (contract f l) (0 , 0) 
contract/bound [] f p = ≤⁻-refl
contract/bound (x ∷ []) f p = ≤⁻-refl
contract/bound (x ∷ x₁ ∷ l) f p = 
  let open ≤⁻-Reasoning cost in 
    begin 
      bind (F _) (f (x , x₁)) (λ x₁ → 
    bind (F _) (contract f l) (λ (l' , p) → 
      ret triv) ) 
    ≲⟨ bind-monoʳ-≤⁻ (f (x , x₁)) (λ a → bind-monoˡ-≤⁻ (λ x₂ → ret triv) (contract/bound l f p)) ⟩ 
      bind (F _) (f (x , x₁)) (λ x₁ → ret triv) 
    ≲⟨ bind-monoˡ-≤⁻ (λ x₂ → ret triv) (p x x₁) ⟩ 
      step⋆ (0 , 0) 
    ∎ 

-- expand needs to take in a proof that length l₁ ≡ ⌈ length l₂ / 2 ⌉ 

expand : {A : tp⁺} → 
         cmp (Π (U (Π (A ×⁺ A) (λ _ → F A))) λ _ → 
              Π (list A) (λ l₁ → 
              Π (list A) (λ l₂ → 
              Π (meta⁺ ( length l₁ ≡ ⌈ length l₂ /2⌉ )) (λ p → 
              F (Σ⁺ (list A) λ l' → meta⁺ (  length l₂  ≡ length l' ) ))) )) -- not sure if this is the correct proof 
expand f [] [] p = ret ( [] , refl)
expand f (x ∷ []) (_ ∷ []) p = ret ( x ∷ [] , refl )
expand f (r ∷ l₁) (x ∷ x₁ ∷ l₂) p = 
  bind (F _) (f (r , x)) 
    (λ fst → bind (F _) (expand f l₁ l₂ (N.+-cancelˡ-≡ 1 (length l₁) ⌈ length l₂ /2⌉ p)) 
      λ (res , p') → ret ( r ∷ fst ∷ res , Eq.cong (2 +_) p' ))

expand/bound : {A : tp⁺} → 
                (l₁ l₂ : val (list A)) → 
                (f :  cmp (Π (A ×⁺ A) (λ _ → F A))) → 
                (p : val (meta⁺ ( length l₁ ≡ ⌈ length l₂ /2⌉ ))) → 
                ((a b : val A) → IsBounded A (f (a , b)) (0 , 0)) → 
                IsBounded  {!   !} (expand f l₁ l₂ p) (0 , 0) 
expand/bound [] [] f p h = ≤⁻-refl
expand/bound (x ∷ []) (x₁ ∷ []) f p h = ≤⁻-refl
expand/bound (r ∷ l₁) (x ∷ x₁ ∷ l₂) f p h = 
  let open ≤⁻-Reasoning cost in 
      begin 
        bind (F _) {! f (r , x)  !} 
    (λ fst → bind (F _) (expand f l₁ l₂ (N.+-cancelˡ-≡ 1 (length l₁) ⌈ length l₂ /2⌉ p)) 
      λ (res , p') → ret triv) 
      ≲⟨ bind-monoʳ-≤⁻ (f (r , x)) 
        (λ a → bind-monoˡ-≤⁻ (λ x₂ → ret triv) 
        (expand/bound l₁ l₂ f (N.+-cancelˡ-≡ 1 (length l₁) ⌈ length l₂ /2⌉ p) h)) ⟩ 
        bind (F _) (f (r , x)) (λ x₁ → ret triv)  
      ≲⟨ bind-monoˡ-≤⁻ (λ x₂ → ret triv) (h r x) ⟩ 
        step⋆ (0 , 0) 
      ∎

scan/contract/clocked :  {A : tp⁺} → 
                     cmp (Π (U (Π (A ×⁺ A) (λ _ → F A))) λ f → 
                          Π A (λ e → 
                          Π nat (λ k → 
                          Π (list A) (λ l → 
                          Π (meta⁺ (⌈log₂ length l ⌉ Nat.≤ k)) (λ p → 
                          F (Σ⁺ (list A ×⁺ A) λ (l' , _) → meta⁺ (length l ≡ length l')))))))
scan/contract/clocked f e zero [] p = ret ( ([] , e) , refl)
scan/contract/clocked f e zero (x ∷ []) p = bind (F _) (f (e , x)) (λ x₁ → ret ((e ∷ [] , x₁ ) , refl)) 
scan/contract/clocked f e (suc k) l p = 
  step (F _) (length l , 1) 
    (bind (F _) (contract f l) λ (cs , p₁) → 
      bind (F _) (scan/contract/clocked f e k cs (h cs (Eq.sym p₁))) λ ((rs , res), p₂) → 
      step (F _) (length l , 1) 
      (bind (F _) (expand f rs l (Eq.sym (Eq.trans p₁ p₂))) λ (es , p₃) → 
        ret ((es , res) , p₃)))
  where 
    h : (l₂ : val (list A)) (length₂ : length l₂ ≡ ⌈ length l /2⌉) → ⌈log₂ length l₂ ⌉ Nat.≤ k
    h l₂ length₂ = 
      let open N.≤-Reasoning in
        (begin
          ⌈log₂ length l₂ ⌉
        ≡⟨ Eq.cong ⌈log₂_⌉ length₂ ⟩
          ⌈log₂ ⌈ length l /2⌉ ⌉
        ≤⟨ log₂-suc (length l) p ⟩
          k
        ∎)

scan/contract : ◯-Monoid A → (cmp  (Π (list A)  (λ _ → F (list A ×⁺ A))))
scan/contract {A} M L = 
    bind (F _) 
      (scan/contract/clocked (◯-Monoid.f M) (◯-Monoid.identity M) ⌈log₂ length L ⌉ L N.≤-refl) 
        (λ (L , p) → ret L)

n≤2*⌈n/2⌉ : ∀ n → n Nat.≤ 2 * ⌈ n /2⌉ 
n≤2*⌈n/2⌉ n = 
  let open N.≤-Reasoning in 
    begin 
      n 
    ≡⟨ Eq.sym (N.⌊n/2⌋+⌈n/2⌉≡n n) ⟩ 
      ⌊ n /2⌋ + ⌈ n /2⌉ 
    ≤⟨ N.+-monoˡ-≤ ⌈ n /2⌉ (N.⌊n/2⌋≤⌈n/2⌉ n) ⟩ 
      ⌈ n /2⌉  + ⌈ n /2⌉ 
    ≡⟨ Eq.cong  (⌈ n /2⌉ +_) (Eq.sym (N.+-identityʳ ⌊ suc n /2⌋)) ⟩ 
      2 * ⌈ n /2⌉ 
    ∎ 
-- ⌊ suc n /2⌋ + ⌊ suc n /2⌋ ≡ ⌊ suc n /2⌋ + (⌊ suc n /2⌋ + 0)
scan/contract/clocked/cost : 
  {A : tp⁺} →
  (f :  cmp (Π (A ×⁺ A) (λ _ → F A))) → 
  ((a b : val A) → IsBounded A (f (a , b)) (0 , 0)) → 
  (e : val A) → 
  (k : val nat) → 
  (l : val (list A)) →
  (h : val (meta⁺ (⌈log₂ length l ⌉ Nat.≤ k))) →  
  IsBounded (Σ⁺ (list A ×⁺ A) λ (l' , _) → meta⁺ (length l ≡ length l')) 
    (scan/contract/clocked f e k l h) 
    (4 * length l , 2 * k)
-- idea behind proof: root-dominated
-- initially 2 * length l, recursive call is length l / 2
scan/contract/clocked/cost f p e zero [] h = ≤⁻-refl
scan/contract/clocked/cost f p e zero (x ∷ []) h = 
  let open ≤⁻-Reasoning cost in 
    begin 
      bind (F _) (f (e , x)) (λ x₁ → ret triv) 
    ≲⟨ bind-monoˡ-≤⁻ (λ x₁ → ret triv) (p e x) ⟩ 
      step⋆ (0 , 0) 
    ≲⟨ step⋆-mono-≤⁻ {c = (0 , 0)} {c' = (4 , 0)} (z≤n , z≤n) ⟩ 
      step⋆ (4 , 0)   
    ∎
scan/contract/clocked/cost f p e (suc k) l h = 
  let open ≤⁻-Reasoning cost in 
      begin 
        step (F _) (length l , 1) 
          (bind (F _) (contract f l) λ (cs , p₁) → 
            bind (F _) (scan/contract/clocked f e k cs _) λ ((rs , res), p₂) → 
            step (F _) (length l , 1) 
            (bind (F _) (expand f rs l (Eq.sym (Eq.trans p₁ p₂))) λ (es , p₃) → 
              ret triv)) 
      ≲⟨ step-monoʳ-≤⁻ ((length l , 1)) 
          (bind-monoʳ-≤⁻ (contract f l) (λ (cs , p₁) → 
            bind-monoʳ-≤⁻ (scan/contract/clocked f e k cs _) 
              λ ((rs , res), p₂) → step-monoʳ-≤⁻ ((length l , 1)) 
                (bind-monoˡ-≤⁻ (λ x → ret triv) (expand/bound rs l f (Eq.sym (Eq.trans p₁ p₂)) p)))) ⟩ 
        step (F _) (length l , 1) 
          (bind (F _) (contract f l) λ (cs , p₁) → 
            bind (F _) (scan/contract/clocked f e k cs _) λ ((rs , res), p₂) → 
            step⋆ (length l , 1)) 
      ≲⟨ step-monoʳ-≤⁻ (length l , 1) 
          (bind-monoʳ-≤⁻ (contract f l) 
            (λ (cs , p₁) → bind-monoˡ-≤⁻ (λ x → step⋆ (length l , 1)) 
              (scan/contract/clocked/cost f p e k cs _))) ⟩ 
        step (F _) (length l , 1) 
          (bind (F _) (contract f l) λ (cs , p₁) → 
            bind (F _) (step⋆ (4 * length cs , 2 * k)) λ _ → 
            step⋆ (length l , 1)) 
      ≡⟨⟩ 
        step (F _) (length l , 1) 
          (bind (F _) (contract f l) λ (cs , p₁) → 
            step⋆ ((4 * length cs) + length l , 2 * k + 1)) 
      -- we have p₂ which states that ⌈ length l /2⌉ ≡ length cs
      -- want to use p₂ to say that 4 * length cs <= 2 * length l 
      ≡⟨ Eq.cong (step (F _) (length l , 1)) 
          (Eq.cong (bind (F _) (contract f l)) 
            (funext (λ (cs , p₁) → Eq.cong step⋆ (Eq.cong₂ _,_ (Eq.cong (_ *_) p₁) refl)))) ⟩ 
        step (F _) (length l , 1) 
          (bind (F _) (contract f l) λ (cs , p₁) → 
            step⋆ ((4 * ⌈ length l /2⌉) + length l , 2 * k + 1)) 
      ≲⟨ {!   !} ⟩ 
        step (F _) (length l , 1) 
          (bind (F _) (contract f l) λ (cs , p₁) → 
            step⋆ ((2 * length l) + length l , 2 * k + 1)) 
      ≲⟨ {!   !} ⟩ 
        {!   !} 
      ≲⟨ {!   !} ⟩ 
        {!   !} 
      ≲⟨ {!   !} ⟩ 
        {!   !} 
      ∎ 

-- SML code for scan 
-- fun scan _ b [] = ([], b)
--     | scan f b [x] = ([b], f (b, x))
--     | scan f b s =
--         let
--           exception Mismatch
--           fun contract [] = []
--             | contract [x] = [x]
--             | contract (x::y::z) = f (x, y)::contract z
--           val (rs, result) = scan f b (contract s)
-- whats the work of expand? is it length of the final list, or how many times we compute f 
-- based on the book impl it should be final length, since its structured as a tabulate 
-- scan preserves length 
-- contract l gives l' where ceil (|l| / 2) = |l'| 
-- |rs| = ceil (|l| / 2)
-- work of expand = length of left list 
--           fun expand ([], []) = []
--             | expand ([r], [_]) = [r]
--             | expand (r::rs, x::_::xs) = r::f (r, x)::expand (rs, xs)
--             | expand _ = raise Mismatch
--         in (expand (rs, s), result)
--         end