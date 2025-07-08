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
split/clocked/cost A zero k' l h =  {!   !}
split/clocked/cost A (suc k) k' (x ∷ xs) h = bind-monoˡ-≤⁻ (λ x₁ → ret triv) (split/clocked/cost A k k' xs (N.suc-injective h))


split : (A : tp⁺) → cmp (Π (list A) λ l → F (split/type {A} ⌊ length l /2⌋ ⌈ length l /2⌉ l))
split A l = split/clocked {A} ⌊ length l /2⌋ ⌈ length l /2⌉ l (N.⌊n/2⌋+⌈n/2⌉≡n (length l))


split/cost : (l : val (list A)) → IsBounded (split/type {A} ⌊ length l /2⌋ ⌈ length l /2⌉ l) (split A l) (0 , 0)
split/cost = {!   !}
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

-- scan/divconq : ◯-Monoid A → (cmp  (Π (list A)  (λ _ → F (list A ×⁺ A))))
-- scan/divconq {A} M L = bind (F _) (scan/divconq/clocked A (◯-Monoid.f M) (◯-Monoid.identity M) ⌈log₂ length L ⌉ N.≤-refl) L (λ (L , p) → ret L)

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
                ( N.+-mono-≤ (N.≤-reflexive (Eq.sym  ∣l₂∣≡∣l₂'∣)) (N.≤-reflexive (Eq.sym ∣l₁∣≡∣l₁'∣)) , N.≤-refl)) ⟩
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
  ≲⟨ bind-monoʳ-≤⁻ (split A l) {!   !} ⟩ 
      -- bind-monoʳ-≤⁻ (split A l) (λ ((l₁ , l₂) , length₁ , length₂ , l↭l₁++l₂) → 
      -- step⋆-mono-≤⁻ 
      -- {c = ( (k + 1) * (length l₁) + (k + 1) * (length l₂) , 2 * k ⊔ 2 * k  )}
      -- {c' = ( (k + 1) * (length l₁) + (k + 1) * (length l₂) , 2 * k  )}
      -- (N.≤-refl , N.≤-reflexive (N.⊔-idem (2 * k))))
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
  ≲⟨ bind-monoˡ-≤⁻ (λ x → step⋆ ( (k + 1) * (length l) + (length l) , 2 * k + 2 )) (split/cost l)  ⟩ 
  step⋆ ( (k + 1) * (length l) + (length l) , 2 * k + 2 ) 
  ≲⟨ step⋆-mono-≤⁻ (N.≤-reflexive (N.+-comm ((k + 1) * (length l)) (length l)) , N.≤-reflexive (N.+-comm {! 2 * k  !} {!   !})) ⟩ 
    {!   !} 
  ∎




arithmetic : (k : val nat) → k ⊔ 1 Nat.≤ suc k 
arithmetic zero    = s≤s z≤n
arithmetic (suc k) = s≤s (N.≤-trans (N.≤-reflexive (N.⊔-identityʳ k)) (N.n≤1+n k))


-- scan/divconq/cost : 
--   (m : ◯-Monoid A) → 
--   (l : val (list A)) →
--   IsBounded (list A ×⁺ A) (scan/divconq m l) ((⌈log₂ length l ⌉ + 1) * length l , ⌈log₂ length l ⌉)



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
                 F (Σ⁺ (list A) λ l' → meta⁺ (  length l / 2 ≡ length l' ) ))) 
                 
-- contract should include a proof that this is half the length? 


-- scan/divconq/clocked : 
--   {A : tp⁺} → 
--   cmp (Π (U (Π (A ×⁺ A) (λ _ → F A))) (λ _ → 
--        Π A (λ _ → 
--        Π (list A) (λ l → 
--        Π nat λ k →
--        Π (meta⁺ (⌈log₂ length l ⌉ Nat.≤ k)) λ _ → 
--        F (Σ⁺ (list A ×⁺ A) λ (l' , _) → meta⁺ (length l ≡ length l'))))))


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
--           fun expand ([], []) = []
--             | expand ([r], [_]) = [r]
--             | expand (r::rs, x::_::xs) = r::f (r, x)::expand (rs, xs)
--             | expand _ = raise Mismatch
--         in (expand (rs, s), result)
--         end