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
open import Calf.Data.List using (list; []; _∷_; _∷ʳ_; [_]; length; _++_; reverse ; splitAt ; tabulate ; lookup ) renaming ( map to listmap )
open import Data.Fin.Base using (Fin; zero; suc; fromℕ)
open import Data.Fin.Properties as Fin
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
            step (F _) (length l₁' + length r' , 1) ( -- cost of append
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

postulate 
  SeqMap : 
    {A B : tp⁺} → 
    (f :  cmp (Π A (λ _ → F B))) → 
    (g : val A → val B) → 
    (∀ (x : val A) → f x ≡ step (F _) (1 , 1) (ret (g x))) → 
    (l : val (list A)) → 
    cmp (F (Σ⁺ (list B) λ l' → meta⁺ (l' ≡ listmap g l)))

  SeqMap/cost : 
    {A B : tp⁺} → 
    (f :  cmp (Π A (λ _ → F B))) → 
    (g : val A → val B) → 
    (p : ∀ (x : val A) → f x ≡ step (F _) (1 , 1) (ret (g x))) → 
    (l : val (list A)) → 
    IsBounded (Σ⁺ (list B) λ l' → meta⁺ (l' ≡ listmap g l)) 
      (SeqMap {A} {B} f g p l) 
      (length l , 1)

  SeqAppend : 
    {A : tp⁺} → 
    (l₁ l₂ : val (list A)) → 
    cmp (F (Σ⁺ (list A) λ l' → meta⁺ (l' ≡ l₁ ++ l₂)))
  
  SeqAppend/cost : 
    {A : tp⁺} → 
    (l₁ l₂ : val (list A)) → 
    IsBounded (Σ⁺ (list A) λ l' → meta⁺ (l' ≡ l₁ ++ l₂)) 
      (SeqAppend {A} l₁ l₂) 
      (length l₁ + length l₂ , 1)

  SeqTabulate : 
    {A : tp⁺} → 
    (n : val nat) → 
    (f : cmp (Π (meta⁺ (Fin n)) λ _ → F A)) →
    (w s : val nat) → 
    (g : val (meta⁺ (Fin n)) → val A) → 
    (∀ (n' : val (meta⁺ (Fin n))) → f n' ≡ step (F _) (w , s) (ret (g n'))) → 
    cmp (F (Σ⁺ (list A) λ l' → meta⁺ (l' ≡ tabulate {n = n} g)))
  
  SeqTabulate/cost :
    {A : tp⁺} → 
    (n : val nat) → 
    (f : cmp (Π (meta⁺ (Fin n)) λ _ → F A)) →
    (w s : val nat) →
    (g : val (meta⁺ (Fin n)) → val A) → 
    (p : ∀ (n' : val (meta⁺ (Fin n))) → f n' ≡ step (F _) (w , s) (ret (g n'))) → 
    IsBounded (Σ⁺ (list A) λ l' → meta⁺ (l' ≡ tabulate {n = n} g)) 
      (SeqTabulate {A} n f w s g p) 
      (w * n , s)
  
  SeqNth : 
    {A : tp⁺} → 
    (l : val (list A)) → 
    (n : val (meta⁺ (Fin (length l)))) → 
    cmp (F (Σ⁺ A λ a → meta⁺ (a ≡ lookup l n)))
  
  SeqNth/cost :
    {A : tp⁺} → 
    (l : val (list A)) → 
    (n : val (meta⁺ (Fin (length l)))) → 
    IsBounded (Σ⁺ A λ a → meta⁺ (a ≡ lookup l n)) 
      (SeqNth {A} l n) 
      (1 , 1)


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
    ((2 * k + 2) * length l , 2 * k)
scan/divconq/clocked/cost f p e zero [] h = ≤⁻-refl
scan/divconq/clocked/cost f p e zero (x ∷ []) h = step⋆-mono-≤⁻ {c' = (2 , 0)} (z≤n , z≤n)
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
                 step (F _) (length l₁' + length r' , 1) ( 
                   ret _))))
  ≲⟨  (bind-monoʳ-≤⁻ (split A l) 
       λ ((l₁ , l₂) , length₁ , length₂ , l↭l₁++l₂) → 
         bind-monoʳ-≤⁻ ((scan/divconq/clocked A f e k l₁ _ ∥
           scan/divconq/clocked A f e k l₂ _)) 
             λ (((l₁' , b') , ∣l₁∣≡∣l₁'∣) , ((l₂' , c'), ∣l₂∣≡∣l₂'∣)) → 
                step-monoʳ-≤⁻ ((length l₂' , 1)) 
                 (bind-monoʳ-≤⁻ ((mapList {A} (λ x → f (b' , x)) l₂')) 
                   (λ (r' , ∣l₂'∣≡∣r'∣) → bind-monoˡ-≤⁻ (λ res → 
                step (F _) (length l₁' + length r' , 1) ( 
                 ret triv)) (p b' c')))) ⟩ 
    (bind (F _) (split A l) (λ ((l₁ , l₂) , length₁ , length₂ , l↭l₁++l₂) → 
         bind (F _)
           (scan/divconq/clocked A f e k l₁ _ ∥
           scan/divconq/clocked A f e k l₂  _) λ (((l₁' , b') , ∣l₁∣≡∣l₁'∣) , ((l₂' , c'), ∣l₂∣≡∣l₂'∣)) → 
           step (F _) (length l₂' , 1) ( 
             bind (F _) (mapList {A} (λ x → f (b' , x)) l₂') λ (r' , ∣l₂'∣≡∣r'∣) → 
                 step (F _) (length l₁' + length r' , 1) ( 
                   ret _))))
  ≲⟨ bind-monoʳ-≤⁻ (split A l) (λ ((l₁ , l₂) , length₁ , length₂ , l↭l₁++l₂) → 
      bind-monoʳ-≤⁻ ((scan/divconq/clocked A f e k l₁ _ ∥ scan/divconq/clocked A f e k l₂  _)) 
      λ (((l₁' , b') , ∣l₁∣≡∣l₁'∣) , ((l₂' , c'), ∣l₂∣≡∣l₂'∣)) → 
      step-monoʳ-≤⁻ (length l₂' , 1) 
      (bind-monoʳ-≤⁻ (mapList {A} (λ x → f (b' , x)) l₂') (λ (r' , ∣l₂'∣≡∣r'∣) → 
      step-monoˡ-≤⁻ (ret _) 
      (N.≤-reflexive (Eq.cong (length l₁' +_) (Eq.sym (Eq.trans ∣l₂∣≡∣l₂'∣ ∣l₂'∣≡∣r'∣))) , N.≤-refl)))) ⟩ 
    (bind (F _) (split A l) (λ ((l₁ , l₂) , length₁ , length₂ , l↭l₁++l₂) → 
         bind (F _)
           (scan/divconq/clocked A f e k l₁ _ ∥
           scan/divconq/clocked A f e k l₂  _) λ (((l₁' , b') , ∣l₁∣≡∣l₁'∣) , ((l₂' , c'), ∣l₂∣≡∣l₂'∣)) → 
           step (F _) (length l₂' , 1) ( 
             bind (F _) (mapList {A} (λ x → f (b' , x)) l₂') λ (r' , ∣l₂'∣≡∣r'∣) → 
                 step (F _) (length l₁' + length l₂ , 1) ( 
                   ret _)))) 
  ≲⟨ bind-monoʳ-≤⁻ (split A l) 
      (λ ((l₁ , l₂) , length₁ , length₂ , l↭l₁++l₂) → 
        bind-monoʳ-≤⁻ (scan/divconq/clocked A f e k l₁ _ ∥
           scan/divconq/clocked A f e k l₂ _) 
            λ (((l₁' , b') , ∣l₁∣≡∣l₁'∣) , ((l₂' , c'), ∣l₂∣≡∣l₂'∣)) → 
              step-monoʳ-≤⁻ ((length l₂' , 1)) 
                (bind-monoˡ-≤⁻ (λ x → step (F _) (length l₁' + length l₂ , 1) (ret _)) (mapList/bound l₂' f p b')))  ⟩ 
   bind (F _) (split A l) (λ ((l₁ , l₂) , length₁ , length₂ , l↭l₁++l₂) → 
    bind (F _) (scan/divconq/clocked A f e k l₁ _ ∥
           scan/divconq/clocked A f e k l₂  _) 
            λ (((l₁' , b') , ∣l₁∣≡∣l₁'∣) , ((l₂' , c'), ∣l₂∣≡∣l₂'∣)) → 
              step⋆ ((length l₂' + (length l₁'  + length l₂) , 2)))
  ≲⟨ bind-monoʳ-≤⁻ (split A l) (λ ((l₁ , l₂) , length₁ , length₂ , l↭l₁++l₂) → 
        bind-monoʳ-≤⁻ (scan/divconq/clocked A f e k l₁ _ ∥
           scan/divconq/clocked A f e k l₂  _) 
            λ (((l₁' , b') , ∣l₁∣≡∣l₁'∣) , ((l₂' , c'), ∣l₂∣≡∣l₂'∣)) → 
              step⋆-mono-≤⁻ {c = (length l₂' + (length l₁' + length l₂) , 2)} 
                {c' = (length l₂ + (length l₁ + length l₂) , 2)} 
                ( N.≤-reflexive (Eq.cong₂ _+_ (Eq.sym ∣l₂∣≡∣l₂'∣) 
                (Eq.cong (_+ _) (Eq.sym ∣l₁∣≡∣l₁'∣))) , N.≤-refl)) ⟩
    bind (F _) (split A l) (λ ((l₁ , l₂) , length₁ , length₂ , l↭l₁++l₂) → 
    bind (F _) (scan/divconq/clocked A f e k l₁ _ ∥
           scan/divconq/clocked A f e k l₂  _) 
            λ (((l₁' , b') , ∣l₁∣≡∣l₁'∣) , ((l₂' , c'), ∣l₂∣≡∣l₂'∣)) → 
              step⋆ ((length l₂ + (length l₁ + length l₂), 2))) 
  ≲⟨ bind-monoʳ-≤⁻ (split A l) (λ ((l₁ , l₂) , length₁ , length₂ , l↭l₁++l₂) → 
      bind-monoˡ-≤⁻ (λ x → step⋆ ((length l₂ + (length l₁ + length l₂) , 2))) 
        (bound/par {e₁ = scan/divconq/clocked A f e k l₁ _} 
          {e₂ = scan/divconq/clocked A f e k l₂  _} 
          {c₁ = ((2 * k + 2) * (length l₁)  , 2 * k)} 
          {c₂ = ((2 * k + 2) * (length l₂)  , 2 * k)} 
          (scan/divconq/clocked/cost {A} f p e k l₁ _) 
          (scan/divconq/clocked/cost {A} f p e k l₂ _)))  ⟩ 
      bind (F _) (split A l) (λ ((l₁ , l₂) , length₁ , length₂ , l↭l₁++l₂) → 
    bind (F _) (step⋆ ( (2 * k + 2) * (length l₁) + (2 * k + 2) * (length l₂) , 2 * k ⊔ 2 * k  ) ) 
            λ _ → 
              step⋆ ((length l₂ + (length l₁ + length l₂) , 2)))
  ≡⟨⟩ 
   bind (F _) (split A l) (λ ((l₁ , l₂) , length₁ , length₂ , l↭l₁++l₂) → 
      step⋆ ( (2 * k + 2) * (length l₁) + (2 * k + 2) * (length l₂) + (length l₂ + (length l₁ + length l₂)) , (2 * k ⊔ 2 * k) + 2 ))
  ≡⟨ Eq.cong (bind (F _) (split A l)) (funext (λ ((l₁ , l₂) , length₁ , length₂ , l↭l₁++l₂) → 
      Eq.cong step⋆ 
        (Eq.cong₂ _,_ (Eq.sym 
        (N.+-assoc ((2 * k + 2) * (length l₁) + (2 * k + 2) * (length l₂)) (length l₂) (length l₁ + length l₂))) 
        (Eq.cong (_+ 2) (N.⊔-idem (2 * k)))))) 
      ⟩ 
     bind (F _) (split A l) (λ ((l₁ , l₂) , length₁ , length₂ , l↭l₁++l₂) → 
      step⋆ ( (2 * k + 2) * (length l₁) + (2 * k + 2) * (length l₂) + length l₂ + (length l₁ + length l₂) , 2 * k + 2 ))
  ≲⟨ bind-monoʳ-≤⁻ (split A l) (λ ((l₁ , l₂) , length₁ , length₂ , l↭l₁++l₂) → 
    step⋆-mono-≤⁻ 
    {c = ( (2 * k + 2) * (length l₁) + (2 * k + 2) * (length l₂) + length l₂ + (length l₁ + length l₂) , 2 * k + 2 )} 
      {c' = ( (2 * k + 2) * (length l₁ + length l₂) + length l₂ + (length l₁ + length l₂) , 2 * k + 2 )}
      (N.≤-reflexive (Eq.cong (λ c → c + length l₂ + (length l₁ + length l₂)) 
      (Eq.sym (N.*-distribˡ-+ (2 * k + 2) (length l₁) (length l₂)))) , N.≤-refl))  ⟩ 
    bind (F _) (split A l) (λ ((l₁ , l₂) , length₁ , length₂ , l↭l₁++l₂) → 
      step⋆ ( (2 * k + 2) * (length l₁ + length l₂) + length l₂ + (length l₁ + length l₂) , 2 * k + 2 ))
  ≲⟨ bind-monoʳ-≤⁻ (split A l) 
    (λ ((l₁ , l₂) , length₁ , length₂ , l↭l₁++l₂) → 
      step⋆-mono-≤⁻ {c = ( (2 * k + 2) * (length l₁ + length l₂) + length l₂ + (length l₁ + length l₂) , 2 * k + 2 )}
      {c' = ( (2 * k + 2) * (length (l₁ ++ l₂)) + length l₂ + length (l₁ ++ l₂) , 2 * k + 2 )}
      ( N.≤-reflexive (Eq.cong₂ (λ c₁ → λ c₂ → (2 * k + 2) * c₁ + length l₂ + c₂) 
      (Eq.sym (length-++ l₁)) (Eq.sym (length-++ l₁))) , N.≤-refl))  ⟩ 
   bind (F _) (split A l) (λ ((l₁ , l₂) , length₁ , length₂ , l↭l₁++l₂) → 
    step⋆ ( (2 * k + 2) * (length (l₁ ++ l₂)) + length l₂ + length (l₁ ++ l₂)  , 2 * k + 2 ))
  ≲⟨ bind-monoʳ-≤⁻ (split A l) (λ ((l₁ , l₂) , length₁ , length₂ , l↭l₁++l₂) → 
      step⋆-mono-≤⁻ (N.≤-reflexive (Eq.cong (λ c → (2 * k + 2) * (length (l₁ ++ l₂)) + c + length (l₁ ++ l₂)) 
      (Eq.sym (N.+-identityˡ (length l₂)))) , N.≤-refl)) ⟩ 
    bind (F _) (split A l) (λ ((l₁ , l₂) , length₁ , length₂ , l↭l₁++l₂) → 
    step⋆ ( (2 * k + 2) * (length (l₁ ++ l₂)) + (0 + length l₂) + length (l₁ ++ l₂)  , 2 * k + 2 )) 
  ≲⟨ bind-monoʳ-≤⁻ (split A l) (λ ((l₁ , l₂) , length₁ , length₂ , l↭l₁++l₂) → 
    step⋆-mono-≤⁻ {c = ((2 * k + 2) * (length (l₁ ++ l₂)) + (0 + length l₂) + length (l₁ ++ l₂) , 2 * k + 2)}
    {c' = ((2 * k + 2) * (length (l₁ ++ l₂)) + (length l₁ + length l₂) + length (l₁ ++ l₂) , 2 * k + 2)} 
    (N.+-monoˡ-≤ (length (l₁ ++ l₂)) (N.+-monoʳ-≤ ((2 * k + 2) * (length (l₁ ++ l₂))) (N.+-mono-≤ z≤n N.≤-refl))  , N.≤-refl)) ⟩ 
    bind (F _) (split A l) (λ ((l₁ , l₂) , length₁ , length₂ , l↭l₁++l₂) → 
    step⋆ ( (2 * k + 2) * (length (l₁ ++ l₂)) + (length l₁ + length l₂) + length (l₁ ++ l₂)  , 2 * k + 2 )) 
  ≲⟨ bind-monoʳ-≤⁻ (split A l) (λ ((l₁ , l₂) , length₁ , length₂ , l↭l₁++l₂) → 
      step⋆-mono-≤⁻ (N.≤-reflexive (Eq.cong (λ c → (2 * k + 2) * (length (l₁ ++ l₂)) + c + length (l₁ ++ l₂)) (Eq.sym (length-++ l₁))) , N.≤-refl)) ⟩ 
    bind (F _) (split A l) (λ ((l₁ , l₂) , length₁ , length₂ , l↭l₁++l₂) → 
    step⋆ ( (2 * k + 2) * (length (l₁ ++ l₂)) + length (l₁ ++ l₂) + length (l₁ ++ l₂)  , 2 * k + 2 )) 
  ≲⟨ bind-monoʳ-≤⁻ (split A l) 
    (λ ((l₁ , l₂) , length₁ , length₂ , l↭l₁++l₂) → 
      step⋆-mono-≤⁻ 
        {c = ( (2 * k + 2) * (length (l₁ ++ l₂)) + length (l₁ ++ l₂) + length (l₁ ++ l₂) , 2 * k + 2 )}
        {c' = ( (2 * k + 2) * (length l) + length (l₁ ++ l₂) + length (l₁ ++ l₂) , 2 * k + 2 )} 
          ( N.≤-reflexive (Eq.cong (λ c →  ((2 * k + 2) * c) + length (l₁ ++ l₂) + length (l₁ ++ l₂)) (↭-length (↭-sym l↭l₁++l₂)))  , N.≤-refl))  ⟩ 
            -- N.+-monoˡ-≤ (length l₁) (N.+-monoˡ-≤ (length l₂) 
            -- (N.*-monoʳ-≤ (k + 1) (N.≤-reflexive (↭-length (↭-sym l↭l₁++l₂)))))
    bind (F _) (split A l) (λ ((l₁ , l₂) , length₁ , length₂ , l↭l₁++l₂) → 
    step⋆ ( (2 * k + 2) * (length l) + length (l₁ ++ l₂) + length (l₁ ++ l₂) , 2 * k + 2 )) 
  ≲⟨ bind-monoʳ-≤⁻ (split A l) (λ ((l₁ , l₂) , length₁ , length₂ , l↭l₁++l₂) → 
      step⋆-mono-≤⁻ (N.≤-reflexive (Eq.cong₂ (λ c₁ → λ c₂ →  (2 * k + 2) * (length l) + c₁ + c₂) 
      ((↭-length (↭-sym l↭l₁++l₂))) ((↭-length (↭-sym l↭l₁++l₂)))) , N.≤-refl)) ⟩ 
    bind (F _) (split A l) (λ ((l₁ , l₂) , length₁ , length₂ , l↭l₁++l₂) → 
    step⋆ ( (2 * k + 2) * (length l) + length l + length l , 2 * k + 2 )) 
  ≲⟨ bind-monoʳ-≤⁻ (split A l) (λ ((l₁ , l₂) , length₁ , length₂ , l↭l₁++l₂) → 
      step⋆-mono-≤⁻ (N.≤-reflexive (Eq.cong ((λ c₁ →  (2 * k + 2) * (length l) + c₁ + length l)) 
      (Eq.sym (N.*-identityˡ (length l))) ) , N.≤-refl)) ⟩ 
    bind (F _) (split A l) (λ ((l₁ , l₂) , length₁ , length₂ , l↭l₁++l₂) → 
    step⋆ ( ((2 * k + 2) * (length l)) + (1 * length l) + length l , 2 * k + 2 )) 
  ≲⟨ bind-monoʳ-≤⁻ (split A l) (λ ((l₁ , l₂) , length₁ , length₂ , l↭l₁++l₂) → 
      step⋆-mono-≤⁻ 
       (N.≤-reflexive (Eq.cong (λ c → c + length l) 
        (Eq.sym (N.*-distribʳ-+ (length l) (2 * k + 2) 1))) , N.≤-refl)) ⟩ 
    bind (F _) (split A l) (λ ((l₁ , l₂) , length₁ , length₂ , l↭l₁++l₂) → 
    step⋆ ( ((2 * k + 2) + 1) * (length l) + length l , 2 * k + 2 )) 
  ≲⟨ bind-monoˡ-≤⁻ (λ x → 
    step⋆ ( ((2 * k + 2) + 1) * (length l) + length l , 2 * k + 2 )) 
    (split/cost A l) ⟩ 
    step⋆ ( ((2 * k + 2) + 1) * (length l) + length l , 2 * k + 2 ) 
  ≲⟨ step⋆-mono-≤⁻ (N.≤-reflexive (N.+-comm (((2 * k + 2) + 1) * (length l)) (length l)) , N.≤-refl) ⟩ 
    step⋆ ( length l +  ((2 * k + 2) + 1) * (length l) , 2 * k + 2 ) 
  ≲⟨ step⋆-mono-≤⁻ (N.≤-reflexive (Eq.cong (λ c → length l + (c + 1) * length l) (arithmetic k)) , N.≤-reflexive (arithmetic k)) ⟩ 
    step⋆ (length l + ((1 + (k + suc (k + zero))) + 1) * length l , suc (k + suc (k + zero))) 
  ≡⟨ Eq.cong (λ c → step⋆ (length l + c * length l , suc (k + suc (k + zero)))) 
    (N.+-comm (1 + (k + suc (k + zero))) 1) ⟩ 
    step⋆ (length l + (1 + (1 + (k + suc (k + zero)))) * length l , suc (k + suc (k + zero))) 
  ≡⟨ Eq.cong (λ c → step⋆ (length l + c * length l , suc (k + suc (k + zero))))
    (N.+-assoc 1 1 (k + suc (k + zero))) ⟩ 
    step⋆ (length l + (2 + (k + suc (k + zero))) * length l , suc (k + suc (k + zero))) 
  ≡⟨ Eq.cong (λ c → step⋆ (length l + c * length l , suc (k + suc (k + zero)))) 
    (N.+-comm 2 ((k + suc (k + zero)))) ⟩ 
    step⋆ (length l  + (k + (suc (k + 0)) + 2) * length l , suc (k + suc (k + zero))) 
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
  IsBounded (list A ×⁺ A) (scan/divconq m l) ((2 * ⌈log₂ length l ⌉ + 2) * length l , 2 * ⌈log₂ length l ⌉)
scan/divconq/cost m l p = scan/divconq/clocked/cost (◯-Monoid.f m) p (◯-Monoid.identity m) ⌈log₂ length l ⌉ l N.≤-refl



-- scan/example : cmp (Π (list nat)  (λ _ → F (list nat ×⁺ nat)))
-- scan/example l = scan/bruteforce +-0-Monoid l 

-- scan/example' : cmp (Π (list nat)  (λ _ → F (list nat ×⁺ nat)))
-- scan/example' l = scan/divconq +-0-Monoid l 


-- ex = {! scan/example' (1 ∷ 2 ∷ 5 ∷ []) !} 



-- -- scan/divconq/correct : (M : ◯-Monoid A) → ◯ (scan/divconq M ≡ scan/bruteforce M)
-- -- scan/divconq/correct M = {!  !}


  -- fun contract i =
  -- if i = n div 2 then nth S (2*i)
  -- else f (nth S (2*i), nth S (2*i + 1))

-- contract' : 
--   {A : tp⁺} → 
--   (l : val (list A)) → 
--   (i : Fin (⌈ (length l) /2⌉)) → 
--   (f : cmp (Π (A ×⁺ A) (λ _ → F A))) →
--   cmp (F A)
-- contract' {A} l i f with {! fromℕ ⌈ (length l) /2⌉  !}
-- ... | foo = {!   !} -- ≟

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

-- -- expand needs to take in a proof that length l₁ ≡ ⌈ length l₂ / 2 ⌉ 

expand : {A : tp⁺} → 
         cmp (Π (U (Π (A ×⁺ A) (λ _ → F A))) λ _ → 
              Π (list A) (λ l₂ → 
              Π (list A) (λ l₁ → 
              Π (meta⁺ ( length l₁ ≡ ⌈ length l₂ /2⌉ )) (λ p → 
              F (Σ⁺ (list A) λ l' → meta⁺ (  length l₂  ≡ length l' ) ))) )) -- not sure if this is the correct proof 
expand f [] [] p = ret ( [] , refl)
expand f (_ ∷ []) (x ∷ [])  p = ret ( x ∷ [] , refl )
expand f (x ∷ x₁ ∷ l₂) (r ∷ l₁) p = 
  bind (F _) (f (r , x)) 
    (λ fst → bind (F _) (expand f l₂ l₁ (N.+-cancelˡ-≡ 1 (length l₁) ⌈ length l₂ /2⌉ p)) 
      λ (res , p') → ret ( r ∷ fst ∷ res , Eq.cong (2 +_) p' ))

expand/bound : {A : tp⁺} → 
                (f :  cmp (Π (A ×⁺ A) (λ _ → F A))) → 
                (l₂ l₁ : val (list A)) → 
                (p : val (meta⁺ ( length l₁ ≡ ⌈ length l₂ /2⌉ ))) → 
                ((a b : val A) → IsBounded A (f (a , b)) (0 , 0)) → 
                IsBounded (Σ⁺ (list A) λ l' → meta⁺ (  length l₂  ≡ length l' )) (expand f l₂ l₁ p) (0 , 0) 
expand/bound f [] [] p h = ≤⁻-refl
expand/bound f (x₁ ∷ []) (x ∷ []) p h = ≤⁻-refl
expand/bound f (x ∷ x₁ ∷ l₂) (r ∷ l₁) p h = 
  let open ≤⁻-Reasoning cost in 
    begin
      bind (F _) (f (r , x)) 
      (λ fst → bind (F _) (expand f l₂ l₁ _) 
      λ x₂ → ret triv) 
    ≲⟨ bind-monoʳ-≤⁻ (f (r , x)) 
    (λ a → bind-monoˡ-≤⁻ (λ x₂ → ret triv) 
    (expand/bound f l₂ l₁ _ h)) ⟩ 
      bind (F _) (f (r , x)) (λ x₂ → ret triv)
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
-- note : I changed the bounds of the call to contract and expand to reflect that we'll rewrite them in terms of tabulates in the future. 
scan/contract/clocked {A} f e (suc k) l p = 
  step (F _) (2 * ⌈ length l /2⌉ , 2) -- since we need to do 2 lookups 
    (bind (F _) (contract f l) λ (cs , p₁) → 
      bind (F _) (scan/contract/clocked f e k cs (h cs (Eq.sym p₁))) λ ((rs , res), p₂) → 
      step (F _) (2 * length l , 2) -- since we need to do max of 2 lookups
      (bind (F _) (expand f l rs (Eq.sym (Eq.trans p₁ p₂))) λ (es , p₃) → 
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
-- -- ⌊ suc n /2⌋ + ⌊ suc n /2⌋ ≡ ⌊ suc n /2⌋ + (⌊ suc n /2⌋ + 0)
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
    (14 * length l , 4 * k)
-- idea behind proof: root-dominated
-- initially 2 * length l, recursive call is length l / 2
scan/contract/clocked/cost f p e zero [] h = ≤⁻-refl
scan/contract/clocked/cost f p e zero (x ∷ []) h = 
  let open ≤⁻-Reasoning cost in 
    begin 
      bind (F _) (f (e , x)) (λ x₁ → ret triv) 
    ≲⟨ bind-monoˡ-≤⁻ (λ x₁ → ret triv) (p e x) ⟩ 
      step⋆ (0 , 0) 
    ≲⟨ step⋆-mono-≤⁻ {c = (0 , 0)} {c' = (14 , 0)} (z≤n , z≤n) ⟩ 
      step⋆ (14 , 0)   
    ∎
scan/contract/clocked/cost f p e (suc k) l h = 
    let open ≤⁻-Reasoning cost in 
        begin
          step (F _) (2 * ⌈ length l /2⌉ , 2) 
          (bind (F _) (contract f l) λ (cs , p₁) → 
            bind (F _) (scan/contract/clocked f e k cs _) λ ((rs , res), p₂) → 
            step (F _) (2 * length l , 2) 
            (bind (F _) (expand f l rs _) λ (es , p₃) → 
              ret triv))
        ≲⟨ step-monoʳ-≤⁻ (2 * ⌈ length l /2⌉ , 2) 
          (bind-monoʳ-≤⁻ (contract f l) (λ (cs , p₁) → 
            bind-monoʳ-≤⁻ (scan/contract/clocked f e k cs _) 
              λ ((rs , res), p₂) → step-monoʳ-≤⁻ (2 * length l , 2) 
                (bind-monoˡ-≤⁻ (λ x → ret triv) (expand/bound f l rs _ p)))) ⟩
          step (F _) (2 * ⌈ length l /2⌉ , 2) 
          (bind (F _) (contract f l) λ (cs , p₁) → 
            bind (F _) (scan/contract/clocked f e k cs _) λ ((rs , res), p₂) → 
            step⋆ (2 * length l , 2)) 
        ≲⟨ step-monoʳ-≤⁻ (2 * ⌈ length l /2⌉ , 2) 
          (bind-monoʳ-≤⁻ (contract f l) 
            (λ (cs , p₁) → bind-monoˡ-≤⁻ (λ x → step⋆ (2 * length l , 2)) 
              (scan/contract/clocked/cost f p e k cs _))) ⟩
          step (F _) (2 * ⌈ length l /2⌉ , 2) 
          (bind (F _) (contract f l) λ (cs , p₁) → 
            bind (F _) (step⋆ (14 * length cs , 4 * k)) λ _ → 
            step⋆ (2 * length l , 2))
        ≡⟨⟩ 
          step (F _) (2 * ⌈ length l /2⌉ , 2) 
          (bind (F _) (contract f l) λ (cs , p₁) → 
            step⋆ ((14 * length cs) + (2 * length l) , 4 * k + 2)) 
        ≲⟨ step-monoʳ-≤⁻ (2 * ⌈ length l /2⌉ , 2) 
            (bind-monoʳ-≤⁻ (contract f l) (λ (cs , p₁) → 
              step⋆-mono-≤⁻ (N.≤-reflexive (Eq.cong (λ c → (14 * c) + (2 * length l)) (Eq.sym p₁)) , N.≤-refl))) ⟩
          step (F _) (2 * ⌈ length l /2⌉ , 2) 
          (bind (F _) (contract f l) λ (cs , p₁) → 
            step⋆ ((14 * ⌈ length l /2⌉) + (2 * length l) , 4 * k + 2))
        ≲⟨ step-monoʳ-≤⁻ (2 * ⌈ length l /2⌉ , 2) 
            (bind-monoˡ-≤⁻ (λ x → 
              step⋆ ((14 * ⌈ length l /2⌉) + (2 * length l) , 4 * k + 2)) 
              (contract/bound l f p)) ⟩
          step⋆ (2 * ⌈ length l /2⌉ + ((14 * ⌈ length l /2⌉) + (2 * length l)) , 2 + (4 * k + 2))
        ≲⟨ step⋆-mono-≤⁻ (N.≤-reflexive (Eq.sym 
        (N.+-assoc (2 * ⌈ length l /2⌉) (14 * ⌈ length l /2⌉) (2 * length l))) , 
        N.≤-reflexive (N.+-comm 2 (4 * k + 2))) ⟩
          step⋆ ((2 * ⌈ length l /2⌉ + (14 * ⌈ length l /2⌉)) + (2 * length l) , (4 * k + 2) + 2)
        ≲⟨ step⋆-mono-≤⁻ (N.≤-reflexive (Eq.cong (λ c → c + (2 * length l)) (Eq.sym (N.*-distribʳ-+ ⌈ length l /2⌉ 2 14))) , N.≤-reflexive (N.+-assoc (4 * k) 2 2)) ⟩
          step⋆ ((16 * ⌈ length l /2⌉) + (2 * length l) , (4 * k + 4))
        ≡⟨⟩
          step⋆ (((8 * 2) * ⌈ length l /2⌉) + (2 * length l) , (4 * k + 4))
        ≡⟨ Eq.cong (λ c → step⋆ (c + (2 * length l) , (4 * k + 4))) (N.*-assoc 8 2 ⌈ length l /2⌉) ⟩
          step⋆ ((8 * (2 * ⌈ length l /2⌉)) + (2 * length l) , (4 * k + 4))
        ≲⟨ step⋆-mono-≤⁻ (N.+-monoˡ-≤ ((2 * length l)) 
            (N.*-monoʳ-≤ 8 (2*⌈n/2⌉≤1+n (length l))) , N.≤-refl) ⟩
          step⋆ ((8 * (1 + length l)) + (2 * length l) , 4 * k + 4)
        ≡⟨ Eq.cong (λ c → step⋆ (c + (2 * length l) , 4 * k + 4)) 
            (N.*-distribˡ-+ 8 1 (length l)) ⟩
          step⋆ ((8 + 8 * length l) + (2 * length l) , 4 * k + 4)
        ≡⟨ Eq.cong (λ c → step⋆ (c , (4 * k + 4))) (N.+-assoc 8 (8 * length l) (2 * length l)) ⟩
          step⋆ (8 + (8 * length l + 2 * length l) , 4 * k + 4)
        ≡⟨ Eq.cong (λ c → step⋆ (8 + c , 4 * k + 4)) (Eq.sym (N.*-distribʳ-+ (length l) 8 2)) ⟩
          step⋆ (8 + (10 * length l) , 4 * k + 4)
        ≡⟨⟩
          step⋆ ((4 * 2) + (10 * length l) , 4 * k + 4)
        ≲⟨ step⋆-mono-≤⁻ (N.+-monoˡ-≤ (10 * length l) (N.*-monoʳ-≤ 4 minlength) , N.≤-refl) ⟩
          step⋆ ((4 * length l) + (10 * length l) , 4 * k + 4)
        ≡⟨ Eq.cong₂ (λ c₁ → λ c₂ → step⋆ (c₁ , c₂)) 
          (Eq.sym (N.*-distribʳ-+ (length l) 4 10)) 
          (Eq.sym (N.*-distribˡ-+ 4 k 1)) ⟩
          step⋆ (14 * length l , 4 * (k + 1))
        ≡⟨ Eq.cong (λ c₂ → step⋆ (length l + 13 * length l , 4 * c₂)) (N.+-comm k 1) ⟩
          step⋆ (length l + 13 * length l , 4 * (1 + k))
        ≡⟨⟩
          step⋆ (length l + 13 * length l , 1 + k + 3 * (1 + k))
        ≡⟨⟩
          step⋆ (length l + 13 * length l , 1 + (k + 3 * (1 + k)))
        ∎
      where 
        ⌈n/2⌉≤1+⌊n/2⌋ : (n : val nat) → ⌈ n /2⌉ Nat.≤ 1 + ⌊ n /2⌋
        ⌈n/2⌉≤1+⌊n/2⌋ zero = z≤n
        ⌈n/2⌉≤1+⌊n/2⌋ (suc n) = s≤s (N.⌊n/2⌋-mono (N.n≤1+n n))

        2*⌈n/2⌉≤1+n : (n : val nat) → 2 * ⌈ n /2⌉ Nat.≤ 1 + n
        2*⌈n/2⌉≤1+n n = 
          let open N.≤-Reasoning in 
            begin 
              ⌈ n /2⌉ + (⌈ n /2⌉ +  0)
            ≤⟨ N.+-monoˡ-≤ ((⌈ n /2⌉ +  0)) (⌈n/2⌉≤1+⌊n/2⌋ n) ⟩ 
              1 + ⌊ n /2⌋ + (⌈ n /2⌉ + 0) 
            ≡⟨ Eq.cong (λ c → 1 + ⌊ n /2⌋ + c) (N.+-identityʳ ⌈ n /2⌉) ⟩ 
              1 + ⌊ n /2⌋ + ⌈ n /2⌉ 
            ≡⟨ Eq.cong (λ c → 1 + c) (N.⌊n/2⌋+⌈n/2⌉≡n n) ⟩ 
              1 + n 
            ∎ 
        
        minlength : 2 Nat.≤ length l 
        minlength = {!   !}

-- we have (h : val (meta⁺ (⌈log₂ length l ⌉ Nat.≤ k)))
-- we'll have a bunch of 1s 
-- WTS 1 ≤ length l
-- -- SML code for scan 
-- -- fun scan _ b [] = ([], b)
-- --     | scan f b [x] = ([b], f (b, x))
-- --     | scan f b s =
-- --         let
-- --           exception Mismatch
-- --           fun contract [] = []
-- --             | contract [x] = [x]
-- --             | contract (x::y::z) = f (x, y)::contract z
-- --           val (rs, result) = scan f b (contract s)
-- -- whats the work of expand? is it length of the final list, or how many times we compute f 
-- -- based on the book impl it should be final length, since its structured as a tabulate 
-- -- scan preserves length 
-- -- contract l gives l' where ceil (|l| / 2) = |l'| 
-- -- |rs| = ceil (|l| / 2)
-- -- work of expand = length of left list 
-- --           fun expand ([], []) = []
-- --             | expand ([r], [_]) = [r]
-- --             | expand (r::rs, x::_::xs) = r::f (r, x)::expand (rs, xs)
-- --             | expand _ = raise Mismatch
-- --         in (expand (rs, s), result)
-- --         end