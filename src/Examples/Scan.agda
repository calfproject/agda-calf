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
-- open import Calf.Data.BigO costMonoid
open import Calf.Data.Product 

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; _≢_; module ≡-Reasoning)
open import Data.Nat as Nat using (_+_; _⊔_)
open import Data.Nat.Properties as N using ()
open import Data.List.Relation.Binary.Permutation.Propositional



open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; module ≡-Reasoning)
open import Data.Sum using (inj₁; inj₂)
open import Function
import Data.Nat.Properties as N
open import Data.Nat.Square
open import Data.Nat.Log2
import Data.Nat.Properties as N


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
  bind (F _) (f (e , x)) (λ y → 
    bind (F _) (scan/bruteforce/help f y L) λ { (ys , r) →  
      ret ( y ∷ ys , r )}) 

scan/bruteforce : {A : tp⁺} → ◯-Monoid A → cmp (Π (list A)  (λ _ → F (list A ×⁺ A)))
scan/bruteforce M L = scan/bruteforce/help (◯-Monoid.f M) (◯-Monoid.identity M) L

+-0-Monoid : ◯-Monoid nat 
+-0-Monoid .◯-Monoid.f (m , n) = step (F _) (1 , 1) (ret (m + n))
+-0-Monoid .◯-Monoid.identity = {!   !}
+-0-Monoid .◯-Monoid.isMonoid = {!   !} 





scan/accum-independent :  (w : ℕ) (s : ℕ) → 
                          (l : val (list A)) → 
                          (f :  cmp (Π (A ×⁺ A) (λ _ → F A))) → 
                          (a : val A) → 
                          ((a b : val A) → IsBounded A (f (a , b)) (w , s)) → 
                          IsBounded (list A ×⁺ A) (scan/bruteforce/help f a l) (length l * w , length l * s)
scan/accum-independent w s [] f a h = ≤⁻-refl
scan/accum-independent w s (x ∷ l) f a h = 
  let open ≤⁻-Reasoning cost in 
  begin 
    bind (F _) (f (a , x)) (λ res →
      bind (F _) (scan/bruteforce/help f res l) (λ _ → 
        ret triv))
  ≲⟨ bind-monoʳ-≤⁻ (f (a , x)) (λ res → scan/accum-independent w s l f res h) ⟩
    bind (F _) (f (a , x)) (λ res →
      step⋆ (length l * w , length l * s))
  ≲⟨ bind-monoˡ-≤⁻ ((λ res →
      step⋆ (length l * w , length l * s))) (h a x) ⟩
    bind (F _) (step⋆ (w , s)) ((λ res →
      step⋆ (length l * w , length l * s)))
  ≡⟨⟩
    step⋆ (w + length l * w , s + length l * s)  
  ∎

-- scan/bruteforce/cost :  
--       (m : ◯-Monoid A) → 
--       (c : ℂ) →
--       ((a b : val A) → IsBounded A (◯-Monoid.f m (a , b)) c) → 
--       (l : val (list A)) →
--       IsBounded (list A ×⁺ A) (scan/bruteforce m l) (length l * ? , ?)
-- scan/bruteforce/cost m c h []      = ≤⁻-refl
-- scan/bruteforce/cost m (w , s) h (x ∷ l) = 
--   let open ≤⁻-Reasoning cost in
--   begin
--    bind (F _) (◯-Monoid.f m (◯-Monoid.identity m , x)) (λ res →
--     bind (F _) (scan/bruteforce/help (◯-Monoid.f m) res l) (λ _ → 
--       ret triv))
--   ≲⟨ bind-monoʳ-≤⁻ (◯-Monoid.f m ( ◯-Monoid.identity m , x)) (λ res → scan/accum-independent c l (◯-Monoid.f m) res h) ⟩
--    bind (F _) (◯-Monoid.f m (◯-Monoid.identity m , x)) (λ _ →
--        bind (F _) (step⋆ (length l * )) (λ _ → 
--          ret triv))
--   ≲⟨ bind-monoˡ-≤⁻ 
--     ((λ _ →
--        bind (F _) (step⋆ (length l * c)) (
--         λ _ → 
--          ret triv))) (h (◯-Monoid.identity m) x) ⟩
--     bind (F _) (step⋆ c) (λ _ →
--        bind (F _) (step⋆ (length l * c)) (λ _ → 
--          ret triv))
--   ≡⟨⟩
--     step⋆ (c + length l * c)  
--   ∎

-- -- reimplemented split from Split.agda in mergesort example

-- pair : {A : tp⁺} → tp⁺
-- pair {A} = list A ×⁺ list A

-- split/type : {A : tp⁺} → val nat → val nat → val (list A) → tp⁺
-- split/type {A} k k' l = Σ⁺ (pair {A}) λ (l₁ , l₂) → meta⁺ (length l₁ ≡ k × length l₂ ≡ k' × l ↭ (l₁ ++ l₂))

-- split/clocked : {A : tp⁺} → cmp (Π nat λ k → Π nat λ k' → Π (list A) λ l → Π (meta⁺ (k + k' ≡ length l)) λ _ → F (split/type {A} k k' l))
-- split/clocked zero    k' l        refl = ret (([] , l) , refl , refl , refl)
-- split/clocked {A} (suc k) k' (x ∷ xs) h    =
--   bind (F (split/type {A} (suc k) k' (x ∷ xs))) (split/clocked {A} k k' xs (N.suc-injective h)) λ ((l₁ , l₂) , h₁ , h₂ , xs↭l₁++l₂) →
--   ret ((x ∷ l₁ , l₂) , Eq.cong suc h₁ , h₂ , prep x xs↭l₁++l₂)


-- split : {A : tp⁺} → cmp (Π (list A) λ l → F (split/type {A} ⌊ length l /2⌋ ⌈ length l /2⌉ l))
-- split {A} l = split/clocked {A} ⌊ length l /2⌋ ⌈ length l /2⌉ l (N.⌊n/2⌋+⌈n/2⌉≡n (length l))


-- mapList : {A B : tp⁺} → cmp (Π (U (Π A λ _ → F B)) (λ _ → Π (list A) (λ _ → F (list B))))
-- mapList f [] = ret []
-- mapList {A} {B} f (x ∷ l) = 
--   bind (F _) (mapList {A} {B} f l) λ l' → 
--     bind (F _) (f x) λ x' → 
--       ret (x' ∷ l')

-- mapList/bound : {A : tp⁺} → 
--                 (c : ℂ) → 
--                 (l : val (list A)) → 
--                 (f :  cmp (Π (A ×⁺ A) (λ _ → F A))) → 
--                 ((a b : val A) → IsBounded A (f (a , b)) c) → 
--                 (a : val A) → 
--                 IsBounded  (list A) (mapList {A} (λ x → f (a , x)) l) (length l * c) 
-- mapList/bound c [] f h a = ≤⁻-refl
-- mapList/bound {A} c (x ∷ l) f h a = let open ≤⁻-Reasoning cost in
--   begin
--     bind (F _) ((mapList {A} (λ x₁ → f (a , x₁)) l)) ((λ a₁ → bind (F _) (f (a , x)) (λ a₂ → ret triv)))
--   ≲⟨ bind-monoˡ-≤⁻ (((λ a₁ → bind (F (meta⁺ Unit)) (f (a , x)) (λ a₂ → ret triv)))) (mapList/bound c l f h a) ⟩ 
--     bind (F _) (step⋆ (length l * c)) (((λ a₁ → bind (F _) (f (a , x)) (λ a₂ → ret triv)))) 
--   ≲⟨ bind-monoʳ-≤⁻ ((step⋆ (length l * c))) (λ a₁ → h a x) ⟩ 
--     bind (F _) (step⋆ (length l * c)) (((λ a₁ → bind (F _) (step⋆ c) (λ a₂ → ret triv)))) 
--   ≡⟨⟩ 
--     step⋆ (length l * c + c) 
--   ≡⟨ Eq.cong step⋆ (N.+-comm (length l * c) c)  ⟩ 
--     step⋆ (c + length l * c) 
--   ∎

-- -- bind (F (meta⁺ Unit)) (mapList (λ x₁ → f (a , x₁)) l)
-- -- (λ a₁ → bind (F (meta⁺ Unit)) (f (a , x)) (λ a₂ → ret triv))
-- -- ≤⁺
-- -- Calf.Step.step ℕ-CostMonoid (F (meta⁺ Unit))
-- -- (c + Calf.Data.List.foldr (λ _ → suc) 0 l * c) (ret triv)

-- appendList : {A : tp⁺} → cmp (Π (list A) (λ _ → Π (list A) λ _ → F (list A)))
-- appendList [] l = ret l
-- appendList {A} (x ∷ xs) l = 
--   step (F _) 1 (
--   bind (F _) (appendList {A} xs l) λ l' → 
--     ret (x ∷ l'))

-- appendList/bound  : {A : tp⁺} → 
--                     (c : ℂ) → 
--                     (l₁ l₂ : val (list A)) → 
--                     IsBounded (list A) (appendList {A} l₁ l₂) (length l₁) 
-- appendList/bound c [] l₂ = ≤⁻-refl
-- appendList/bound {A} c (x ∷ l₁) l₂ = let open ≤⁻-Reasoning cost in
--   begin 
--     step (F _) 1 (
--       bind (F _) (appendList {A} l₁ l₂) λ l' → 
--         ret triv ) 
--   ≲⟨ step-monoʳ-≤⁻ 1 (appendList/bound {A} c l₁ l₂) ⟩
--     step (F _) 1 (
--       bind (F _) (step⋆ (length l₁) ) λ _ → 
--         ret triv )
--   ≡⟨⟩
--     step⋆ (1 + length l₁)
--   ∎

-- scan/divconq/clocked : 
--   {A : tp⁺} → 
--   cmp (Π (U (Π (A ×⁺ A) (λ _ → F A))) (λ _ → 
--        Π A (λ _ → 
--        Π (list A) (λ l → 
--        Π nat λ k →
--        Π (meta⁺ (⌈log₂ length l ⌉ Nat.≤ k)) λ _ → 
--         F (list A ×⁺ A)))))
-- scan/divconq/clocked f e l Nat.zero p = ret (l , e)
-- scan/divconq/clocked f e [] (suc Nat.zero) p = ret ([] , e)
-- scan/divconq/clocked f e (x ∷ l) (suc Nat.zero) p = ret (e ∷ [] , x)
-- scan/divconq/clocked {A} f e l (2+ k) p = 
--   bind (F _) (split {A} l) λ ((l₁ , l₂) , length₁ , length₂ , l↭l₁++l₂) → 
--   let
--     h₁ , h₂ =
--       let open N.≤-Reasoning in
--       (begin
--         ⌈log₂ length l₁ ⌉
--       ≡⟨ Eq.cong ⌈log₂_⌉ length₁ ⟩
--         ⌈log₂ ⌊ length l /2⌋ ⌉
--       ≤⟨ log₂-mono (N.⌊n/2⌋≤⌈n/2⌉ (length l)) ⟩
--         ⌈log₂ ⌈ length l /2⌉ ⌉
--       ≤⟨ log₂-suc (length l) p ⟩
--         suc k
--       ∎) ,
--       (begin
--         ⌈log₂ length l₂ ⌉
--       ≡⟨ Eq.cong ⌈log₂_⌉ length₂ ⟩
--         ⌈log₂ ⌈ length l /2⌉ ⌉
--       ≤⟨ log₂-suc (length l) p ⟩
--         suc k
--       ∎)
--   in
--   bind (F _) (scan/divconq/clocked f e l₁ (suc k) h₁ ∥ scan/divconq/clocked f e l₂ (suc k) h₂ ) λ ((l₁' , b') , (l₂' , c')) → ?
--   bind (F _) (scan/divconq/clocked f e l₁ (suc k) h₁) λ (l₁' , b') → 
--   bind (F _) (scan/divconq/clocked f e l₂ (suc k) h₂) λ (l₂' , c') → 
--   bind (F _) (mapList {A} (λ x → f (b' , x)) l₂') λ r' → 
--   bind (F _) (appendList {A} l₁' r') λ resL →
--   bind (F _) (f (b' , c')) λ res → 
--   ret (resL , res)

-- -- scan/divconq/clocked/cost : 
--                           -- (f :  cmp (Π (A ×⁺ A) (λ _ → F A))) → 
--                           -- (c : ℂ) →
--                           -- ((a b : val A) → IsBounded A (f (a , b)) c) → 
--                           -- (l : val (list A)) →
--                           -- (h : meta⁺ (⌈log₂ length l ⌉ Nat.≤ ?)) → 
--                           -- (n : nat) → 
--                           -- IsBounded (list A ×⁺ A) (scan/divconq m l) (length l * c)


-- scan/divconq : ◯-Monoid A → (cmp  (Π (list A)  (λ _ → F (list A ×⁺ A))))
-- scan/divconq M L = scan/divconq/clocked (◯-Monoid.f M) (◯-Monoid.identity M) L ⌈log₂ length L ⌉ N.≤-refl 


-- scan/example : cmp (Π (list nat)  (λ _ → F (list nat ×⁺ nat)))
-- scan/example l = scan/bruteforce +-0-Monoid l 

-- ex = {! scan/example (0 ∷ 1 ∷ 2 ∷ [])  !} 

-- -- scan/divconq/cost : 
-- --       (m : ◯-Monoid A) → 
-- --       (c : ℂ) →
-- --       ((a b : val A) → IsBounded A (◯-Monoid.f m (a , b)) c) → 
-- --       (l : val (list A)) →
-- --       IsBounded (list A ×⁺ A) (scan/divconq m l) (length l * c)
-- -- scan/divconq/cost m c h [] = ≤⁺-refl
-- -- -- this should definitely go by induction on log2 length L
-- -- scan/divconq/cost m c h (x ∷ l) =
-- --   let open ≤⁻-Reasoning cost in 
-- --   begin
-- --     bind (F (meta⁺ Unit))
-- --       (scan/divconq/clocked (◯-Monoid.f m) (◯-Monoid.identity m) (x ∷ l)
-- --         ⌈log₂ length (x ∷ l) ⌉ N.≤-refl) (λ _ → ret triv)
-- --   ≲⟨ {!  !} ⟩
-- --     {!   !} 
-- --   ≲⟨ {!   !} ⟩
-- --     {!   !} 
-- --   ∎
-- -- bind (F (meta⁺ Unit))
-- -- (scan/divconq/clocked (◯-Monoid.f m) (◯-Monoid.identity m) (x ∷ l)
-- --  (Data.Nat.Logarithm.Core.⌈log2⌉
-- --   (suc (Calf.Data.List.foldr (λ _ → suc) 0 l))
-- --   (Induction.WellFounded.Acc.acc
-- --    (λ y<x →
-- --       Induction.WellFounded.Subrelation.accessible N.<⇒<′
-- --       (Data.Nat.Induction.<′-wellFounded′
-- --        (suc (Calf.Data.List.foldr (λ _ → suc) 0 l)) (N.<⇒<′ y<x)))))
-- --  (N.≤-reflexive refl))
-- -- (λ _ → ret triv)
-- -- ≤⁺
-- -- Calf.Step.step ℕ-CostMonoid (F (meta⁺ Unit))
-- -- (c + Calf.Data.List.foldr (λ _ → suc) 0 l * c) (ret triv)

-- -- scan/divconq/correct : (M : ◯-Monoid A) → ◯ (scan/divconq M ≡ scan/bruteforce M)
-- -- scan/divconq/correct M = {!  !}
