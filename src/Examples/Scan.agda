{-# OPTIONS --rewriting #-}

open import Examples.Sorting.Sequential.Comparable

module Examples.Scan (M : Comparable) where 

open Comparable M
open import Examples.Sorting.Sequential.Core M

open import Algebra.Cost

-- costMonoid = ℕ-CostMonoid
-- open CostMonoid costMonoid

open import Calf costMonoid hiding (A)
open import Calf.Data.Nat
open import Calf.Data.List using (list; []; _∷_; _∷ʳ_; [_]; length; _++_; reverse ; splitAt  ) renaming ( map to listmap )
open import Calf.Data.IsBounded costMonoid
open import Calf.Data.IsBoundedG costMonoid
-- open import Calf.Data.BigO costMonoid
open import Calf.Data.Product 

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; _≢_; module ≡-Reasoning)
open import Data.Nat as Nat using (_+_; _⊔_)
open import Data.Nat.Properties as N using ()



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
scan/bruteforce/help f e (x ∷ L) = bind (F _) (f (e , x)) (λ y → bind (F _) (scan/bruteforce/help f e L) λ { (ys , r) →  ret ( y ∷ ys , r )}) 

scan/bruteforce : {A : tp⁺} → ◯-Monoid A → (cmp  (Π (list A)  (λ _ → F (list A ×⁺ A))))
scan/bruteforce M L = scan/bruteforce/help (◯-Monoid.f M) (◯-Monoid.identity M) L

scan/bruteforce/cost :  
      (m : ◯-Monoid A) → 
      (c : ℂ) →
      ((a b : val A) → IsBounded A (◯-Monoid.f m (a , b)) c) → 
      (l : val (list A)) →
      IsBounded (list A ×⁺ A) (scan/bruteforce m l) (length l * c)
scan/bruteforce/cost m c h []      = ≤⁻-refl
scan/bruteforce/cost m c h (x ∷ l) = 
  let open ≤⁻-Reasoning cost in
  begin
   bind (F unit) (◯-Monoid.f m (◯-Monoid.identity m , x)) (λ _ →
    bind (F unit) (scan/bruteforce/help (◯-Monoid.f m) (◯-Monoid.identity m) l) (λ _ → 
      ret triv))
  ≲⟨ bind-monoˡ-≤⁻ (λ _ →
        bind (F unit) (scan/bruteforce/help (◯-Monoid.f m) (◯-Monoid.identity m) l) (λ _ → ret triv)) 
        (h (◯-Monoid.identity m) x) ⟩
   bind (F unit) (step⋆ c) (λ _ →
    bind (F unit) (scan/bruteforce/help (◯-Monoid.f m) (◯-Monoid.identity m) l) (λ _ → 
      ret triv))
  ≲⟨ bind-monoʳ-≤⁻ (step⋆ c) (λ _ → scan/bruteforce/cost m c h l) ⟩
    bind (F unit) (step⋆ c) (λ _ →
      bind (F unit) (step⋆ (length l * c)) (λ _ → 
        ret triv))
  ≡⟨⟩
    step⋆ (c + length l * c)  
  ∎

open import Examples.Sorting.Sequential.MergeSort.Split M


mapList : cmp (Π (U (Π A λ _ → F B)) (λ _ → Π (list A) (λ _ → F (list B))))
mapList f [] = ret []
mapList f (x ∷ l) = 
  bind (F _) (mapList f l) λ l' → 
    bind (F _) (f x) λ x' → 
      ret (x' ∷ l')

appendList : cmp (Π (list A) (λ _ → Π (list A) λ _ → F (list A)))
appendList [] l = ret l
appendList (x ∷ xs) l = 
  step (F _) 1 (
  bind (F _) (appendList xs l) λ l' → 
    ret (x ∷ l'))

scan/divconq/help : 
  cmp (Π (U (Π (A ×⁺ A) (λ _ → F A))) (λ _ → 
       Π A (λ _ → 
       Π (list A) (λ l → 
       Π nat λ k →
       Π (meta⁺ (⌈log₂ length l ⌉ Nat.≤ k)) λ _ → 
        F (list A ×⁺ A)))))
scan/divconq/help f e l Nat.zero p = ret (l , e)
scan/divconq/help f e [] (suc Nat.zero) p = ret ([] , e)
scan/divconq/help f e (x ∷ l) (suc Nat.zero) p = ret (e ∷ [] , x)
scan/divconq/help f e l (2+ k) p = 
  bind (F _) (split l) λ ((l₁ , l₂) , length₁ , length₂ , l↭l₁++l₂) → 
  let
    h₁ , h₂ =
      let open N.≤-Reasoning in
      (begin
        ⌈log₂ length l₁ ⌉
      ≡⟨ Eq.cong ⌈log₂_⌉ length₁ ⟩
        ⌈log₂ ⌊ length l /2⌋ ⌉
      ≤⟨ log₂-mono (N.⌊n/2⌋≤⌈n/2⌉ (length l)) ⟩
        ⌈log₂ ⌈ length l /2⌉ ⌉
      ≤⟨ log₂-suc (length l) p ⟩
        suc k
      ∎) ,
      (begin
        ⌈log₂ length l₂ ⌉
      ≡⟨ Eq.cong ⌈log₂_⌉ length₂ ⟩
        ⌈log₂ ⌈ length l /2⌉ ⌉
      ≤⟨ log₂-suc (length l) p ⟩
        suc k
      ∎)
  in
  bind (F _) (scan/divconq/help f e l₁ (suc k) h₁) λ (l₁' , b') → 
  bind (F _) (scan/divconq/help f e l₂ (suc k) h₂) λ (l₂' , c') → 
  bind (F _) (mapList (λ x → f (b' , x)) l₂') λ r' → 
  bind (F _) (appendList l₁' r') λ resL →
  bind (F _) (f (b' , c')) λ res → 
  ret (resL , res)

scan/divconq : ◯-Monoid A → (cmp  (Π (list A)  (λ _ → F (list A ×⁺ A))))
scan/divconq M L = scan/divconq/help (◯-Monoid.f M) (◯-Monoid.identity M) L ⌈log₂ length L ⌉ {! Nat.≤-refl  !} 
-- should probably make this log2 L 

-- scan/divconq/correct : (M : ◯-Monoid A) → ◯ (scan/divconq M ≡ scan/bruteforce M)
-- scan/divconq/correct M = {!  !}
