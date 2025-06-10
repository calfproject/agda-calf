{-# OPTIONS --rewriting #-}

module Examples.Scan where 

open import Algebra.Cost

costMonoid = ℕ-CostMonoid
open CostMonoid costMonoid

open import Calf costMonoid
open import Calf.Data.Nat
open import Calf.Data.List using (list; []; _∷_; _∷ʳ_; [_]; length; _++_; reverse ; splitAt  ) renaming ( map to listmap )
open import Calf.Data.IsBounded costMonoid
open import Calf.Data.BigO costMonoid
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

splitMid : {A : tp⁺} → cmp (Π (list A) (λ _ → F (list A ×⁺ list A)))
splitMid L = ret (splitAt (length L / 2) L)

scan/divconq/help : {A : tp⁺} → cmp (Π (U (Π (A ×⁺ A) (λ _ → F A))) (λ _ → Π A (λ _ → (Π (list A) (λ _ → Π nat  λ _ → F (list A ×⁺ A))))))
scan/divconq/help f e L Nat.zero = ret (L , e)  
-- not sure if this should be L or []
-- in particular, we need to handle the |L| = 1 case somehow
scan/divconq/help f e L (suc n) = 
  bind (F _) (splitMid L) 
    (λ {(b , c) → 
      bind (F _) ((scan/divconq/help f e b n  )) 
        (λ {(l , b') →   
          bind (F _) (scan/divconq/help f e c n) 
            (λ {(r , c') →  
              bind (F _) (ret (listmap ( λ x → f (e , x)) r)) {! 
                (λ r' → ret ( l ++ r' , f (b' , c' ) ))  !}})})})
-- could change scan/divconq/help to take in the entire monoid instead - might be helpful to use properties?


scan/divconq : {A : tp⁺} → ◯-Monoid A → (cmp  (Π (list A)  (λ _ → F (list A ×⁺ A))))
scan/divconq M L = scan/divconq/help (◯-Monoid.f M) (◯-Monoid.identity M) L (⌈log₂ length L ⌉)
-- should probably make this log2 L 

scan/divconq/correct : (M : ◯-Monoid A) → ◯ (scan/divconq M ≡ scan/bruteforce M)
scan/divconq/correct M = {!  !}
