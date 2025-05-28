{-# OPTIONS --rewriting #-}

module Examples.Amortized.QueueAgain where

open import Algebra.Cost

costMonoid = ℕ-CostMonoid
open CostMonoid costMonoid

open import Calf costMonoid 
open import Calf.Data.Nat renaming (_+_ to _⊕_)
open import Calf.Data.Product
open import Calf.Data.List
open import Calf.Data.IsBounded costMonoid
open import Data.Nat.Properties using (+-comm; n≤1+n)
open import Data.List.Properties using (++-assoc; unfold-reverse; ++-identityʳ)

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; module ≡-Reasoning)

record Queue : Set where
  field
    Q : tp⁺
    empty   : cmp (F Q)
    enqueue : cmp (Π Q (λ _ → Π nat (λ _ → F Q)))
    dequeue : cmp (Π Q (λ _ → F (nat ×⁺ Q)))

ListQueue : Queue
ListQueue .Queue.Q = list nat
ListQueue .Queue.empty = ret []
ListQueue .Queue.enqueue l n = step (F _) 1 (ret (l ++ n ∷ []))
ListQueue .Queue.dequeue [] = ret (0 , [])
ListQueue .Queue.dequeue (x ∷ l) = ret (x , l)

opaque
  BatchedQueue : Queue
  BatchedQueue .Queue.Q = list nat ×⁺ list nat
  BatchedQueue .Queue.empty = ret ([] , [])
  BatchedQueue .Queue.enqueue (l₁ , l₂) n = ret (n ∷ l₁ , l₂)
  BatchedQueue .Queue.dequeue (l₁ , []) with reverse l₁
  ... | [] = ret (0 , ([] , []))
  ... | x ∷ l₁' = step (F _) (length l₁) (ret (x , ([] , l₁'))) 
  BatchedQueue .Queue.dequeue (l₁ , x ∷ l₂) = ret (x , l₁ , l₂)

open Queue 

record QueueHom (Queue Queue' : Queue) : Set where 
  field 
    ϕ : cmp (Π (Queue .Q) λ _ → F (Queue' .Q))
    ϕ/empty : 
        bind (F _) (Queue .empty) ϕ 
      ≤⁻[ F (Queue' .Q) ] 
        Queue' .empty
    ϕ/enqueue : (q : val (Queue .Q)) (n : val nat) → 
        bind (F _) (Queue .enqueue q n) ϕ 
      ≤⁻[ F (Queue' .Q) ] 
        bind (F _) (ϕ q) (λ q' → Queue' .enqueue q' n)
    ϕ/dequeue : (q : val (Queue .Q)) →
        bind (F _) (Queue .dequeue q) (λ { (_ , q') → ϕ q'}) 
      ≤⁻[ F (Queue' .Q) ] 
        bind (F _) (ϕ q) (λ q' → bind (F _) (Queue' .dequeue q') (λ { (_ , q'') → ret q''}))
    ϕ/total : (q : val (Queue .Q)) → 
        ret triv
      ≤⁻[ F unit ] 
        bind (F _) (ϕ q) (λ _ → ret triv)

open QueueHom

opaque 
  unfolding BatchedQueue
  
  BQ⇒LQ : QueueHom BatchedQueue ListQueue 
  BQ⇒LQ .ϕ (l₁ , l₂) = step (F _) (length l₁) (ret (l₂ ++ reverse l₁))
  BQ⇒LQ .ϕ/empty = ≤⁻-refl
  BQ⇒LQ .ϕ/enqueue (l₁ , l₂) n = 
    let open ≤⁻-Reasoning (F _) in
    begin 
      bind (F (list nat)) (ret {A = list nat ×⁺ list nat} (n ∷ l₁ , l₂)) (BQ⇒LQ .ϕ)
    ≡⟨⟩
      step (F (list nat)) (length (n ∷ l₁))
        (ret (l₂ ++ reverse (n ∷ l₁)))
    ≡⟨ Eq.cong (λ c → step (F (list nat)) c (ret (l₂ ++ (reverse (n ∷ l₁))))) (+-comm 1 (length l₁)) ⟩
      step (F (list nat)) (length l₁ ⊕ 1)
        (ret (l₂ ++ (reverse (n ∷ l₁))))
    ≡⟨ Eq.cong (step (F (list nat)) (length l₁ ⊕ 1)) (Eq.cong ret (Eq.cong (λ l → l₂ ++ l) (unfold-reverse n l₁))) ⟩
      step (F (list nat)) (length l₁ ⊕ 1)
        (ret (l₂ ++ (reverse l₁ ++ n ∷ [])))
    ≡⟨ Eq.cong (step (F (list nat)) (length l₁ ⊕ 1)) (Eq.cong ret (++-assoc l₂ (reverse l₁) (n ∷ []))) ⟨
      step (F (list nat)) (length l₁ ⊕ 1)
        (ret ((l₂ ++ reverse l₁) ++ n ∷ []))
    ≡⟨⟩
      step (F (list nat)) (length l₁) 
        (step (F (list nat)) 1 (ret ((l₂ ++ reverse l₁) ++ n ∷ [])))
    ≡⟨⟩
      bind (F (list nat))
        (step (F (list nat)) (length l₁) (ret (l₂ ++ reverse l₁)))
        (λ q' → step (F (list nat)) 1 (ret (q' ++ n ∷ []))) 
    ∎
  BQ⇒LQ .ϕ/dequeue (l₁ , []) with reverse l₁ 
  ... | [] = step-monoˡ-≤⁻ {c' = length l₁} (ret []) z≤n 
  ... | x ∷ l₁' rewrite ++-identityʳ l₁' = ≤⁻-refl
  BQ⇒LQ .ϕ/dequeue (l₁ , (x ∷ l₂)) = ≤⁻-refl
  BQ⇒LQ .ϕ/total (l₁ , _) = step-monoˡ-≤⁻ {c' = length l₁} (ret triv) z≤n

data QueueOperation : Set where
  enq : val nat → QueueOperation
  deq : QueueOperation

apply : QueueOperation → (q : Queue) → val (q .Q) → cmp (F (q .Q))
apply (enq n) q l = q .enqueue l n 
apply deq     q l = bind (F _) (q .dequeue l) λ { (_ , l') → ret l' }

fold-apply : (ops : List QueueOperation) (q : Queue) → val (q .Q) → cmp (F (q .Q))
fold-apply [] q l = ret l
fold-apply (op ∷ ops) q l = 
  bind (F _) (fold-apply ops q l) λ l' →
  bind (F _) (apply op q l') ret 

commutes : (ops : List QueueOperation) → (q : val (BatchedQueue .Q)) →
    bind (F _) (fold-apply ops BatchedQueue q) (BQ⇒LQ .ϕ)
  ≤⁻[ F (ListQueue .Q) ] 
    bind (F _) (BQ⇒LQ .ϕ q) (λ q' → fold-apply ops ListQueue q')
commutes [] q = ≤⁻-refl
commutes (enq n ∷ ops) q = 
  let open ≤⁻-Reasoning (F _) in
  begin
    bind (F _) (fold-apply ops BatchedQueue q) (λ q' → bind (F _) (BatchedQueue .enqueue q' n) (BQ⇒LQ .ϕ))
  ≲⟨ bind-monoʳ-≤⁻ (fold-apply ops BatchedQueue q) (λ q' → BQ⇒LQ .ϕ/enqueue q' n) ⟩
    bind (F _) (fold-apply ops BatchedQueue q) (λ q' → bind (F _) (BQ⇒LQ .ϕ q') (λ q'' → ListQueue .enqueue q'' n))
  ≡⟨⟩
    bind (F _) (bind (F _) (fold-apply ops BatchedQueue q) (BQ⇒LQ .ϕ)) (λ q'' → ListQueue .enqueue q'' n)
  ≲⟨ bind-monoˡ-≤⁻ (λ q'' → ListQueue .enqueue q'' n) (commutes ops q) ⟩ 
    bind (F _) (bind (F _) (BQ⇒LQ .ϕ q) (λ q' → fold-apply ops ListQueue q')) (λ q'' → ListQueue .enqueue q'' n)
  ∎
commutes (deq ∷ ops) q = 
  let open ≤⁻-Reasoning (F _) in
  begin
    bind (F _) (fold-apply ops BatchedQueue q) (λ q' → bind (F _) (BatchedQueue .dequeue q') (λ { (_ , q'') → (BQ⇒LQ .ϕ q'') }) )
  ≲⟨ bind-monoʳ-≤⁻ (fold-apply ops BatchedQueue q) (ϕ/dequeue BQ⇒LQ)  ⟩
    bind (F _) (fold-apply ops BatchedQueue q) (λ q' → bind (F _) (BQ⇒LQ .ϕ q') (λ q'' → bind (F _) (ListQueue .dequeue q'') (λ { (_ , q''') → ret q''' })))
  ≡⟨⟩
    bind (F _) (bind (F _) (fold-apply ops BatchedQueue q) (BQ⇒LQ .ϕ)) (λ q' → bind (F _) (ListQueue .dequeue q') (λ { (_ , q'') → ret q'' }))
  ≲⟨ bind-monoˡ-≤⁻ (λ q' → bind (F _) (ListQueue .dequeue q') (λ { (_ , q'') → ret q'' })) (commutes ops q) ⟩ 
    bind (F _) (bind (F _) (BQ⇒LQ .ϕ q) (λ q' → fold-apply ops ListQueue q')) (λ q'' → bind (F _) (ListQueue .dequeue q'') (λ { (_ , q''') → ret q''' }))
  ∎

thm : (ops : List QueueOperation) → 
  IsBounded (BatchedQueue .Q) (bind (F _) (BatchedQueue .empty) (λ emp → fold-apply ops BatchedQueue emp)) (length ops)
thm = BQ/bound 
  where 
    LQ/bound : (ops : List QueueOperation) → 
      Σ[ l ∈ val (ListQueue .Q) ] 
        fold-apply ops ListQueue [] 
      ≤⁻[ F _ ] 
        step (F _) (length ops) (ret l)
    LQ/bound [] = [] , ≤⁻-refl
    LQ/bound (enq n ∷ ops) with LQ/bound ops 
    ... | l , leq = l ++ n ∷ [] , 
      let open ≤⁻-Reasoning (F _) in
      begin
        bind (F _) (fold-apply ops ListQueue []) (λ l' → step (F _) 1 (ret (l' ++ n ∷ [])))
      ≲⟨ bind-monoˡ-≤⁻ (λ l' → step (F _) 1 (ret (l' ++ n ∷ []))) leq ⟩
        step (F _) (length ops ⊕ 1) (ret (l ++ n ∷ []))
      ≡⟨ Eq.cong (λ c → step (F _) c (ret (l ++ n ∷ []))) (+-comm (length ops) 1) ⟩
        step (F _) (1 + length ops) (ret (l ++ n ∷ []))
      ∎
    LQ/bound (deq ∷ ops) with LQ/bound ops 
    ... | [] , leq = [] , 
      let open ≤⁻-Reasoning (F _) in
      begin
        bind (F _) (fold-apply ops ListQueue []) (λ l' → bind (F _) (ListQueue .dequeue l') (λ { (_ , l) → ret l }))
      ≲⟨ bind-monoˡ-≤⁻ (λ l' → bind (F _) (ListQueue .dequeue l') (λ { (_ , l) → ret l })) leq ⟩
        step (F _) (length ops) (ret [])
      ≲⟨ step-monoˡ-≤⁻ (ret []) (n≤1+n (length ops)) ⟩
        step (F _) (1 ⊕ length ops) (ret [])
      ∎
    ... | (_ ∷ l) , leq = l , 
      let open ≤⁻-Reasoning (F _) in
      begin
        bind (F _) (fold-apply ops ListQueue []) (λ l' → bind (F _) (ListQueue .dequeue l') (λ { (_ , l) → ret l }))
      ≲⟨ bind-monoˡ-≤⁻ (λ l' → bind (F _) (ListQueue .dequeue l') (λ { (_ , l) → ret l })) leq ⟩
        step (F _) (length ops) (ret l)
      ≲⟨ step-monoˡ-≤⁻ (ret l) (n≤1+n (length ops)) ⟩
        step (F _) (1 ⊕ length ops) (ret l)
      ∎

    BQ/bound : (ops : List QueueOperation) → 
      IsBounded (BatchedQueue .Q) (bind (F _) (BatchedQueue .empty) (λ emp → fold-apply ops BatchedQueue emp)) (length ops)
    BQ/bound ops with LQ/bound ops 
    ... | l , leq = 
      let open ≤⁻-Reasoning (F _) in
      begin
        bind (F _) (BatchedQueue .empty) (λ emp →
         bind (F _) (fold-apply ops BatchedQueue emp) (λ _ → 
            ret triv))
      ≲⟨ bind-monoʳ-≤⁻ (BatchedQueue .empty) (λ emp → 
          bind-monoʳ-≤⁻ (fold-apply ops BatchedQueue emp) λ q → 
            BQ⇒LQ .ϕ/total q) 
        ⟩
       bind (F _) (BatchedQueue .empty) (λ emp →
         bind (F _) (fold-apply ops BatchedQueue emp) (λ q → 
          bind (F _) (BQ⇒LQ .ϕ q) (λ _ → 
            ret triv)))
      ≡⟨⟩
        bind (F _) (BatchedQueue .empty) (λ emp →
          bind (F _) (
            bind (F _) (fold-apply ops BatchedQueue emp) (BQ⇒LQ .ϕ)
          ) (λ _ → 
            ret triv))
      ≲⟨ bind-monoʳ-≤⁻ (BatchedQueue .empty) (λ emp → 
          bind-monoˡ-≤⁻ (λ _ → ret triv) (commutes ops emp)) ⟩
        bind (F _) (BatchedQueue .empty) (λ emp →
          bind (F _) (
            bind (F _) (BQ⇒LQ .ϕ emp) (λ q → fold-apply ops ListQueue q)
          ) (λ _ → 
            ret triv))
      ≡⟨⟩
        bind (F _) (BatchedQueue .empty) (λ emp →
          bind (F _) (BQ⇒LQ .ϕ emp) (λ q → 
            bind (F _) (fold-apply ops ListQueue q) (λ _ → 
              ret triv)))
      ≡⟨⟩ 
        bind (F _) (
          bind (F _) (BatchedQueue .empty) (BQ⇒LQ .ϕ)
          ) (λ q →
            bind (F _) (fold-apply ops ListQueue q) (λ _ → 
              ret triv)) 
      ≲⟨ bind-monoˡ-≤⁻ (λ q →
          bind (F _) (fold-apply ops ListQueue q) (λ _ → 
            ret triv)) 
          (BQ⇒LQ .ϕ/empty) ⟩
        bind (F _) (ListQueue .empty) (λ q →
            bind (F _) (fold-apply ops ListQueue q) (λ _ → 
              ret triv)) 
      ≡⟨⟩
        bind (F _) (fold-apply ops ListQueue []) (λ _ → 
          ret triv)
      ≲⟨ bind-monoˡ-≤⁻ (λ _ → ret triv) leq ⟩
        step (F _) (length ops) (ret triv)
      ∎