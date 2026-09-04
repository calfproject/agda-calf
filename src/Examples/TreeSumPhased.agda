module Examples.TreeSumPhased where

open import Calf.Core.Cost
open import Calf.Value hiding (id)
open import Calf.Value.Nat
open import Calf.Computation
open import Calf.Computation.Free
open import Calf.Computation.Power

add : U (ℕ ⇀ ℕ ⇀ F ℕ)
add m n = chargeℕ (F _) 1 (ret (m + n))


data Tree : 𝒱 where
  leaf : ℕ → Tree
  node : Tree → Tree → Tree

sum : U (Tree ⇀ F ℕ)
sum (leaf x)     = ret x
sum (node t₁ t₂) =
  bind[ F _ ] (n₁ , n₂) ← sum t₁ ∥ sum t₂ ⨾
  add n₁ n₂

sum-spec : Tree → ℕ
sum-spec (leaf x)     = x
sum-spec (node t₁ t₂) = sum-spec t₁ + sum-spec t₂

size : Tree → ℕ
size (leaf x)     = 0
size (node t₁ t₂) = suc (size t₁ + size t₂)

depth : Tree → ℕ
depth (leaf x)     = 0
depth (node t₁ t₂) = suc (depth t₁ ⊔ depth t₂)


postulate
  SEQ : hProp ℓ-zero
  -- BEH ⊢ SEQ ⊢ ABS ⊢ ⊤
  -- BEH ⊢ SEQ, ABS ⊢ ⊤

open import Calf.Value.Product
open import Calf.Value.Open SEQ as ◯    -- sequential
open import Calf.Value.Closed SEQ as ●  -- parallel
open import Calf.Value.Seal SEQ

SealPar : 𝒱 → 𝒱
SealPar = Seal

η : X → SealPar X
η x = (η• x , η◦ x) , ⊑-refl

SealPar-map : (X → Y) → SealPar X → SealPar Y
SealPar-map f ((par , seq) , h) =
  (●.map f par , ◯.map f seq) , {!   !}

sjoin : isPreorder X → SealPar (SealPar X) → SealPar X
sjoin isPreorderX = {!   !} -- ((((x₁ , _) , h₁) , ((_ , x₂) , _)) , h) = (x₁ , x₂) , ⊑-trans isPreorderX h₁ (⊑-mono (proj₂ ∘ proj₁) h)

postulate
  work-span : SealPar ℂ → ℂ

  work-span-unit : ∀ (c : ℂ) {h} → work-span ((η• c , η◦ c) , h) ≡ c

  work-span-mult : (comma : SealPar (SealPar ℂ)) →
    work-span (SealPar-map work-span comma) ≡
    work-span (sjoin isPreorderℂ comma)

  work-span-⊔ : ∀ {s₁ w₁ h₁ s₂ w₂ h₂} →
    work-span ((s₁ , w₁) , h₁) ⊔ℂ work-span ((s₂ , w₂) , h₂) ≡
    work-span ((●.map₂ _⊔ℂ_ s₁ s₂ , ◯.map₂ _+ℂ_ w₁ w₂) , {!   !})

depth≤size : (t : Tree) → depth t ≤ size t
depth≤size = {!   !}

sum-bound : U (Tree ⇀ F ℕ)
sum-bound t =
  charge (F _)
    (work-span ((η• (# depth t) , η◦ (# size t)) , ⊑-mono (η• ∘ η◦) (≤⇒⊑ℂ (depth≤size t))))
    (ret (sum-spec t))

sum-costs : sum ≡ sum-bound
sum-costs = funExt aux
  where
    aux : (t : Tree) → sum t ≡ sum-bound t
    aux (leaf x)     =
        ret x
      ≡⟨ sym (F _ .charge-0) ⟩
        charge (F _) 0ℂ (ret x)
      ≡⟨ cong (λ c → charge (F _) c (ret x)) (sym (work-span-unit 0ℂ)) ⟩
        charge (F _) (work-span ((η• 0ℂ , η◦ 0ℂ) , ⊑-mono (η• ∘ η◦) (≤⇒⊑ℂ (depth≤size (leaf x))))) (ret x)
      ∎
    aux (node t₁ t₂) =
        ( bind[ F _ ] (n₁ , n₂) ← sum t₁ ∥ sum t₂ ⨾
          add n₁ n₂
        )
      ≡⟨ cong₂ (λ e₁ e₂ → bind[ F _ ] (n₁ , n₂) ← e₁ ∥ e₂ ⨾ add n₁ n₂) (aux t₁) (aux t₂) ⟩
        ( bind[ F _ ] (n₁ , n₂) ←
            charge (F _) (work-span ((η• (# depth t₁) , η◦ (# size t₁)) , ⊑-mono (η• ∘ η◦) (≤⇒⊑ℂ (depth≤size t₁)))) (ret (sum-spec t₁)) ∥
            charge (F _) (work-span ((η• (# depth t₂) , η◦ (# size t₂)) , ⊑-mono (η• ∘ η◦) (≤⇒⊑ℂ (depth≤size t₂)))) (ret (sum-spec t₂)) ⨾
          add n₁ n₂
        )
      ≡⟨ {!   !} ⟩
        charge (F _)
          (work-span ((η• (# depth t₁) , η◦ (# size t₁)) , {!   !}) ⊔ℂ work-span ((η• (# depth t₂) , η◦ (# size t₂)) , {!   !}) +ℂ 1ℂ)
          (ret (sum-spec t₁ + sum-spec t₂))
      ≡⟨ {!   !} ⟩
        charge (F _)
          (work-span ((η• (# (depth t₁ ⊔ depth t₂)) , η◦ (# (size t₁ + size t₂))) , {!   !}) +ℂ 1ℂ)
          (ret (sum-spec t₁ + sum-spec t₂))
      ≡⟨ {!   !} ⟩
        charge (F _) (work-span ((η• (# suc (depth t₁ ⊔ depth t₂)) , η◦ (# suc (size t₁ + size t₂))) , ⊑-mono (η• ∘ η◦) (≤⇒⊑ℂ (depth≤size (node t₁ t₂))))) (ret (sum-spec t₁ + sum-spec t₂))
      ∎

work-thm : ⟨ SEQ ⟩ → sum ≡ (λ t → charge (F _) (# size t) (ret (sum-spec t)))
work-thm = {!   !}

-- QUESTION: why not just upper bound though...?

sum-bounded : sum ⊑ sum-bound
sum-bounded = ⊑-reflexive sum-costs
