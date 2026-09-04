module Examples.TreeSum where

open import Calf.Core.Cost
open import Calf.Value
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


open import Calf.Value.Product

SealPar : 𝒱 → 𝒱
SealPar X = Σ[ (s , w) ∈ X × X ] s ⊑ w

SealPar-map : (X → Y) → SealPar X → SealPar Y
SealPar-map f ((x₁ , x₂) , h) = (f x₁ , f x₂) , ⊑-mono f h

join : isPreorder X → SealPar (SealPar X) → SealPar X
join isPreorderX ((((x₁ , _) , h₁) , ((_ , x₂) , _)) , h) = (x₁ , x₂) , ⊑-trans isPreorderX h₁ (⊑-mono (proj₂ ∘ proj₁) h)

opaque
  work-span : SealPar ℂ → ℂ
  work-span = proj₁ ∘ proj₁

  work-span-unit : ∀ (c : ℂ) {h} → work-span ((c , c) , h) ≡ c
  work-span-unit c = refl

  work-span-mult : (comma : SealPar (SealPar ℂ)) → work-span (SealPar-map work-span comma) ≡ work-span (join isPreorderℂ comma)
  work-span-mult comma = refl

  work-span-⊔ : ∀ {s₁ w₁ h₁ s₂ w₂ h₂} →
    work-span ((s₁ , w₁) , h₁) ⊔ℂ work-span ((s₂ , w₂) , h₂) ≡
    work-span ((s₁ ⊔ℂ s₂ , w₁ +ℂ w₂) , {!   !})
  work-span-⊔ = refl

depth≤size : (t : Tree) → depth t ≤ size t
depth≤size = {!   !}

sum-bound : U (Tree ⇀ F ℕ)
sum-bound t =
  charge (F _)
    (work-span (((# depth t) , (# size t)) , ≤⇒⊑ℂ (depth≤size t)))
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
        charge (F _) (work-span ((0ℂ , 0ℂ) , ≤⇒⊑ℂ (depth≤size (leaf x)))) (ret x)
      ∎
    aux (node t₁ t₂) =
        ( bind[ F _ ] (n₁ , n₂) ← sum t₁ ∥ sum t₂ ⨾
          add n₁ n₂
        )
      ≡⟨ cong₂ (λ e₁ e₂ → bind[ F _ ] (n₁ , n₂) ← e₁ ∥ e₂ ⨾ add n₁ n₂) (aux t₁) (aux t₂) ⟩
        ( bind[ F _ ] (n₁ , n₂) ←
            charge (F _) (work-span (((# depth t₁) , (# size t₁)) , ≤⇒⊑ℂ (depth≤size t₁))) (ret (sum-spec t₁)) ∥
            charge (F _) (work-span (((# depth t₂) , (# size t₂)) , ≤⇒⊑ℂ (depth≤size t₂))) (ret (sum-spec t₂)) ⨾
          add n₁ n₂
        )
      ≡⟨ {!   !} ⟩
        charge (F _)
          (work-span (((# depth t₁) , (# size t₁)) , {!   !}) ⊔ℂ work-span (((# depth t₂) , (# size t₂)) , {!   !}) +ℂ 1ℂ)
          (ret (sum-spec t₁ + sum-spec t₂))
      ≡⟨ {! work-span-⊔  !} ⟩
        charge (F _)
          (work-span (((# (depth t₁ ⊔ depth t₂)) , (# (size t₁ + size t₂))) , {!   !}) +ℂ 1ℂ)
          (ret (sum-spec t₁ + sum-spec t₂))
      ≡⟨ {!   !} ⟩
        charge (F _) (work-span (((# suc (depth t₁ ⊔ depth t₂)) , (# suc (size t₁ + size t₂))) , ≤⇒⊑ℂ (depth≤size (node t₁ t₂)))) (ret (sum-spec t₁ + sum-spec t₂))
      ∎

sum-bounded : sum ⊑ sum-bound
sum-bounded = ⊑-reflexive sum-costs
