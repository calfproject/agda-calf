open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

module Calf.Computation.CList2 where

open import Calf.Core.Cost
open import Calf.Value
open import Calf.Value.List
open import Calf.Value.Nat
open import Calf.Computation
open import Calf.Computation.Copower
open import Calf.Computation.Credit
open import Calf.Computation.Tensor
open import Calf.Computation.Potential using (▷-Σᶜ)

clist₂-potential : ℂ → ℂ → ℕ → ℂ
clist₂-potential c-lin c-quad zero = 0ℂ
clist₂-potential c-lin c-quad (suc n) = c-lin +ℂ clist₂-potential (c-quad +ℂ c-lin) c-quad n

opaque
  CList₂ : ℂ → ℂ → 𝒱ₛ → 𝒞
  CList₂ c-lin c-quad Xₛ = [ l ∈ Listₛ Xₛ ] ⋊ ▷[ clist₂-potential c-lin c-quad (length l) ] ⊤

  cnil₂ : ∀ {c-lin c-quad} → U (CList₂ c-lin c-quad Xₛ)
  cnil₂ = [] , subst U (sym ▷/0) 0ℂ

  ccons₂ : ∀ {c-lin c-quad}
    → ⟨ Xₛ ⟩ → ▷[ c-lin ] CList₂ (c-quad +ℂ c-lin) c-quad Xₛ ⊸ CList₂ c-lin c-quad Xₛ
  ccons₂ {X} {c-lin} {c-quad} x =
    transport (cong (_⊸ CList₂ c-lin c-quad X) (sym (▷-Σᶜ c-lin))) $
    Σᶜ-rec λ l → transport (cong (_⊸ CList₂ c-lin c-quad X) ▷/+) (Σᶜ-in (x ∷ l))

  cfoldr₂ : ∀ {c-lin c-quad} (A : ℂ → 𝒞)
    → (∀ c → U (A c))
    → (∀ c → ⟨ Xₛ ⟩ → ▷[ c ] A (c-quad +ℂ c) ⊸ A c)
    → CList₂ c-lin c-quad Xₛ ⊸ A c-lin
  cfoldr₂ {X} {c-lin} {c-quad} A e-nil e-cons = Σᶜ-rec (λ l → go l c-lin)
    where
      go : (l : List ⟨ X ⟩) (c : ℂ) → ▷[ clist₂-potential c c-quad (length l) ] ⊤ ⊸ A c
      go [] c = ▷⊤-rec (e-nil c)
      go (x ∷ l) c =
        transport (cong (_⊸ A c) (sym ▷/+)) (▷-map (go l (c-quad +ℂ c)) ⨾ᶜ e-cons c x)
