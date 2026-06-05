open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Univalence using (ua)
open import Cubical.Data.Sigma

module Calf.Computation.PList2 where

open import Calf.Core.Cost
open import Calf.Value
open import Calf.Value.List
import Calf.Value.Closed as ●ᵛ
import Calf.Value.Open as ◯ᵛ
open import Calf.Computation
open import Calf.Computation.Free
open import Calf.Computation.Copower
open import Calf.Computation.Open as ◯ᶜ
open import Calf.Computation.Closed as ●ᶜ
open import Calf.Computation.Glue
open import Calf.Computation.Potential
open import Cubical.Data.Nat
open import Data.Nat.Combinatorics using (_C_)

_⊙_ : ℕ → val ℂ → val ℂ
zero ⊙ c = 0ℂ
suc n ⊙ c = c +ℂ (n ⊙ c)

binom : ℕ → ℕ → ℕ
binom n k = _C_ n k

opaque
  PList₂ : val ℂ → val ℂ → 𝒱 → 𝒞
  PList₂ c-linear c-quadratic X =
    Glueᶜ'
      (F (Listᵛ X))
      (F (Listᵛ X))
      (bind' (λ l → F _ .charge ((length l ⊙ c-linear) +ℂ (binom (length l) 2 ⊙ c-quadratic)) (ret l)))

  pnil₂ : ∀ {c-lin c-quad} → cmp (PList₂ c-lin c-quad X)
  pnil₂ {X} {c-lin} {c-quad} =
    triangleᶜ'
      (ret [])
      (ret [])
      $
        bind' (λ l → F _ .charge ((length l ⊙ c-lin) +ℂ (binom (length l) 2 ⊙ c-quad)) (ret l)) .U (ret [])
      ≡⟨ bind'/β ⟩
        F _ .charge (0ℂ +ℂ 0ℂ) (ret [])
      ≡⟨ cong (λ c → F _ .charge c (ret [])) (+ℂ-identityˡ 0ℂ) ⟩
        F _ .charge 0ℂ (ret [])
      ≡⟨ F _ .charge/0 ⟩
        ret []
      ∎

  -- pcons₂' : ∀ {c-lin c-quad} → val X → PList₂ (c-lin +ℂ c-quad) c-quad X ⊸ PList₂ c-lin c-quad X
  -- pcons₂' {X} {c-lin} {c-quad} x =
  --   squareᶜ' {F _} {F _} {_} {F _} {F _} {_}
  --     (bind' (λ l → ret (x ∷ l)))
  --     (bind' (λ l → F _ .charge c-lin (ret (x ∷ l))))
  --     λ a-⊤ →
  --         bind' (λ l → F _ .charge ((length l ⊙ c-lin) +ℂ (binom (length l) 2 ⊙ c-quad)) (ret l)) .U (bind' (ret ∘ (x ∷_)) .U a-⊤)
  --       ≡⟨ {!   !} ⟩
  --         bind' (λ l → F _ .charge ((length (x ∷ l) ⊙ c-lin) +ℂ (binom (length l) 2 ⊙ c-quad)) (ret (x ∷ l))) .U a-⊤
  --       ≡⟨ {! lemma  !} ⟩
  --         bind' (λ l → F _ .charge (((length l ⊙ (c-lin +ℂ c-quad)) +ℂ (binom (length l) 2 ⊙ c-quad)) +ℂ c-lin) (ret (x ∷ l))) .U a-⊤
  --       ≡⟨ {! F _ .charge/+  !} ⟩
  --         bind' (λ l → F _ .charge ((length l ⊙ (c-lin +ℂ c-quad)) +ℂ (binom (length l) 2 ⊙ c-quad)) (F _ .charge c-lin (ret (x ∷ l)))) .U a-⊤
  --       ≡⟨ {!   !} ⟩
  --         bind' (λ l → F _ .charge c-lin (ret (x ∷ l))) .U (bind' (λ l → F _ .charge ((length l ⊙ (c-lin +ℂ c-quad)) +ℂ (binom (length l) 2 ⊙ c-quad)) (ret l)) .U a-⊤)
  --       ∎
  --   where
  --     lemma : ∀ n → ((n ⊙ (c-lin +ℂ c-quad)) +ℂ (binom n 2 ⊙ c-quad)) +ℂ c-lin ≡ (suc n ⊙ c-lin) +ℂ (binom n 2 ⊙ c-quad)
  --     lemma n = {!   !}

  pcons₂ : ∀ {c-lin c-quad} → val X → ▷'[ c-lin ] (PList₂ (c-quad +ℂ c-lin) c-quad X) ⊸ PList₂ c-lin c-quad X
  pcons₂ = {!   !}

pfoldr₂ : ∀ {c-lin c-quad} (A : val ℂ → 𝒞)
  → (∀ c-lin → cmp (A c-lin))
  → (∀ c-lin → val X → (▷'[ c-lin ] (A (c-quad +ℂ c-lin))) ⊸ A c-lin)
  → PList₂ c-lin c-quad X ⊸ A c-lin
pfoldr₂ A e-nil e-cons .U g = transport (sym (ua (𝒞-fracture-equiv (A _)))) {!   !}
pfoldr₂ A e-nil e-cons .charge = {!   !}
