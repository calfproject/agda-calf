open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma

module Calf.Computation.PList1 where

open import Calf.Core.Abstract
open import Calf.Core.Cost
open import Calf.Value
open import Calf.Value.List
import Calf.Value.Closed as ●ᵛ
import Calf.Value.Open as ◯ᵛ
open import Calf.Computation
open import Calf.Computation.Free as F
open import Calf.Computation.Copower
open import Calf.Computation.Open as ◯ᶜ
open import Calf.Computation.Closed as ●ᶜ
open import Calf.Computation.Glue
open import Calf.Computation.Potential
open import Cubical.Data.Nat

_⊙_ : ℕ → val ℂ → val ℂ
zero ⊙ c = 0ℂ
suc n ⊙ c = c +ℂ (n ⊙ c)

opaque
  PList₁ : val ℂ → 𝒱 → 𝒞
  PList₁ c-linear X =
    Glueᶜ'
      (F (Listᵛ X))
      (F (Listᵛ X))
      (bind' λ l → F _ .charge (length l ⊙ c-linear) (ret l))

  pnil₁ : ∀ {c-lin} → cmp (PList₁ c-lin X)
  pnil₁ {c-lin = c-lin} =
    triangleᶜ'
      {F _} {F _} {bind' (λ l → F _ .charge (length l ⊙ c-lin) (ret l))}
      (ret [])
      (ret [])
      (bind'/β ∙ F _ .charge/0)

  pcons₁ : ∀ {c-lin} → val X → ▷'[ c-lin ] (PList₁ c-lin X) ⊸ PList₁ c-lin X
  pcons₁ {X} {c-lin = c-lin} x =
    subst (_⊸ PList₁ c-lin X)
      ( Glueᶜ' (F (Listᵛ X)) (F (Listᵛ X)) (CHARGE c-lin ⨾⊸ bind' (λ l → F _ .charge (length l ⊙ c-lin) (ret l)))
      ≡⟨ {!   !} ⟩
        ▷'[ c-lin ] (PList₁ c-lin X)
      ∎) $
    squareᶜ'
      (F.map (x ∷_))
      (F.map (x ∷_))
      λ e →
        bind' (λ l → F _ .charge (length l ⊙ c-lin) (ret l)) .U (F.map (x ∷_) .U e)
      ≡⟨ {!   !} ⟩
        F.map (x ∷_) .U (bind' (λ l → F _ .charge (length l ⊙ c-lin) (ret l)) .U (F _ .charge c-lin e))
      ∎

  pfoldr₁ : ∀ {c-lin}
    → cmp A
    → (val X → (▷'[ c-lin ] A ⊸ A))
    → PList₁ c-lin X ⊸ A
  pfoldr₁ {X = X} {c-lin = c-lin} enil econs =
    subst (PList₁ c-lin X ⊸_) Glueᶜ'-id $
    squareᶜ'
      (bind' λ l → {!   !})
      {!   !}
      {!   !}
