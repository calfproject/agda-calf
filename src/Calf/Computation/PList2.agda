open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Foundations.Equiv

module Calf.Computation.PList2 (φ : Type) (φ-isProp : isProp φ) where

open import Calf.Core.Cost
open import Calf.Value
open import Calf.Value.List
open import Calf.Value.Closed φ φ-isProp as ◯ᵛ
open import Calf.Computation
open import Calf.Computation.Free
open import Calf.Computation.Copower
open import Calf.Computation.Open φ φ-isProp as ◯ᶜ
open import Calf.Computation.Closed φ φ-isProp as ●ᶜ
open import Calf.Computation.Glue φ φ-isProp
open import Calf.Computation.Potential φ φ-isProp
open import Cubical.Data.Nat
open import Data.Nat.Combinatorics using (_C_)

_⊙_ : ℕ → val ℂ → val ℂ
zero ⊙ c = 0ℂ
suc n ⊙ c = c +ℂ (n ⊙ c)

binom : ℕ → ℕ → ℕ
binom n k = _C_ n k

PList2 : val ℂ → val ℂ → 𝒱 → 𝒞
PList2 c-linear c-quadratic X =
  Glueᶜ
    (●ᶜ (F (Listᵛ X)) , ●ᶜ-ηᶜ-isEquiv)
    (◯ᶜ (F (Listᵛ X)) , ◯ᶜ-ηᶜ-isEquiv)
    (●ᶜ.map (bind' id⊸ (λ l → F _ .charge ((length l ⊙ c-linear) +ℂ (binom (length l) 2 ⊙ c-quadratic)) (ret l)) ⨾⊸ η∘ᶜ {F _}))

pnil : ∀ {c-lin c-quad X} → cmp (PList2 c-lin c-quad X)
pnil = {!   !}

pcons : ∀ {c-lin c-quad X} → ▷'[ c-lin ] (PList2 (c-lin +ℂ c-quad) c-quad X) ⊸ PList2 c-lin c-quad X
pcons = {!   !}
