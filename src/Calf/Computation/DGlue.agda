open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure

module Calf.Computation.DGlue where

open import Calf.Core.Cost
open import Calf.Core.Directed
open import Calf.Computation
open import Calf.Value
import Calf.Value.Closed as ●ᵛ
import Calf.Value.Open as ◯ᵛ
open import Calf.Value.Glue
open import Calf.Computation.Power
open import Calf.Computation.Open as ◯ᶜ
open import Calf.Computation.Closed as ●ᶜ
open import Calf.Computation.Glue

record DGlue (X• : Type•) (X◦ : Type◦) (χ• : ⟨ X• ⟩ → ● ⟨ X◦ ⟩) : Type where
  field
    • : ⟨ X• ⟩
    ◦ : ⟨ X◦ ⟩
    •→◦ : χ• • ⊑ η• ◦
open DGlue public

DGlueᵛ : (X• : 𝒱•) (X◦ : 𝒱◦) (χ• : val (X• .fst) → val (●ᵛ (X◦ .fst))) → 𝒱
DGlueᵛ X• X◦ χ• .val = DGlue (𝒱•→Type• X•) (𝒱◦→Type◦ X◦) χ•
DGlueᵛ X• X◦ χ• .is-set = {!   !}
DGlueᵛ X• X◦ χ• .is-preorder = {!   !}

DGlueᶜ : (A• : 𝒞•) (A◦ : 𝒞◦) (α• : A• .fst ⊸ ●ᶜ (A◦ .fst)) → 𝒞
DGlueᶜ A• A◦ α• .U = DGlueᵛ (U• A•) (U◦ A◦) (α• .U)
DGlueᶜ A• A◦ α• .charge c a .• = A• .fst .charge c (a .•)
DGlueᶜ A• A◦ α• .charge c a .◦ = A◦ .fst .charge c (a .◦)
DGlueᶜ A• A◦ α• .charge c a .•→◦ =
  let open ⊑ᵛ-Reasoning (U (●ᶜ (A◦ .fst))) in
  begin
    α• .U (A• .fst .charge c (a .•))
  ≡ᵛ⟨ α• .charge c (a .•) ⟩
    ●ᶜ (A◦ .fst) .charge c (α• .U (a .•))
  ⊑ᵛ⟨ ⊑ᵛ-mono (●ᶜ (A◦ .fst) .charge c) (a .•→◦) ⟩
    η• (A◦ .fst .charge c (a .◦))
  ∎ᵛ
DGlueᶜ A• A◦ α• .charge/0 {a} i .• = A• .fst .charge/0 {a .•} i
DGlueᶜ A• A◦ α• .charge/0 {a} i .◦ = A◦ .fst .charge/0 {a .◦} i
DGlueᶜ A• A◦ α• .charge/0 {a} i .•→◦ = {! ⊑ᵛ-isProp  !}
DGlueᶜ A• A◦ α• .charge/+ = {! same   !}
