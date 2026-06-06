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
      ( Glueᶜ' (F (Listᵛ X)) (F (Listᵛ X)) (CHARGE c-lin ⨾ᶜ bind' (λ l → F _ .charge (length l ⊙ c-lin) (ret l)))
      ≡⟨ cong (Glueᶜ' _ _) (CHARGE-commute _ _) ⟩
        Glueᶜ' (F (Listᵛ X)) (F (Listᵛ X)) (bind' (λ l → F _ .charge (length l ⊙ c-lin) (ret l)) ⨾ᶜ CHARGE c-lin)
      ≡⟨ sym Glueᶜ'-Glueᶜ' ⟩
        Glueᶜ'
          (PList₁ c-lin X)
          (PList₁ c-lin X)
          (squareᶜ'
            (CHARGE c-lin)
            (CHARGE c-lin)
            (λ e → bind' (λ l → F _ .charge (length l ⊙ c-lin) (ret l)) .charge c-lin e))
      ≡⟨ cong (Glueᶜ' _ _) (squareᶜ'-charge _) ⟩
        ▷'[ c-lin ] (PList₁ c-lin X)
      ∎) $
    squareᶜ'
      (F.map (x ∷_))
      (F.map (x ∷_))
      λ e →
        bind' (λ l → F (Listᵛ X) .charge (length l ⊙ c-lin) (ret l)) .U (F.map (x ∷_) .U e)
      ≡⟨ refl ⟩
        bind' (λ l → F (Listᵛ X) .charge (length l ⊙ c-lin) (ret l)) .U (bind' (ret ∘ (x ∷_)) .U e)
      ≡⟨ bind'-assoc _ _ _ ⟩
        bind' (λ l → 
          bind' (λ l → 
            F (Listᵛ X) .charge (length l ⊙ c-lin) (ret l))
          .U (ret (x ∷ l))) 
        .U e
      ≡⟨ cong (λ h → bind' {A = F (Listᵛ X)} h .U e) (funExt λ _ → bind'/β) ⟩
        bind' (λ l → 
          F (Listᵛ X) .charge (length (x ∷ l) ⊙ c-lin) (ret (x ∷ l))) 
        .U e
      ≡⟨ refl ⟩
        bind' (λ l → 
          F (Listᵛ X) .charge (suc (length l) ⊙ c-lin) (ret (x ∷ l))) 
        .U e
      ≡⟨ refl ⟩
        bind' (λ l → 
          F (Listᵛ X) .charge (c-lin +ℂ (length l ⊙ c-lin)) (ret (x ∷ l))) 
        .U e
      ≡⟨ cong (λ h → bind' {A = F (Listᵛ X)} h .U e) (funExt (λ l → F (Listᵛ X) .charge/+)) ⟩
        bind' (λ l → 
          F (Listᵛ X) .charge c-lin (F (Listᵛ X) .charge (length l ⊙ c-lin) (ret (x ∷ l)))) 
        .U e
      ≡⟨ bind'-charge _ _ _ ⟩
        bind' (λ l → 
          F (Listᵛ X) .charge (length l ⊙ c-lin) (ret (x ∷ l))) 
        .U (F (Listᵛ X) .charge c-lin e)
      ≡⟨ sym
            (cong (λ h → bind' {A = F (Listᵛ X)} h .U (F (Listᵛ X) .charge c-lin e))
              (funExt λ l →
                cong (F (Listᵛ X) .charge (length l ⊙ c-lin)) bind'/β)) ⟩
        bind' (λ l →
          F (Listᵛ X) .charge (length l ⊙ c-lin) (F.map (x ∷_) .U (ret l)))
        .U (F (Listᵛ X) .charge c-lin e)
      ≡⟨ sym
            (cong (λ h → bind' {A = F (Listᵛ X)} h .U (F (Listᵛ X) .charge c-lin e))
              (funExt λ l →
                F.map (x ∷_) .charge (length l ⊙ c-lin) (ret l))) ⟩
        bind' (λ l →
          F.map (x ∷_) .U (F (Listᵛ X) .charge (length l ⊙ c-lin) (ret l)))
        .U (F (Listᵛ X) .charge c-lin e)
      ≡⟨ sym (bind'-assoc _ _ _) ⟩
        F.map (x ∷_) .U
          (bind' (λ l → 
            F (Listᵛ X) .charge (length l ⊙ c-lin) (ret l)) 
          .U (F (Listᵛ X) .charge c-lin e))
      ∎

  pfoldr₁-square
    : ∀ {c-lin A-⊤ A-abs β}
    → (enil-⊤ : cmp A-⊤)
    → (enil-abs : cmp A-abs)
    → β .U enil-⊤ ≡ enil-abs
    → (econs-⊤ : val X → A-⊤ ⊸ A-⊤)
    → (econs-abs : val X → A-abs ⊸ A-abs)
    → ((x : val X) (a : cmp A-⊤)
        → β .U (econs-⊤ x .U a)
          ≡ econs-abs x .U (β .U (A-⊤ .charge c-lin a)))
    → PList₁ c-lin X ⊸ Glueᶜ' A-⊤ A-abs β
  pfoldr₁-square {X = X} {c-lin = c-lin} {A-⊤ = A-⊤} {A-abs = A-abs} {β = β}
    enil-⊤ enil-abs enil-coh econs-⊤ econs-abs econs-coh =
    squareᶜ'
      (bind' go-⊤)
      (bind' go-abs)
      (λ e →
          β .U (bind' go-⊤ .U e)
        ≡⟨ bind'-map {A = A-⊤} {B = A-abs} β go-⊤ e ⟩
          bind' {A = A-abs} (λ l → β .U (go-⊤ l)) .U e
        ≡⟨ cong (λ h → bind' {A = A-abs} h .U e) (funExt go-coh) ⟩
          bind' (λ l →
            A-abs .charge (length l ⊙ c-lin) (go-abs l))
          .U e
        ≡⟨ sym
              (cong (λ h → bind' {A = A-abs} h .U e)
                (funExt λ l →
                  cong (A-abs .charge (length l ⊙ c-lin)) bind'/β)) ⟩
          bind' (λ l →
            A-abs .charge (length l ⊙ c-lin) (bind' go-abs .U (ret l)))
          .U e
        ≡⟨ sym
              (cong (λ h → bind' {A = A-abs} h .U e)
                (funExt λ l →
                  bind' go-abs .charge
                    (length l ⊙ c-lin) (ret l))) ⟩
          bind' (λ l →
            bind' go-abs .U
              (F (Listᵛ X) .charge (length l ⊙ c-lin) (ret l)))
          .U e
        ≡⟨ sym (bind'-assoc _ _ _) ⟩
          bind' go-abs .U
            (bind' (λ l →
              F (Listᵛ X) .charge (length l ⊙ c-lin) (ret l))
            .U e)
        ∎)
    where
      go-⊤ : val (Listᵛ X) → cmp A-⊤
      go-⊤ [] = enil-⊤
      go-⊤ (x ∷ l) = econs-⊤ x .U (go-⊤ l)

      go-abs : val (Listᵛ X) → cmp A-abs
      go-abs [] = enil-abs
      go-abs (x ∷ l) = econs-abs x .U (go-abs l)

      go-coh
        : (l : val (Listᵛ X))
        → β .U (go-⊤ l) ≡ A-abs .charge (length l ⊙ c-lin) (go-abs l)
      go-coh [] = enil-coh ∙ sym (A-abs .charge/0)
      go-coh (x ∷ l) =
          β .U (go-⊤ (x ∷ l))
        ≡⟨ econs-coh x (go-⊤ l) ⟩
          econs-abs x .U (β .U (A-⊤ .charge c-lin (go-⊤ l)))
        ≡⟨ cong (econs-abs x .U) (β .charge c-lin (go-⊤ l)) ⟩
          econs-abs x .U (A-abs .charge c-lin (β .U (go-⊤ l)))
        ≡⟨ cong (econs-abs x .U) (cong (A-abs .charge c-lin) (go-coh l)) ⟩
          econs-abs x .U
            (A-abs .charge c-lin
              (A-abs .charge (length l ⊙ c-lin) (go-abs l)))
        ≡⟨ econs-abs x .charge c-lin (A-abs .charge (length l ⊙ c-lin) (go-abs l)) ⟩
          A-abs .charge c-lin
            (econs-abs x .U
              (A-abs .charge (length l ⊙ c-lin) (go-abs l)))
        ≡⟨ cong (A-abs .charge c-lin) (econs-abs x .charge (length l ⊙ c-lin) (go-abs l)) ⟩
          A-abs .charge c-lin
            (A-abs .charge (length l ⊙ c-lin)
              (econs-abs x .U (go-abs l)))
        ≡⟨ sym (A-abs .charge/+) ⟩
          A-abs .charge (length (x ∷ l) ⊙ c-lin) (go-abs (x ∷ l))
        ∎
 
  pfoldr₁ : ∀ {c-lin}
    → cmp A
    → (val X → (▷'[ c-lin ] A ⊸ A))
    → PList₁ c-lin X ⊸ A
  pfoldr₁ {A = A} {X = X} {c-lin = c-lin} enil econs =
    subst (PList₁ c-lin X ⊸_) Glueᶜ'-id $
    squareᶜ'
      {!   !} {!   !} {!   !}
