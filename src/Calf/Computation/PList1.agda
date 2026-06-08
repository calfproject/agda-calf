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
open import Cubical.Data.List

_⊙_ : ℕ → val ℂ → val ℂ
zero ⊙ c = 0ℂ
suc n ⊙ c = c +ℂ (n ⊙ c)

opaque
  PList₁ : val ℂ → 𝒱 → 𝒞
  PList₁ c X =
    Glueᶜ'
      (F (Listᵛ X))
      (F (Listᵛ X))
      (bind' λ l → F _ .charge (length l ⊙ c) (ret l))

  pnil₁ : cmp (PList₁ c X)
  pnil₁ {c} =
    triangleᶜ'
      {F _} {F _} {bind' (λ l → F _ .charge (length l ⊙ c) (ret l))}
      (ret [])
      (ret [])
      (bind'/β ∙ F _ .charge/0)

  pcons₁ : val X → ▷'[ c ] (PList₁ c X) ⊸ PList₁ c X
  pcons₁ {X} {c} x =
    subst (_⊸ PList₁ c X)
      ( Glueᶜ' (F (Listᵛ X)) (F (Listᵛ X)) (CHARGE c ⨾ᶜ bind' (λ l → F _ .charge (length l ⊙ c) (ret l)))
      ≡⟨ cong (Glueᶜ' _ _) (CHARGE-commute _ _) ⟩
        Glueᶜ' (F (Listᵛ X)) (F (Listᵛ X)) (bind' (λ l → F _ .charge (length l ⊙ c) (ret l)) ⨾ᶜ CHARGE c)
      ≡⟨ {!   !} ⟩
        Glueᶜ'
          (PList₁ c X)
          (PList₁ c X)
          (squareᶜ'
            (CHARGE c)
            (CHARGE c)
            (λ e → bind' (λ l → F _ .charge (length l ⊙ c) (ret l)) .charge c e))
      ≡⟨ cong (Glueᶜ' _ _) (squareᶜ'-charge _) ⟩
        ▷'[ c ] (PList₁ c X)
      ∎) $
    squareᶜ'
      (F.map (x ∷_))
      (F.map (x ∷_))
      λ e →
        bind' (λ l → F _ .charge (length l ⊙ c) (ret l)) .U (F.map (x ∷_) .U e)
      ≡⟨ refl ⟩
        bind' (λ l → F _ .charge (length l ⊙ c) (ret l)) .U (bind' (ret ∘ (x ∷_)) .U e)
      ≡⟨ bind'-assoc _ _ _ ⟩
        bind' (λ l →
          bind' (λ l →
            F _ .charge (length l ⊙ c) (ret l))
          .U (ret (x ∷ l)))
        .U e
      ≡⟨ cong (λ h → bind' {A = F (Listᵛ X)} h .U e) (funExt λ _ → bind'/β) ⟩
        bind' (λ l →
          F _ .charge (length (x ∷ l) ⊙ c) (ret (x ∷ l)))
        .U e
      ≡⟨ refl ⟩
        bind' (λ l →
          F _ .charge (suc (length l) ⊙ c) (ret (x ∷ l)))
        .U e
      ≡⟨ refl ⟩
        bind' (λ l →
          F _ .charge (c +ℂ (length l ⊙ c)) (ret (x ∷ l)))
        .U e
      ≡⟨ cong (λ h → bind' {A = F (Listᵛ X)} h .U e) (funExt (λ l → F _ .charge/+)) ⟩
        bind' (λ l →
          F _ .charge c (F _ .charge (length l ⊙ c) (ret (x ∷ l))))
        .U e
      ≡⟨ bind'-charge _ _ _ ⟩
        bind' (λ l →
          F _ .charge (length l ⊙ c) (ret (x ∷ l)))
        .U (F _ .charge c e)
      ≡⟨ sym
            (cong (λ h → bind' {A = F (Listᵛ X)} h .U (F _ .charge c e))
              (funExt λ l →
                cong (F _ .charge (length l ⊙ c)) bind'/β)) ⟩
        bind' (λ l →
          F _ .charge (length l ⊙ c) (F.map (x ∷_) .U (ret l)))
        .U (F _ .charge c e)
      ≡⟨ sym
            (cong (λ h → bind' {A = F (Listᵛ X)} h .U (F _ .charge c e))
              (funExt λ l →
                F.map (x ∷_) .charge (length l ⊙ c) (ret l))) ⟩
        bind' (λ l →
          F.map (x ∷_) .U (F _ .charge (length l ⊙ c) (ret l)))
        .U (F _ .charge c e)
      ≡⟨ sym (bind'-assoc _ _ _) ⟩
        F.map (x ∷_) .U
          (bind' (λ l →
            F _ .charge (length l ⊙ c) (ret l))
          .U (F _ .charge c e))
      ∎

  pfoldr₁-square
    : ∀ {c A-⊤ A-abs α}
    → (enil-⊤ : cmp A-⊤)
    → (enil-abs : cmp A-abs)
    → α .U enil-⊤ ≡ enil-abs
    → (econs-⊤ : val X → A-⊤ ⊸ A-⊤)
    → (econs-abs : val X → A-abs ⊸ A-abs)
    → ((x : val X) (a : cmp A-⊤)
        → α .U (econs-⊤ x .U a)
          ≡ econs-abs x .U (α .U (A-⊤ .charge c a)))
    → PList₁ c X ⊸ Glueᶜ' A-⊤ A-abs α
  pfoldr₁-square {X = X} {c = c} {A-⊤ = A-⊤} {A-abs = A-abs} {α = α}
    enil-⊤ enil-abs enil-coh econs-⊤ econs-abs econs-coh =
    squareᶜ'
      (bind' go-⊤)
      (bind' go-abs)
      (λ e →
          α .U (bind' go-⊤ .U e)
        ≡⟨ bind'-map {A = A-⊤} {B = A-abs} α go-⊤ e ⟩
          bind' {A = A-abs} (λ l → α .U (go-⊤ l)) .U e
        ≡⟨ cong (λ h → bind' {A = A-abs} h .U e) (funExt go-coh) ⟩
          bind' (λ l →
            A-abs .charge (length l ⊙ c) (go-abs l))
          .U e
        ≡⟨ sym
              (cong (λ h → bind' {A = A-abs} h .U e)
                (funExt λ l →
                  cong (A-abs .charge (length l ⊙ c)) bind'/β)) ⟩
          bind' (λ l →
            A-abs .charge (length l ⊙ c) (bind' go-abs .U (ret l)))
          .U e
        ≡⟨ sym
              (cong (λ h → bind' {A = A-abs} h .U e)
                (funExt λ l →
                  bind' go-abs .charge
                    (length l ⊙ c) (ret l))) ⟩
          bind' (λ l →
            bind' go-abs .U
              (F _ .charge (length l ⊙ c) (ret l)))
          .U e
        ≡⟨ sym (bind'-assoc _ _ _) ⟩
          bind' go-abs .U
            (bind' (λ l →
              F _ .charge (length l ⊙ c) (ret l))
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
        → α .U (go-⊤ l) ≡ A-abs .charge (length l ⊙ c) (go-abs l)
      go-coh [] = enil-coh ∙ sym (A-abs .charge/0)
      go-coh (x ∷ l) =
          α .U (go-⊤ (x ∷ l))
        ≡⟨ econs-coh x (go-⊤ l) ⟩
          econs-abs x .U (α .U (A-⊤ .charge c (go-⊤ l)))
        ≡⟨ cong (econs-abs x .U) (α .charge c (go-⊤ l)) ⟩
          econs-abs x .U (A-abs .charge c (α .U (go-⊤ l)))
        ≡⟨ cong (econs-abs x .U) (cong (A-abs .charge c) (go-coh l)) ⟩
          econs-abs x .U
            (A-abs .charge c
              (A-abs .charge (length l ⊙ c) (go-abs l)))
        ≡⟨ econs-abs x .charge c (A-abs .charge (length l ⊙ c) (go-abs l)) ⟩
          A-abs .charge c
            (econs-abs x .U
              (A-abs .charge (length l ⊙ c) (go-abs l)))
        ≡⟨ cong (A-abs .charge c) (econs-abs x .charge (length l ⊙ c) (go-abs l)) ⟩
          A-abs .charge c
            (A-abs .charge (length l ⊙ c)
              (econs-abs x .U (go-abs l)))
        ≡⟨ sym (A-abs .charge/+) ⟩
          A-abs .charge (length (x ∷ l) ⊙ c) (go-abs (x ∷ l))
        ∎

  opaque
    unfolding Glueᶜ'

    pfoldr₁ :
        cmp A
      → (val X → (▷'[ c ] A ⊸ A))
      → PList₁ c X ⊸ A
    pfoldr₁ {A = A} {X = X} {c} enil econs =
      subst (PList₁ c X ⊸_) (𝒞-glue-fracture-retract A) $
      squareᶜ go• go◦ go-•⊸◦
      where
        lemma• : ●ᶜ (▷'[ c ] A) ≡ ●ᶜ A
        lemma• = cong (fst ∘ 𝒞-FRAC.A•) (𝒞-glue-fracture-section (▷'-FRAC c A))

        go• : ●ᶜ (F (Listᵛ X)) ⊸ ●ᶜ A
        go• =
          ●ᶜ.bind $
          bind' {A = ●ᶜ A} $
          foldr
            (λ x → ●ᵛ.map (econs x .U) ∘ transport (cong cmp (sym lemma•)))
            (η• enil)

        lemma◦ : ◯ᶜ (▷'[ c ] A) ≡ ◯ᶜ A
        lemma◦ = cong (fst ∘ 𝒞-FRAC.A◦) (𝒞-glue-fracture-section (▷'-FRAC c A))

        go◦ : ◯ᶜ (F (Listᵛ X)) ⊸ ◯ᶜ A
        go◦ =
          ◯ᶜ.bind {F _} {A} $
          bind' {A = ◯ᶜ A} $
          foldr
            (λ x → ◯ᵛ.map (econs x .U) ∘ transport (cong cmp (sym lemma◦)))
            (η◦ enil)

        go-•⊸◦ :
          go• ⨾ᶜ ●ᶜ.map (η◦ᶜ {A})
          ≡ ●ᶜ.map (bind' (λ l → F _ .charge (length l ⊙ c) (ret l)) ⨾ᶜ η◦ᶜ {F _}) ⨾ᶜ ●ᶜ.map go◦
        go-•⊸◦ =
            go• ⨾ᶜ ●ᶜ.map (η◦ᶜ {A})
          ≡⟨ refl ⟩
            ●ᶜ.bind (bind' (foldr _ _)) ⨾ᶜ ●ᶜ.map (η◦ᶜ {A})
          ≡⟨ {!   !} ⟩
            ●ᶜ.bind (bind' (foldr (λ x → ●ᵛ.map (econs x .U) ∘ transport (cong cmp (sym lemma•))) (η• enil)) ⨾ᶜ ●ᶜ.map (η◦ᶜ {A}))
          ≡⟨ {!   !} ⟩
            ●ᶜ.bind (bind' (foldr (λ x → ●ᵛ.map (◯ᵛ.map (econs x .U)) ∘ transport (cong (cmp ∘ ●ᶜ) (sym lemma◦))) (η• (η◦ enil))))
          ≡⟨ cong ●ᶜ.bind (bind'-path _ _ (funExt lemma')) ⟩
            ●ᶜ.bind (bind' (λ l → F _ .charge (length l ⊙ c) (ret l)) ⨾ᶜ η◦ᶜ {F _} ⨾ᶜ go◦ ⨾ᶜ η•ᶜ)
          ≡⟨ {!   !} ⟩
            ●ᶜ.map (bind' (λ l → F _ .charge (length l ⊙ c) (ret l)) ⨾ᶜ η◦ᶜ {F _} ⨾ᶜ go◦)
          ≡⟨ sym (●ᶜ.map-∘ _ _) ⟩
            ●ᶜ.map (bind' (λ l → F _ .charge (length l ⊙ c) (ret l)) ⨾ᶜ η◦ᶜ {F _}) ⨾ᶜ ●ᶜ.map go◦
          ∎
          where
            lemma' : ∀ l →
              bind' {X = Listᵛ X} {A = ●ᶜ (◯ᶜ A)} (foldr (λ x → ●ᵛ.map (◯ᵛ.map (econs x .U)) ∘ transport (cong (cmp ∘ ●ᶜ) (sym lemma◦))) (η• (η◦ enil))) .U (ret l)
              ≡ (bind' {X = Listᵛ X} {A = F _} (λ l → F _ .charge (length l ⊙ c) (ret l)) ⨾ᶜ η◦ᶜ {F _} ⨾ᶜ go◦ ⨾ᶜ η•ᶜ) .U (ret l)
            lemma' [] =
                bind' (foldr (λ x → ●ᵛ.map (◯ᵛ.map (econs x .U)) ∘ transport (cong (cmp ∘ ●ᶜ) (sym lemma◦))) (η• (η◦ enil))) .U (ret [])
              ≡⟨ bind'/β ⟩
                foldr (λ x → ●ᵛ.map (◯ᵛ.map (econs x .U)) ∘ transport (cong (cmp ∘ ●ᶜ) (sym lemma◦))) (η• (η◦ enil)) []
              ≡⟨ refl ⟩
                η• (η◦ enil)
              ≡⟨ cong η• (sym bind'/β) ⟩
                η• (bind' (foldr _ _) .U (ret []))
              ≡⟨ refl ⟩
                η• (go◦ .U (η◦ (ret [])))
              ≡⟨ cong (η• ∘ go◦ .U ∘ η◦) (sym (F _ .charge/0)) ⟩
                η• (go◦ .U (η◦ (F _ .charge 0ℂ (ret []))))
              ≡⟨ cong (η• ∘ go◦ .U ∘ η◦) (sym bind'/β) ⟩
                η• (go◦ .U (η◦ (bind' (λ l → F _ .charge (length l ⊙ c) (ret l)) .U (ret []))))
              ≡⟨ refl ⟩
                (bind' (λ l → F _ .charge (length l ⊙ c) (ret l)) ⨾ᶜ η◦ᶜ {F _} ⨾ᶜ go◦ ⨾ᶜ η•ᶜ) .U (ret [])
              ∎
            lemma' (x ∷ l) = {!   !}
