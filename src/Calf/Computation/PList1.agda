open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.List

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
      ≡⟨ sym Glueᶜ'-Glueᶜ' ⟩
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
      ≡⟨ cong (λ h → bind' {A = F _} h .U e) (funExt λ _ → bind'/β) ⟩
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
      ≡⟨ cong (λ h → bind' {A = F _} h .U e) (funExt (λ l → F _ .charge/+)) ⟩
        bind' (λ l →
          F _ .charge c (F _ .charge (length l ⊙ c) (ret (x ∷ l))))
        .U e
      ≡⟨ bind'-charge _ _ _ ⟩
        bind' (λ l →
          F _ .charge (length l ⊙ c) (ret (x ∷ l)))
        .U (F _ .charge c e)
      ≡⟨ sym
            (cong (λ h → bind' {A = F _} h .U (F _ .charge c e))
              (funExt λ l →
                cong (F _ .charge (length l ⊙ c)) bind'/β)) ⟩
        bind' (λ l →
          F _ .charge (length l ⊙ c) (F.map (x ∷_) .U (ret l)))
        .U (F _ .charge c e)
      ≡⟨ sym
            (cong (λ h → bind' {A = F _} h .U (F _ .charge c e))
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
        costᶜ : F (Listᵛ X) ⊸ F (Listᵛ X)
        costᶜ =
          bind' {A = F _} λ l →
          CHARGE {A = F _} (length l ⊙ c) .U (ret l)

        fold• : val (Listᵛ X) → cmp (●ᶜ A)
        fold• =
          foldr
            (λ x → ●ᵛ.map (econs x .U) ∘ transport (cong cmp (sym (▷'-●ᶜ c A))))
            (η• enil)

        go• : ●ᶜ (F (Listᵛ X)) ⊸ ●ᶜ A
        go• =
          ●ᶜ.bind $
          bind' fold•

        open-econs : val X → ◯ᶜ A ⊸ ◯ᶜ A
        open-econs x .U a◦ =
          ◯ᵛ.map (econs x .U) (transport (cong cmp (sym (▷'-◯ᶜ c A))) a◦)
        open-econs x .charge d a◦ = funExt λ abs →
            econs x .U
              (transport (cong cmp (sym (▷'-◯ᶜ c A)))
                (◯ᶜ A .charge d a◦)
                abs)
          ≡⟨ cong (λ q → econs x .U (q abs))
                (transport-charge (sym (▷'-◯ᶜ c A)) d a◦) ⟩
            econs x .U
              ((◯ᶜ (▷'[ c ] A) .charge d
                (transport (cong cmp (sym (▷'-◯ᶜ c A))) a◦)) abs)
          ≡⟨ econs x .charge d
                (transport (cong cmp (sym (▷'-◯ᶜ c A))) a◦ abs) ⟩
            A .charge d
              (econs x .U (transport (cong cmp (sym (▷'-◯ᶜ c A))) a◦ abs))
          ∎

        fold◦ : val (Listᵛ X) → cmp (◯ᶜ A)
        fold◦ =
          foldr
            (λ x → open-econs x .U)
            (η◦ enil)

        go◦ : ◯ᶜ (F (Listᵛ X)) ⊸ ◯ᶜ A
        go◦ =
          ◯ᶜ.bind {A = F _} {B = A} $
          bind' fold◦

        fold•ᶜ : F (Listᵛ X) ⊸ ●ᶜ A
        fold•ᶜ = bind' fold•

        go-•⊸◦ :
          go• ⨾ᶜ ●ᶜ.map η◦ᶜ ≡ ●ᶜ.map (costᶜ ⨾ᶜ η◦ᶜ) ⨾ᶜ ●ᶜ.map go◦
        go-•⊸◦ =
            go• ⨾ᶜ ●ᶜ.map η◦ᶜ
          ≡⟨ refl ⟩
            ●ᶜ.bind fold•ᶜ ⨾ᶜ ●ᶜ.map η◦ᶜ
          ≡⟨ ●ᶜ.bind-map _ _ ⟩
            ●ᶜ.bind (fold•ᶜ ⨾ᶜ ●ᶜ.map η◦ᶜ)
          ≡⟨ cong ●ᶜ.bind (bind'-path _ _ (funExt fold•-coherence)) ⟩
            ●ᶜ.bind (costᶜ ⨾ᶜ η◦ᶜ ⨾ᶜ go◦ ⨾ᶜ η•ᶜ)
          ≡⟨ ●ᶜ.bind-η• _ ⟩
            ●ᶜ.map (costᶜ ⨾ᶜ η◦ᶜ ⨾ᶜ go◦)
          ≡⟨ sym (●ᶜ.map-∘ _ _) ⟩
            ●ᶜ.map (costᶜ ⨾ᶜ η◦ᶜ) ⨾ᶜ ●ᶜ.map go◦
          ∎
          where
            cost-cons : ∀ x l →
              CHARGE {A = F _} c .U (F.map (x ∷_) .U (costᶜ .U (ret l)))
              ≡ costᶜ .U (ret (x ∷ l))
            cost-cons x l =
                CHARGE {A = F _} c .U (F.map (x ∷_) .U (costᶜ .U (ret l)))
              ≡⟨ cong (λ e → CHARGE {A = F _} c .U (F.map (x ∷_) .U e)) bind'/β ⟩
                CHARGE {A = F _} c .U
                  (F.map (x ∷_) .U
                    (CHARGE {A = F _} (length l ⊙ c) .U (ret l)))
              ≡⟨ cong (CHARGE {A = F _} c .U)
                    (cong ((_$ ret l) ∘ U)
                      (CHARGE-commute
                        (length l ⊙ c) (F.map (x ∷_)))) ⟩
                CHARGE {A = F _} c .U
                  (CHARGE {A = F _} (length l ⊙ c) .U
                    (F.map (x ∷_) .U (ret l)))
              ≡⟨ cong (λ e → CHARGE {A = F _} c .U (CHARGE {A = F _} (length l ⊙ c) .U e)) bind'/β ⟩
                CHARGE {A = F _} c .U
                  (CHARGE {A = F _} (length l ⊙ c) .U (ret (x ∷ l)))
              ≡⟨ sym (cong ((_$ ret (x ∷ l)) ∘ U) (CHARGE-+ {A = F _} c (length l ⊙ c))) ⟩
                CHARGE {A = F _} (length (x ∷ l) ⊙ c) .U (ret (x ∷ l))
              ≡⟨ sym bind'/β ⟩
                costᶜ .U (ret (x ∷ l))
              ∎

            go◦-cons : ∀ x (e : cmp (F (Listᵛ X))) →
              go◦ .U (η◦ᶜ {A = F _} .U (F.map (x ∷_) .U e))
              ≡ open-econs x .U (go◦ .U (η◦ᶜ {A = F _} .U e))
            go◦-cons x e =
                go◦ .U (η◦ᶜ {A = F _} .U (F.map (x ∷_) .U e))
              ≡⟨ refl ⟩
                bind' fold◦ .U (F.map (x ∷_) .U e)
              ≡⟨ bind'-assoc _ _ _ ⟩
                bind' (λ l →
                  bind' fold◦ .U (ret (x ∷ l)))
                .U e
              ≡⟨ cong (λ h → bind' {A = ◯ᶜ A} h .U e) (funExt λ l → bind'/β) ⟩
                bind' (λ l →
                  open-econs x .U (fold◦ l))
                .U e
              ≡⟨ sym (bind'-map (open-econs x) _ _) ⟩
                open-econs x .U (bind' fold◦ .U e)
              ≡⟨ refl ⟩
                open-econs x .U (go◦ .U (η◦ᶜ {A = F _} .U e))
              ∎

            open-cons-charge : ∀ x l →
              ◯ᵛ.map (econs x .U)
                (transport (cong cmp (sym (▷'-◯ᶜ c A)))
                  (CHARGE {A = ◯ᶜ A} c .U
                    ((costᶜ ⨾ᶜ η◦ᶜ ⨾ᶜ go◦) .U (ret l))))
              ≡ (costᶜ ⨾ᶜ η◦ᶜ ⨾ᶜ go◦) .U (ret (x ∷ l))
            open-cons-charge x l =
              let
                e = costᶜ .U (ret l)
                r = go◦ .U (η◦ᶜ {A = F _} .U e)
              in
                open-econs x .U (CHARGE {A = ◯ᶜ A} c .U r)
              ≡⟨ cong ((_$ r) ∘ U) (CHARGE-commute c (open-econs x)) ⟩
                CHARGE {A = ◯ᶜ A} c .U (open-econs x .U r)
              ≡⟨ cong (CHARGE {A = ◯ᶜ A} c .U) (sym (go◦-cons x e)) ⟩
                CHARGE {A = ◯ᶜ A} c .U
                  (go◦ .U (η◦ᶜ {A = F _} .U (F.map (x ∷_) .U e)))
              ≡⟨ sym (cong ((_$ η◦ᶜ {A = F _} .U (F.map (x ∷_) .U e)) ∘ U)
                    (CHARGE-commute c go◦)) ⟩
                go◦ .U
                  (η◦ᶜ {A = F _} .U
                    (CHARGE {A = F _} c .U (F.map (x ∷_) .U e)))
              ≡⟨ cong (λ e → go◦ .U (η◦ᶜ {A = F _} .U e)) (cost-cons x l) ⟩
                go◦ .U (η◦ᶜ {A = F _} .U (costᶜ .U (ret (x ∷ l))))
              ∎

            fold•-coherence : ∀ l →
              (fold•ᶜ ⨾ᶜ ●ᶜ.map η◦ᶜ) .U (ret l)
              ≡ (costᶜ ⨾ᶜ η◦ᶜ ⨾ᶜ go◦ ⨾ᶜ η•ᶜ) .U (ret l)
            fold•-coherence [] =
                (fold•ᶜ ⨾ᶜ ●ᶜ.map η◦ᶜ) .U (ret [])
              ≡⟨ cong (●ᵛ.map (η◦ᶜ {A = A} .U)) bind'/β ⟩
                η•ᶜ {A = ◯ᶜ A} .U (η◦ᶜ {A = A} .U enil)
              ≡⟨ cong (η•ᶜ {A = ◯ᶜ A} .U) (sym bind'/β) ⟩
                η•ᶜ {A = ◯ᶜ A} .U
                  (bind' fold◦ .U (ret []))
              ≡⟨ refl ⟩
                η•ᶜ {A = ◯ᶜ A} .U
                  (go◦ .U (η◦ᶜ {A = F _} .U (ret [])))
              ≡⟨ cong
                    (λ e → η•ᶜ {A = ◯ᶜ A} .U (go◦ .U (η◦ᶜ {A = F _} .U e)))
                    (sym (cong ((_$ ret []) ∘ U) (CHARGE-0 {A = F _}))) ⟩
                η•ᶜ {A = ◯ᶜ A} .U
                  (go◦ .U (η◦ᶜ {A = F _} .U
                    (CHARGE {A = F _} 0ℂ .U (ret []))))
              ≡⟨ cong
                    (λ e → η•ᶜ {A = ◯ᶜ A} .U
                      (go◦ .U (η◦ᶜ {A = F _} .U e)))
                    (sym bind'/β) ⟩
                η•ᶜ {A = ◯ᶜ A} .U
                  (go◦ .U (η◦ᶜ {A = F _} .U
                    (costᶜ .U (ret []))))
              ≡⟨ refl ⟩
                (costᶜ ⨾ᶜ η◦ᶜ ⨾ᶜ go◦ ⨾ᶜ η•ᶜ) .U (ret [])
              ∎
            fold•-coherence (x ∷ l) =
                (fold•ᶜ ⨾ᶜ ●ᶜ.map η◦ᶜ) .U (ret (x ∷ l))
              ≡⟨ cong (●ᵛ.map (η◦ᶜ {A = A} .U)) bind'/β ⟩
                ●ᵛ.map (η◦ᶜ {A = A} .U)
                  (●ᵛ.map (econs x .U)
                    (transport (cong cmp (sym (▷'-●ᶜ c A)))
                      (fold• l)))
              ≡⟨ cong
                  (λ q → ●ᵛ.map (η◦ᶜ {A = A} .U)
                    (●ᵛ.map (econs x .U)
                      (transport (cong cmp (sym (▷'-●ᶜ c A))) q)))
                  (sym bind'/β) ⟩
                ●ᵛ.map (η◦ᶜ {A = A} .U)
                  (●ᵛ.map (econs x .U)
                    (transport (cong cmp (sym (▷'-●ᶜ c A)))
                      (fold•ᶜ .U (ret l))))
              ≡⟨ (
                let
                    q▷• = transport (cong cmp (sym (▷'-●ᶜ c A))) (fold•ᶜ .U (ret l))
                    q▷◦ = transport (cong cmp (sym (▷'-◯ᶜ c A))) (CHARGE {A = ◯ᶜ A} c .U ((costᶜ ⨾ᶜ η◦ᶜ ⨾ᶜ go◦) .U (ret l)))

                    q▷-coh : ●ᶜ.map (η◦ᶜ {A = ▷'[ c ] A}) .U q▷• ≡ η• q▷◦
                    q▷-coh =
                        ●ᶜ.map (η◦ᶜ {A = ▷'[ c ] A}) .U q▷•
                      ≡⟨ transport-▷' c A (fold•ᶜ .U (ret l)) ⟩
                        transport (cong (λ C → cmp (●ᶜ C)) (sym (▷'-◯ᶜ c A)))
                          ((▷'-FRAC c A .𝒞-FRAC.α•) .U (fold•ᶜ .U (ret l)))
                      ≡⟨ cong
                          (transport (cong (λ C → cmp (●ᶜ C)) (sym (▷'-◯ᶜ c A))))
                          (sym (●ᵛ.map-∘ (η◦ᶜ {A = A} .U) (◯ᶜ A .charge c) (fold•ᶜ .U (ret l))) ) ⟩
                        transport (cong (λ C → cmp (●ᶜ C)) (sym (▷'-◯ᶜ c A)))
                          (●ᵛ.map (CHARGE {A = ◯ᶜ A} c .U)
                            ((fold•ᶜ ⨾ᶜ ●ᶜ.map η◦ᶜ) .U (ret l)))
                      ≡⟨ cong
                          (transport (cong (λ C → cmp (●ᶜ C)) (sym (▷'-◯ᶜ c A))))
                          (cong (●ᵛ.map (CHARGE {A = ◯ᶜ A} c .U)) (fold•-coherence l)) ⟩
                        η• q▷◦
                      ∎
                  in
                  fracture-map-coh (econs x) q▷• q▷◦ q▷-coh
              ) ⟩
                η•ᶜ {A = ◯ᶜ A} .U (◯ᵛ.map (econs x .U)
                  (transport (cong cmp (sym (▷'-◯ᶜ c A)))
                    (CHARGE {A = ◯ᶜ A} c .U ((costᶜ ⨾ᶜ η◦ᶜ ⨾ᶜ go◦) .U (ret l)))))
              ≡⟨ cong (η•ᶜ {A = ◯ᶜ A} .U) (open-cons-charge x l) ⟩
                (costᶜ ⨾ᶜ η◦ᶜ ⨾ᶜ go◦ ⨾ᶜ η•ᶜ) .U (ret (x ∷ l))
              ∎
