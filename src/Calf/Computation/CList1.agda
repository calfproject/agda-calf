{-# OPTIONS --allow-unsolved-metas #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure

module Calf.Computation.CList1 where

open import Calf.Core.Abstract
open import Calf.Core.Cost
open import Calf.Value
open import Calf.Value.List
open import Calf.Value.Nat
import Calf.Value.Closed as ●
import Calf.Value.Open as ◯
open import Calf.Computation
open import Calf.Computation.Free as F
open import Calf.Computation.Copower
open import Calf.Computation.Open as ◯ᶜ
open import Calf.Computation.Closed as ●ᶜ
open import Calf.Computation.Glue
open import Calf.Computation.Abstraction
open import Calf.Computation.Potential
open import Calf.Computation.Credit

opaque
  CList₁ : ℂ → 𝒱 → 𝒞
  CList₁ c X = ?  -- Potential {List X} (λ l → length l ⊙ c)

  cnil₁ : U (CList₁ c X)
  cnil₁ {c} = ?
    -- triangleᶜ'
    --   {F _} {F _} {bind' (λ l → F _ .charge (length l ⊙ c) (ret l))}
    --   (ret [])
    --   (ret [])
    --   (bind'/β ∙ F _ .charge/0)

  ccons₁ : X → ▷[ c ] (CList₁ c X) ⊸ CList₁ c X
  ccons₁ {X} {c} x = ?
    -- subst (_⊸ CList₁ c X)
    --   ( Abstractionᶜ (F (List X)) (F (List X)) (CHARGE c ⨾ᶜ bind' (λ l → F _ .charge (length l ⊙ c) (ret l)))
    --   ≡⟨ cong (Abstractionᶜ _ _) (CHARGE-commute _ _) ⟩
    --     Abstractionᶜ (F (List X)) (F (List X)) (bind' (λ l → F _ .charge (length l ⊙ c) (ret l)) ⨾ᶜ CHARGE c)
    --   ≡⟨ sym Abstractionᶜ-Abstractionᶜ ⟩
    --     Abstractionᶜ
    --       (CList₁ c X)
    --       (CList₁ c X)
    --       (squareᶜ'
    --         (CHARGE c)
    --         (CHARGE c)
    --         (λ e → bind' (λ l → F _ .charge (length l ⊙ c) (ret l)) .charge c e))
    --   ≡⟨ cong (Abstractionᶜ _ _) (squareᶜ'-charge _) ⟩
    --     ▷[ c ] (CList₁ c X)
    --   ∎) $
    -- squareᶜ'
    --   (F.map (x ∷_))
    --   (F.map (x ∷_))
    --   λ e →
    --     bind' (λ l → F _ .charge (length l ⊙ c) (ret l)) .U (F.map (x ∷_) .U e)
    --   ≡⟨ refl ⟩
    --     bind' (λ l → F _ .charge (length l ⊙ c) (ret l)) .U (bind' (ret ∘ (x ∷_)) .U e)
    --   ≡⟨ bind'-assoc _ _ _ ⟩
    --     bind' (λ l →
    --       bind' (λ l →
    --         F _ .charge (length l ⊙ c) (ret l))
    --       .U (ret (x ∷ l)))
    --     .U e
    --   ≡⟨ cong (λ h → bind' {A = F _} h .U e) (funExt λ _ → bind'/β) ⟩
    --     bind' (λ l →
    --       F _ .charge (length (x ∷ l) ⊙ c) (ret (x ∷ l)))
    --     .U e
    --   ≡⟨ refl ⟩
    --     bind' (λ l →
    --       F _ .charge (suc (length l) ⊙ c) (ret (x ∷ l)))
    --     .U e
    --   ≡⟨ refl ⟩
    --     bind' (λ l →
    --       F _ .charge (c +ℂ (length l ⊙ c)) (ret (x ∷ l)))
    --     .U e
    --   ≡⟨ cong (λ h → bind' {A = F _} h .U e) (funExt (λ l → F _ .charge/+)) ⟩
    --     bind' (λ l →
    --       F _ .charge c (F _ .charge (length l ⊙ c) (ret (x ∷ l))))
    --     .U e
    --   ≡⟨ bind'-charge _ _ _ ⟩
    --     bind' (λ l →
    --       F _ .charge (length l ⊙ c) (ret (x ∷ l)))
    --     .U (F _ .charge c e)
    --   ≡⟨ sym
    --         (cong (λ h → bind' {A = F _} h .U (F _ .charge c e))
    --           (funExt λ l →
    --             cong (F _ .charge (length l ⊙ c)) bind'/β)) ⟩
    --     bind' (λ l →
    --       F _ .charge (length l ⊙ c) (F.map (x ∷_) .U (ret l)))
    --     .U (F _ .charge c e)
    --   ≡⟨ sym
    --         (cong (λ h → bind' {A = F _} h .U (F _ .charge c e))
    --           (funExt λ l →
    --             F.map (x ∷_) .charge (length l ⊙ c) (ret l))) ⟩
    --     bind' (λ l →
    --       F.map (x ∷_) .U (F _ .charge (length l ⊙ c) (ret l)))
    --     .U (F _ .charge c e)
    --   ≡⟨ sym (bind'-assoc _ _ _) ⟩
    --     F.map (x ∷_) .U
    --       (bind' (λ l →
    --         F _ .charge (length l ⊙ c) (ret l))
    --       .U (F _ .charge c e))
    --   ∎

  cfoldr₁ :
      U A
    → (X → (▷[ c ] A ⊸ A))
    → CList₁ c X ⊸ A
  cfoldr₁ {A = A} {X = X} {c} enil econs = ?
    -- subst (CList₁ c X ⊸_) (𝒞-glue-fracture-retract A) $
    -- squareᶜ go• go◦ go-•⊸◦
    -- where
    --   costᶜ : F (List X) ⊸ F (List X)
    --   costᶜ =
    --     bind' {A = F _} λ l →
    --     CHARGE {A = F _} (length l ⊙ c) .U (ret l)

    --   fold• : (List X) → U (●ᶜ A)
    --   fold• =
    --     foldr
    --       (λ x → ●.map (econs x .U) ∘ transport (cong U (sym (▷-●ᶜ c A))))
    --       (η• enil)

    --   go• : ●ᶜ (F (List X)) ⊸ ●ᶜ A
    --   go• =
    --     ●ᶜ.bind $
    --     bind' fold•

    --   open-econs : X → ◯ᶜ A ⊸ ◯ᶜ A
    --   open-econs x .U a◦ =
    --     ◯.map (econs x .U) (transport (cong U (sym (▷-◯ᶜ c A))) a◦)
    --   open-econs x .charge d a◦ = funExt λ abs →
    --       econs x .U
    --         (transport (cong U (sym (▷-◯ᶜ c A)))
    --           (◯ᶜ A .charge d a◦)
    --           abs)
    --     ≡⟨ cong (λ q → econs x .U (q abs))
    --           (transport-charge (sym (▷-◯ᶜ c A)) d a◦) ⟩
    --       econs x .U
    --         ((◯ᶜ (▷[ c ] A) .charge d
    --           (transport (cong U (sym (▷-◯ᶜ c A))) a◦)) abs)
    --     ≡⟨ econs x .charge d
    --           (transport (cong U (sym (▷-◯ᶜ c A))) a◦ abs) ⟩
    --       A .charge d
    --         (econs x .U (transport (cong U (sym (▷-◯ᶜ c A))) a◦ abs))
    --     ∎

    --   fold◦ : (List X) → U (◯ᶜ A)
    --   fold◦ =
    --     foldr
    --       (λ x → open-econs x .U)
    --       (η◦ enil)

    --   go◦ : ◯ᶜ (F (List X)) ⊸ ◯ᶜ A
    --   go◦ =
    --     ◯ᶜ.bind {A = F _} {B = A} $
    --     bind' fold◦

    --   fold•ᶜ : F (List X) ⊸ ●ᶜ A
    --   fold•ᶜ = bind' fold•

    --   go-•⊸◦ :
    --     go• ⨾ᶜ ●ᶜ.map η◦ᶜ ≡ ●ᶜ.map (costᶜ ⨾ᶜ η◦ᶜ) ⨾ᶜ ●ᶜ.map go◦
    --   go-•⊸◦ =
    --       go• ⨾ᶜ ●ᶜ.map η◦ᶜ
    --     ≡⟨ refl ⟩
    --       ●ᶜ.bind fold•ᶜ ⨾ᶜ ●ᶜ.map η◦ᶜ
    --     ≡⟨ ●ᶜ.bind-map _ _ ⟩
    --       ●ᶜ.bind (fold•ᶜ ⨾ᶜ ●ᶜ.map η◦ᶜ)
    --     ≡⟨ cong ●ᶜ.bind (bind'-path _ _ (funExt fold•-coherence)) ⟩
    --       ●ᶜ.bind (costᶜ ⨾ᶜ η◦ᶜ ⨾ᶜ go◦ ⨾ᶜ η•ᶜ)
    --     ≡⟨ ●ᶜ.bind-η• _ ⟩
    --       ●ᶜ.map (costᶜ ⨾ᶜ η◦ᶜ ⨾ᶜ go◦)
    --     ≡⟨ sym (●ᶜ.map-∘ _ _) ⟩
    --       ●ᶜ.map (costᶜ ⨾ᶜ η◦ᶜ) ⨾ᶜ ●ᶜ.map go◦
    --     ∎
    --     where
    --       cost-cons : ∀ x l →
    --         CHARGE {A = F _} c .U (F.map (x ∷_) .U (costᶜ .U (ret l)))
    --         ≡ costᶜ .U (ret (x ∷ l))
    --       cost-cons x l =
    --           CHARGE {A = F _} c .U (F.map (x ∷_) .U (costᶜ .U (ret l)))
    --         ≡⟨ cong (λ e → CHARGE {A = F _} c .U (F.map (x ∷_) .U e)) bind'/β ⟩
    --           CHARGE {A = F _} c .U
    --             (F.map (x ∷_) .U
    --               (CHARGE {A = F _} (length l ⊙ c) .U (ret l)))
    --         ≡⟨ cong (CHARGE {A = F _} c .U)
    --               (cong ((_$ ret l) ∘ U)
    --                 (CHARGE-commute
    --                   (length l ⊙ c) (F.map (x ∷_)))) ⟩
    --           CHARGE {A = F _} c .U
    --             (CHARGE {A = F _} (length l ⊙ c) .U
    --               (F.map (x ∷_) .U (ret l)))
    --         ≡⟨ cong (λ e → CHARGE {A = F _} c .U (CHARGE {A = F _} (length l ⊙ c) .U e)) bind'/β ⟩
    --           CHARGE {A = F _} c .U
    --             (CHARGE {A = F _} (length l ⊙ c) .U (ret (x ∷ l)))
    --         ≡⟨ sym (cong ((_$ ret (x ∷ l)) ∘ U) (CHARGE-+ {A = F _} c (length l ⊙ c))) ⟩
    --           CHARGE {A = F _} (length (x ∷ l) ⊙ c) .U (ret (x ∷ l))
    --         ≡⟨ sym bind'/β ⟩
    --           costᶜ .U (ret (x ∷ l))
    --         ∎

    --       go◦-cons : ∀ x (e : U (F (List X))) →
    --         go◦ .U (η◦ᶜ {A = F _} .U (F.map (x ∷_) .U e))
    --         ≡ open-econs x .U (go◦ .U (η◦ᶜ {A = F _} .U e))
    --       go◦-cons x e =
    --           go◦ .U (η◦ᶜ {A = F _} .U (F.map (x ∷_) .U e))
    --         ≡⟨ refl ⟩
    --           bind' fold◦ .U (F.map (x ∷_) .U e)
    --         ≡⟨ bind'-assoc _ _ _ ⟩
    --           bind' (λ l →
    --             bind' fold◦ .U (ret (x ∷ l)))
    --           .U e
    --         ≡⟨ cong (λ h → bind' {A = ◯ᶜ A} h .U e) (funExt λ l → bind'/β) ⟩
    --           bind' (λ l →
    --             open-econs x .U (fold◦ l))
    --           .U e
    --         ≡⟨ sym (bind'-map (open-econs x) _ _) ⟩
    --           open-econs x .U (bind' fold◦ .U e)
    --         ≡⟨ refl ⟩
    --           open-econs x .U (go◦ .U (η◦ᶜ {A = F _} .U e))
    --         ∎

    --       open-cons-charge : ∀ x l →
    --         ◯.map (econs x .U)
    --           (transport (cong U (sym (▷-◯ᶜ c A)))
    --             (CHARGE {A = ◯ᶜ A} c .U
    --               ((costᶜ ⨾ᶜ η◦ᶜ ⨾ᶜ go◦) .U (ret l))))
    --         ≡ (costᶜ ⨾ᶜ η◦ᶜ ⨾ᶜ go◦) .U (ret (x ∷ l))
    --       open-cons-charge x l =
    --         let
    --           e = costᶜ .U (ret l)
    --           r = go◦ .U (η◦ᶜ {A = F _} .U e)
    --         in
    --           open-econs x .U (CHARGE {A = ◯ᶜ A} c .U r)
    --         ≡⟨ cong ((_$ r) ∘ U) (CHARGE-commute c (open-econs x)) ⟩
    --           CHARGE {A = ◯ᶜ A} c .U (open-econs x .U r)
    --         ≡⟨ cong (CHARGE {A = ◯ᶜ A} c .U) (sym (go◦-cons x e)) ⟩
    --           CHARGE {A = ◯ᶜ A} c .U
    --             (go◦ .U (η◦ᶜ {A = F _} .U (F.map (x ∷_) .U e)))
    --         ≡⟨ sym (cong ((_$ η◦ᶜ {A = F _} .U (F.map (x ∷_) .U e)) ∘ U)
    --               (CHARGE-commute c go◦)) ⟩
    --           go◦ .U
    --             (η◦ᶜ {A = F _} .U
    --               (CHARGE {A = F _} c .U (F.map (x ∷_) .U e)))
    --         ≡⟨ cong (λ e → go◦ .U (η◦ᶜ {A = F _} .U e)) (cost-cons x l) ⟩
    --           go◦ .U (η◦ᶜ {A = F _} .U (costᶜ .U (ret (x ∷ l))))
    --         ∎

    --       fold•-coherence : ∀ l →
    --         (fold•ᶜ ⨾ᶜ ●ᶜ.map η◦ᶜ) .U (ret l)
    --         ≡ (costᶜ ⨾ᶜ η◦ᶜ ⨾ᶜ go◦ ⨾ᶜ η•ᶜ) .U (ret l)
    --       fold•-coherence [] =
    --           (fold•ᶜ ⨾ᶜ ●ᶜ.map η◦ᶜ) .U (ret [])
    --         ≡⟨ cong (●.map (η◦ᶜ {A = A} .U)) bind'/β ⟩
    --           η•ᶜ {A = ◯ᶜ A} .U (η◦ᶜ {A = A} .U enil)
    --         ≡⟨ cong (η•ᶜ {A = ◯ᶜ A} .U) (sym bind'/β) ⟩
    --           η•ᶜ {A = ◯ᶜ A} .U
    --             (bind' fold◦ .U (ret []))
    --         ≡⟨ refl ⟩
    --           η•ᶜ {A = ◯ᶜ A} .U
    --             (go◦ .U (η◦ᶜ {A = F _} .U (ret [])))
    --         ≡⟨ cong
    --               (λ e → η•ᶜ {A = ◯ᶜ A} .U (go◦ .U (η◦ᶜ {A = F _} .U e)))
    --               (sym (cong ((_$ ret []) ∘ U) (CHARGE-0 {A = F _}))) ⟩
    --           η•ᶜ {A = ◯ᶜ A} .U
    --             (go◦ .U (η◦ᶜ {A = F _} .U
    --               (CHARGE {A = F _} 0ℂ .U (ret []))))
    --         ≡⟨ cong
    --               (λ e → η•ᶜ {A = ◯ᶜ A} .U
    --                 (go◦ .U (η◦ᶜ {A = F _} .U e)))
    --               (sym bind'/β) ⟩
    --           η•ᶜ {A = ◯ᶜ A} .U
    --             (go◦ .U (η◦ᶜ {A = F _} .U
    --               (costᶜ .U (ret []))))
    --         ≡⟨ refl ⟩
    --           (costᶜ ⨾ᶜ η◦ᶜ ⨾ᶜ go◦ ⨾ᶜ η•ᶜ) .U (ret [])
    --         ∎
    --       fold•-coherence (x ∷ l) =
    --           (fold•ᶜ ⨾ᶜ ●ᶜ.map η◦ᶜ) .U (ret (x ∷ l))
    --         ≡⟨ cong (●.map (η◦ᶜ {A = A} .U)) bind'/β ⟩
    --           ●.map (η◦ᶜ {A = A} .U)
    --             (●.map (econs x .U)
    --               (transport (cong U (sym (▷-●ᶜ c A)))
    --                 (fold• l)))
    --         ≡⟨ cong
    --             (λ q → ●.map (η◦ᶜ {A = A} .U)
    --               (●.map (econs x .U)
    --                 (transport (cong U (sym (▷-●ᶜ c A))) q)))
    --             (sym bind'/β) ⟩
    --           ●.map (η◦ᶜ {A = A} .U)
    --             (●.map (econs x .U)
    --               (transport (cong U (sym (▷-●ᶜ c A)))
    --                 (fold•ᶜ .U (ret l))))
    --         ≡⟨ (
    --           let
    --               q▷• = transport (cong U (sym (▷-●ᶜ c A))) (fold•ᶜ .U (ret l))
    --               q▷◦ = transport (cong U (sym (▷-◯ᶜ c A))) (CHARGE {A = ◯ᶜ A} c .U ((costᶜ ⨾ᶜ η◦ᶜ ⨾ᶜ go◦) .U (ret l)))

    --               q▷-coh : ●ᶜ.map (η◦ᶜ {A = ▷[ c ] A}) .U q▷• ≡ η• q▷◦
    --               q▷-coh =
    --                   ●ᶜ.map (η◦ᶜ {A = ▷[ c ] A}) .U q▷•
    --                 ≡⟨ ? ⟩  -- transport-▷ c A (fold•ᶜ .U (ret l)) ⟩
    --                   transport (cong (λ C → U (●ᶜ C)) (sym (▷-◯ᶜ c A)))
    --                     ((▷-FRAC c A .𝒞-FRACTURE.α•) .U (fold•ᶜ .U (ret l)))
    --                 ≡⟨ cong
    --                     (transport (cong (λ C → U (●ᶜ C)) (sym (▷-◯ᶜ c A))))
    --                     (sym (●.map-∘ (η◦ᶜ {A = A} .U) (◯ᶜ A .charge c) (fold•ᶜ .U (ret l))) ) ⟩
    --                   transport (cong (λ C → U (●ᶜ C)) (sym (▷-◯ᶜ c A)))
    --                     (●.map (CHARGE {A = ◯ᶜ A} c .U)
    --                       ((fold•ᶜ ⨾ᶜ ●ᶜ.map η◦ᶜ) .U (ret l)))
    --                 ≡⟨ cong
    --                     (transport (cong (λ C → U (●ᶜ C)) (sym (▷-◯ᶜ c A))))
    --                     (cong (●.map (CHARGE {A = ◯ᶜ A} c .U)) (fold•-coherence l)) ⟩
    --                   η• q▷◦
    --                 ∎
    --             in
    --             fracture-map-coh (econs x) q▷• q▷◦ q▷-coh
    --         ) ⟩
    --           η•ᶜ {A = ◯ᶜ A} .U (◯.map (econs x .U)
    --             (transport (cong U (sym (▷-◯ᶜ c A)))
    --               (CHARGE {A = ◯ᶜ A} c .U ((costᶜ ⨾ᶜ η◦ᶜ ⨾ᶜ go◦) .U (ret l)))))
    --         ≡⟨ cong (η•ᶜ {A = ◯ᶜ A} .U) (open-cons-charge x l) ⟩
    --           (costᶜ ⨾ᶜ η◦ᶜ ⨾ᶜ go◦ ⨾ᶜ η•ᶜ) .U (ret (x ∷ l))
    --         ∎
