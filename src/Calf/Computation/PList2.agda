open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Univalence using (ua)
open import Cubical.Data.Equality.Conversion using (eqToPath)
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.List

module Calf.Computation.PList2 where

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
open import Calf.Computation.Credit

binom2 : ℕ → ℕ
binom2 zero = zero
binom2 (suc n) = n + binom2 n

plist₂-potential : val ℂ → val ℂ → ℕ → val ℂ
plist₂-potential c-linear c-quadratic n =
  (n ⊙ c-linear) +ℂ (binom2 n ⊙ c-quadratic)

module _ where
  plist₂-potential-suc
    : ∀ n c-linear c-quadratic
    → plist₂-potential c-linear c-quadratic (suc n)
      ≡ c-linear +ℂ plist₂-potential (c-quadratic +ℂ c-linear) c-quadratic n
  plist₂-potential-suc n c-linear c-quadratic =
      plist₂-potential c-linear c-quadratic (suc n)
    ≡⟨ refl ⟩
      (c-linear +ℂ (n ⊙ c-linear))
        +ℂ ((n + binom2 n) ⊙ c-quadratic)
    ≡⟨ cong
        ((c-linear +ℂ (n ⊙ c-linear)) +ℂ_)
        (⊙-+-left n (binom2 n) c-quadratic) ⟩
      (c-linear +ℂ (n ⊙ c-linear))
        +ℂ ((n ⊙ c-quadratic) +ℂ (binom2 n ⊙ c-quadratic))
    ≡⟨ +ℂ-assoc c-linear (n ⊙ c-linear)
        ((n ⊙ c-quadratic) +ℂ (binom2 n ⊙ c-quadratic)) ⟩
      c-linear +ℂ
        ((n ⊙ c-linear)
          +ℂ ((n ⊙ c-quadratic) +ℂ (binom2 n ⊙ c-quadratic)))
    ≡⟨ cong (c-linear +ℂ_)
        (sym (+ℂ-assoc (n ⊙ c-linear) (n ⊙ c-quadratic) (binom2 n ⊙ c-quadratic))) ⟩
      c-linear +ℂ
        (((n ⊙ c-linear) +ℂ (n ⊙ c-quadratic))
          +ℂ (binom2 n ⊙ c-quadratic))
    ≡⟨ cong
        (λ c → c-linear +ℂ (c +ℂ (binom2 n ⊙ c-quadratic)))
        (+ℂ-comm (n ⊙ c-linear) (n ⊙ c-quadratic)) ⟩
      c-linear +ℂ
        (((n ⊙ c-quadratic) +ℂ (n ⊙ c-linear))
          +ℂ (binom2 n ⊙ c-quadratic))
    ≡⟨ cong (c-linear +ℂ_)
        (cong (_+ℂ (binom2 n ⊙ c-quadratic))
          (sym (⊙-+ n c-quadratic c-linear))) ⟩
      c-linear +ℂ plist₂-potential (c-quadratic +ℂ c-linear) c-quadratic n
    ∎

opaque
  PList₂ : val ℂ → val ℂ → 𝒱 → 𝒞
  PList₂ c-linear c-quadratic X =
    PotentialFunction {Listᵛ X} (plist₂-potential c-linear c-quadratic ∘ length)

  pnil₂ : ∀ {c-lin c-quad} → cmp (PList₂ c-lin c-quad X)
  pnil₂ {X} {c-lin} {c-quad} =
    triangleᶜ'
      (ret [])
      (ret [])
      $
        bind' (λ l → F _ .charge (plist₂-potential c-lin c-quad (length l)) (ret l)) .U (ret [])
      ≡⟨ bind'/β ⟩
        F _ .charge (0ℂ +ℂ 0ℂ) (ret [])
      ≡⟨ cong (λ c → F _ .charge c (ret [])) (+ℂ-identityˡ 0ℂ) ⟩
        F _ .charge 0ℂ (ret [])
      ≡⟨ F _ .charge/0 ⟩
        ret []
      ∎

  pcons₂ : ∀ {c-lin c-quad} → val X → ▷'[ c-lin ] (PList₂ (c-quad +ℂ c-lin) c-quad X) ⊸ PList₂ c-lin c-quad X
  pcons₂ {X} {c-lin} {c-quad} x =
    subst (_⊸ PList₂ c-lin c-quad X)
      ( Glueᶜ' (F (Listᵛ X)) (F (Listᵛ X))
          (CHARGE c-lin ⨾ᶜ bind' (λ l → F _ .charge (plist₂-potential (c-quad +ℂ c-lin) c-quad (length l)) (ret l)))
      ≡⟨ cong (Glueᶜ' _ _) (CHARGE-commute _ _) ⟩
        Glueᶜ' (F (Listᵛ X)) (F (Listᵛ X))
          (bind' (λ l → F _ .charge (plist₂-potential (c-quad +ℂ c-lin) c-quad (length l)) (ret l)) ⨾ᶜ CHARGE c-lin)
      ≡⟨ sym Glueᶜ'-Glueᶜ' ⟩
        Glueᶜ'
          (PList₂ (c-quad +ℂ c-lin) c-quad X)
          (PList₂ (c-quad +ℂ c-lin) c-quad X)
          (squareᶜ'
            (CHARGE c-lin)
            (CHARGE c-lin)
            (λ e → bind' (λ l → F _ .charge (plist₂-potential (c-quad +ℂ c-lin) c-quad (length l)) (ret l)) .charge c-lin e))
      ≡⟨ cong (Glueᶜ' _ _) (squareᶜ'-charge _) ⟩
        ▷'[ c-lin ] (PList₂ (c-quad +ℂ c-lin) c-quad X)
      ∎) $
    squareᶜ'
      (F.map (x ∷_))
      (F.map (x ∷_))
      λ e →
        bind' (λ l → F (Listᵛ X) .charge (plist₂-potential c-lin c-quad (length l)) (ret l)) .U (F.map (x ∷_) .U e)
      ≡⟨ refl ⟩
        bind' (λ l → F (Listᵛ X) .charge (plist₂-potential c-lin c-quad (length l)) (ret l)) .U (bind' (ret ∘ (x ∷_)) .U e)
      ≡⟨ bind'-assoc _ _ _ ⟩
        bind' (λ l →
          bind' (λ l →
            F (Listᵛ X) .charge (plist₂-potential c-lin c-quad (length l)) (ret l))
          .U (ret (x ∷ l)))
        .U e
      ≡⟨ cong (λ h → bind' {A = F (Listᵛ X)} h .U e) (funExt λ _ → bind'/β) ⟩
        bind' (λ l →
          F (Listᵛ X) .charge (plist₂-potential c-lin c-quad (length (x ∷ l))) (ret (x ∷ l)))
        .U e
      ≡⟨ cong (λ h → bind' {A = F (Listᵛ X)} h .U e)
            (funExt λ l →
              cong (λ c → F (Listᵛ X) .charge c (ret (x ∷ l)))
                (plist₂-potential-suc (length l) c-lin c-quad)) ⟩
        bind' (λ l →
          F (Listᵛ X) .charge
            (c-lin +ℂ plist₂-potential (c-quad +ℂ c-lin) c-quad (length l))
            (ret (x ∷ l)))
        .U e
      ≡⟨ cong (λ h → bind' {A = F (Listᵛ X)} h .U e) (funExt λ l → F (Listᵛ X) .charge/+) ⟩
        bind' (λ l →
          F (Listᵛ X) .charge c-lin
            (F (Listᵛ X) .charge
              (plist₂-potential (c-quad +ℂ c-lin) c-quad (length l))
              (ret (x ∷ l))))
        .U e
      ≡⟨ bind'-charge _ _ _ ⟩
        bind' (λ l →
          F (Listᵛ X) .charge
            (plist₂-potential (c-quad +ℂ c-lin) c-quad (length l))
            (ret (x ∷ l)))
        .U (F (Listᵛ X) .charge c-lin e)
      ≡⟨ sym
            (cong (λ h → bind' {A = F (Listᵛ X)} h .U (F (Listᵛ X) .charge c-lin e))
              (funExt λ l →
                cong (F (Listᵛ X) .charge (plist₂-potential (c-quad +ℂ c-lin) c-quad (length l))) bind'/β)) ⟩
        bind' (λ l →
          F (Listᵛ X) .charge
            (plist₂-potential (c-quad +ℂ c-lin) c-quad (length l))
            (F.map (x ∷_) .U (ret l)))
        .U (F (Listᵛ X) .charge c-lin e)
      ≡⟨ sym
            (cong (λ h → bind' {A = F (Listᵛ X)} h .U (F (Listᵛ X) .charge c-lin e))
              (funExt λ l →
                F.map (x ∷_) .charge (plist₂-potential (c-quad +ℂ c-lin) c-quad (length l)) (ret l))) ⟩
        bind' (λ l →
          F.map (x ∷_) .U
            (F (Listᵛ X) .charge (plist₂-potential (c-quad +ℂ c-lin) c-quad (length l)) (ret l)))
        .U (F (Listᵛ X) .charge c-lin e)
      ≡⟨ sym (bind'-assoc _ _ _) ⟩
        F.map (x ∷_) .U
          (bind' (λ l →
            F (Listᵛ X) .charge (plist₂-potential (c-quad +ℂ c-lin) c-quad (length l)) (ret l))
          .U (F (Listᵛ X) .charge c-lin e))
      ∎

  opaque
    unfolding Glueᶜ'

    pfoldr₂ : ∀ {c-lin c-quad} (A : val ℂ → 𝒞)
      → (∀ c-lin → cmp (A c-lin))
      → (∀ c-lin → val X → (▷'[ c-lin ] (A (c-quad +ℂ c-lin))) ⊸ A c-lin)
      → PList₂ c-lin c-quad X ⊸ A c-lin
    pfoldr₂ {X = X} {c-lin = c-lin} {c-quad = c-quad} A e-nil e-cons =
      subst (PList₂ c-lin c-quad X ⊸_) (𝒞-glue-fracture-retract (A c-lin)) $
      squareᶜ (go• c-lin) (go◦ c-lin) go-•⊸◦
      where
        costᶜ-at : val ℂ → F (Listᵛ X) ⊸ F (Listᵛ X)
        costᶜ-at c =
          bind' {A = F _} λ l →
          CHARGE {A = F _} (plist₂-potential c c-quad (length l)) .U (ret l)

        costᶜ : F (Listᵛ X) ⊸ F (Listᵛ X)
        costᶜ = costᶜ-at c-lin

        fold• : val (Listᵛ X) → (c : val ℂ) → cmp (●ᶜ (A c))
        fold• =
          foldr
            (λ x rec c →
              ●ᵛ.map (e-cons c x .U)
                (transport
                  (cong cmp (sym (▷'-●ᶜ c (A (c-quad +ℂ c)))))
                  (rec (c-quad +ℂ c))))
            (λ c → η• (e-nil c))

        go• : (c : val ℂ) → ●ᶜ (F (Listᵛ X)) ⊸ ●ᶜ (A c)
        go• c =
          ●ᶜ.bind $
          bind' (λ l → fold• l c)

        open-econs : (c : val ℂ) → val X → ◯ᶜ (A (c-quad +ℂ c)) ⊸ ◯ᶜ (A c)
        open-econs c x .U a◦ =
          ◯ᵛ.map (e-cons c x .U)
            (transport (cong cmp (sym (▷'-◯ᶜ c (A (c-quad +ℂ c))))) a◦)
        open-econs c x .charge d a◦ = funExt λ abs →
            e-cons c x .U
              (transport (cong cmp (sym (▷'-◯ᶜ c (A (c-quad +ℂ c)))))
                (◯ᶜ (A (c-quad +ℂ c)) .charge d a◦)
                abs)
          ≡⟨ cong (λ q → e-cons c x .U (q abs))
                (transport-charge (sym (▷'-◯ᶜ c (A (c-quad +ℂ c)))) d a◦) ⟩
            e-cons c x .U
              ((◯ᶜ (▷'[ c ] (A (c-quad +ℂ c))) .charge d
                (transport (cong cmp (sym (▷'-◯ᶜ c (A (c-quad +ℂ c))))) a◦)) abs)
          ≡⟨ e-cons c x .charge d
                (transport (cong cmp (sym (▷'-◯ᶜ c (A (c-quad +ℂ c))))) a◦ abs) ⟩
            A c .charge d
              (e-cons c x .U
                (transport (cong cmp (sym (▷'-◯ᶜ c (A (c-quad +ℂ c))))) a◦ abs))
          ∎

        fold◦ : val (Listᵛ X) → (c : val ℂ) → cmp (◯ᶜ (A c))
        fold◦ =
          foldr
            (λ x rec c → open-econs c x .U (rec (c-quad +ℂ c)))
            (λ c → η◦ (e-nil c))

        go◦ : (c : val ℂ) → ◯ᶜ (F (Listᵛ X)) ⊸ ◯ᶜ (A c)
        go◦ c =
          ◯ᶜ.bind {A = F _} {B = A c} $
          bind' (λ l → fold◦ l c)

        fold•ᶜ : (c : val ℂ) → F (Listᵛ X) ⊸ ●ᶜ (A c)
        fold•ᶜ c = bind' (λ l → fold• l c)

        go-•⊸◦ :
          go• c-lin ⨾ᶜ ●ᶜ.map η◦ᶜ ≡ ●ᶜ.map (costᶜ ⨾ᶜ η◦ᶜ) ⨾ᶜ ●ᶜ.map (go◦ c-lin)
        go-•⊸◦ =
            go• c-lin ⨾ᶜ ●ᶜ.map η◦ᶜ
          ≡⟨ refl ⟩
            ●ᶜ.bind (fold•ᶜ c-lin) ⨾ᶜ ●ᶜ.map η◦ᶜ
          ≡⟨ ●ᶜ.bind-map _ _ ⟩
            ●ᶜ.bind (fold•ᶜ c-lin ⨾ᶜ ●ᶜ.map η◦ᶜ)
          ≡⟨ cong ●ᶜ.bind (bind'-path _ _ (funExt (fold•-coherence c-lin))) ⟩
            ●ᶜ.bind (costᶜ ⨾ᶜ η◦ᶜ ⨾ᶜ go◦ c-lin ⨾ᶜ η•ᶜ)
          ≡⟨ ●ᶜ.bind-η• _ ⟩
            ●ᶜ.map (costᶜ ⨾ᶜ η◦ᶜ ⨾ᶜ go◦ c-lin)
          ≡⟨ sym (●ᶜ.map-∘ _ _) ⟩
            ●ᶜ.map (costᶜ ⨾ᶜ η◦ᶜ) ⨾ᶜ ●ᶜ.map (go◦ c-lin)
          ∎
          where
            cost-nil : ∀ c → costᶜ-at c .U (ret []) ≡ ret []
            cost-nil c =
                costᶜ-at c .U (ret [])
              ≡⟨ bind'/β ⟩
                F (Listᵛ X) .charge (0ℂ +ℂ 0ℂ) (ret [])
              ≡⟨ cong (λ c → F (Listᵛ X) .charge c (ret [])) (+ℂ-identityˡ 0ℂ) ⟩
                F (Listᵛ X) .charge 0ℂ (ret [])
              ≡⟨ F (Listᵛ X) .charge/0 ⟩
                ret []
              ∎

            cost-cons : ∀ c x l →
              CHARGE {A = F _} c .U
                (F.map (x ∷_) .U (costᶜ-at (c-quad +ℂ c) .U (ret l)))
              ≡ costᶜ-at c .U (ret (x ∷ l))
            cost-cons c x l =
                CHARGE {A = F _} c .U
                  (F.map (x ∷_) .U (costᶜ-at (c-quad +ℂ c) .U (ret l)))
              ≡⟨ cong (λ e → CHARGE {A = F _} c .U (F.map (x ∷_) .U e)) bind'/β ⟩
                CHARGE {A = F _} c .U
                  (F.map (x ∷_) .U
                    (CHARGE {A = F _} (plist₂-potential (c-quad +ℂ c) c-quad (length l)) .U (ret l)))
              ≡⟨ cong (CHARGE {A = F _} c .U)
                    (cong ((_$ ret l) ∘ U)
                      (CHARGE-commute
                        (plist₂-potential (c-quad +ℂ c) c-quad (length l))
                        (F.map (x ∷_)))) ⟩
                CHARGE {A = F _} c .U
                  (CHARGE {A = F _} (plist₂-potential (c-quad +ℂ c) c-quad (length l)) .U
                    (F.map (x ∷_) .U (ret l)))
              ≡⟨ cong (λ e → CHARGE {A = F _} c .U
                    (CHARGE {A = F _} (plist₂-potential (c-quad +ℂ c) c-quad (length l)) .U e))
                    bind'/β ⟩
                CHARGE {A = F _} c .U
                  (CHARGE {A = F _} (plist₂-potential (c-quad +ℂ c) c-quad (length l)) .U
                    (ret (x ∷ l)))
              ≡⟨ sym (cong ((_$ ret (x ∷ l)) ∘ U)
                    (CHARGE-+ {A = F _} c (plist₂-potential (c-quad +ℂ c) c-quad (length l)))) ⟩
                CHARGE {A = F _}
                  (c +ℂ plist₂-potential (c-quad +ℂ c) c-quad (length l)) .U
                  (ret (x ∷ l))
              ≡⟨ cong (λ c → CHARGE {A = F _} c .U (ret (x ∷ l)))
                    (sym (plist₂-potential-suc (length l) c c-quad)) ⟩
                CHARGE {A = F _}
                  (plist₂-potential c c-quad (length (x ∷ l))) .U
                  (ret (x ∷ l))
              ≡⟨ sym bind'/β ⟩
                costᶜ-at c .U (ret (x ∷ l))
              ∎

            go◦-cons : ∀ c x (e : cmp (F (Listᵛ X))) →
              go◦ c .U (η◦ᶜ {A = F _} .U (F.map (x ∷_) .U e))
              ≡ open-econs c x .U (go◦ (c-quad +ℂ c) .U (η◦ᶜ {A = F _} .U e))
            go◦-cons c x e =
                go◦ c .U (η◦ᶜ {A = F _} .U (F.map (x ∷_) .U e))
              ≡⟨ refl ⟩
                bind' (λ l → fold◦ l c) .U (F.map (x ∷_) .U e)
              ≡⟨ bind'-assoc _ _ _ ⟩
                bind' (λ l →
                  bind' (λ l → fold◦ l c) .U (ret (x ∷ l)))
                .U e
              ≡⟨ cong (λ h → bind' {A = ◯ᶜ (A c)} h .U e) (funExt λ l → bind'/β) ⟩
                bind' (λ l →
                  open-econs c x .U (fold◦ l (c-quad +ℂ c)))
                .U e
              ≡⟨ sym (bind'-map (open-econs c x) _ _) ⟩
                open-econs c x .U (bind' (λ l → fold◦ l (c-quad +ℂ c)) .U e)
              ≡⟨ refl ⟩
                open-econs c x .U (go◦ (c-quad +ℂ c) .U (η◦ᶜ {A = F _} .U e))
              ∎

            open-cons-charge : ∀ c x l →
              ◯ᵛ.map (e-cons c x .U)
                (transport (cong cmp (sym (▷'-◯ᶜ c (A (c-quad +ℂ c)))))
                  (CHARGE {A = ◯ᶜ (A (c-quad +ℂ c))} c .U
                    ((costᶜ-at (c-quad +ℂ c) ⨾ᶜ η◦ᶜ ⨾ᶜ go◦ (c-quad +ℂ c)) .U (ret l))))
              ≡ (costᶜ-at c ⨾ᶜ η◦ᶜ ⨾ᶜ go◦ c) .U (ret (x ∷ l))
            open-cons-charge c x l =
              let
                e = costᶜ-at (c-quad +ℂ c) .U (ret l)
                s = go◦ (c-quad +ℂ c) .U (η◦ᶜ {A = F _} .U e)
              in
                open-econs c x .U (CHARGE {A = ◯ᶜ (A (c-quad +ℂ c))} c .U s)
              ≡⟨ cong ((_$ s) ∘ U) (CHARGE-commute c (open-econs c x)) ⟩
                CHARGE {A = ◯ᶜ (A c)} c .U (open-econs c x .U s)
              ≡⟨ cong (CHARGE {A = ◯ᶜ (A c)} c .U)
                    (sym (go◦-cons c x e)) ⟩
                CHARGE {A = ◯ᶜ (A c)} c .U
                  (go◦ c .U (η◦ᶜ {A = F _} .U (F.map (x ∷_) .U e)))
              ≡⟨ sym (cong ((_$ η◦ᶜ {A = F _} .U (F.map (x ∷_) .U e)) ∘ U)
                    (CHARGE-commute c (go◦ c))) ⟩
                go◦ c .U
                  (η◦ᶜ {A = F _} .U
                    (CHARGE {A = F _} c .U (F.map (x ∷_) .U e)))
              ≡⟨ cong (λ e → go◦ c .U (η◦ᶜ {A = F _} .U e)) (cost-cons c x l) ⟩
                go◦ c .U (η◦ᶜ {A = F _} .U (costᶜ-at c .U (ret (x ∷ l))))
              ∎

            fold•-coherence : ∀ c l →
              (fold•ᶜ c ⨾ᶜ ●ᶜ.map η◦ᶜ) .U (ret l)
              ≡ (costᶜ-at c ⨾ᶜ η◦ᶜ ⨾ᶜ go◦ c ⨾ᶜ η•ᶜ) .U (ret l)
            fold•-coherence c [] =
                (fold•ᶜ c ⨾ᶜ ●ᶜ.map η◦ᶜ) .U (ret [])
              ≡⟨ cong (●ᵛ.map (η◦ᶜ {A = A c} .U)) bind'/β ⟩
                η•ᶜ {A = ◯ᶜ (A c)} .U (η◦ᶜ {A = A c} .U (e-nil c))
              ≡⟨ cong (η•ᶜ {A = ◯ᶜ (A c)} .U) (sym bind'/β) ⟩
                η•ᶜ {A = ◯ᶜ (A c)} .U
                  (bind' (λ l → fold◦ l c) .U (ret []))
              ≡⟨ refl ⟩
                η•ᶜ {A = ◯ᶜ (A c)} .U
                  (go◦ c .U (η◦ᶜ {A = F _} .U (ret [])))
              ≡⟨ cong
                    (λ e → η•ᶜ {A = ◯ᶜ (A c)} .U
                      (go◦ c .U (η◦ᶜ {A = F _} .U e)))
                    (sym (cost-nil c)) ⟩
                η•ᶜ {A = ◯ᶜ (A c)} .U
                  (go◦ c .U (η◦ᶜ {A = F _} .U
                    (costᶜ-at c .U (ret []))))
              ≡⟨ refl ⟩
                (costᶜ-at c ⨾ᶜ η◦ᶜ ⨾ᶜ go◦ c ⨾ᶜ η•ᶜ) .U (ret [])
              ∎
            fold•-coherence c (x ∷ l) =
                (fold•ᶜ c ⨾ᶜ ●ᶜ.map η◦ᶜ) .U (ret (x ∷ l))
              ≡⟨ cong (●ᵛ.map (η◦ᶜ {A = A c} .U)) bind'/β ⟩
                ●ᵛ.map (η◦ᶜ {A = A c} .U)
                  (●ᵛ.map (e-cons c x .U)
                    (transport (cong cmp (sym (▷'-●ᶜ c (A (c-quad +ℂ c)))))
                      (fold• l (c-quad +ℂ c))))
              ≡⟨ cong
                  (λ q → ●ᵛ.map (η◦ᶜ {A = A c} .U)
                    (●ᵛ.map (e-cons c x .U)
                      (transport (cong cmp (sym (▷'-●ᶜ c (A (c-quad +ℂ c))))) q)))
                  (sym bind'/β) ⟩
                ●ᵛ.map (η◦ᶜ {A = A c} .U)
                  (●ᵛ.map (e-cons c x .U)
                    (transport (cong cmp (sym (▷'-●ᶜ c (A (c-quad +ℂ c)))))
                      (fold•ᶜ (c-quad +ℂ c) .U (ret l))))
              ≡⟨ (
                let
                    q▷• =
                      transport
                        (cong cmp (sym (▷'-●ᶜ c (A (c-quad +ℂ c)))))
                        (fold•ᶜ (c-quad +ℂ c) .U (ret l))
                    q▷◦ =
                      transport
                        (cong cmp (sym (▷'-◯ᶜ c (A (c-quad +ℂ c)))))
                        (CHARGE {A = ◯ᶜ (A (c-quad +ℂ c))} c .U
                          ((costᶜ-at (c-quad +ℂ c) ⨾ᶜ η◦ᶜ ⨾ᶜ go◦ (c-quad +ℂ c)) .U (ret l)))
                    tr▷◦ =
                      transport
                        (cong (λ C → cmp (●ᶜ C)) (sym (▷'-◯ᶜ c (A (c-quad +ℂ c)))))

                    q▷-coh : ●ᶜ.map (η◦ᶜ {A = ▷'[ c ] (A (c-quad +ℂ c))}) .U q▷• ≡ η• q▷◦
                    q▷-coh =
                        ●ᶜ.map (η◦ᶜ {A = ▷'[ c ] (A (c-quad +ℂ c))}) .U q▷•
                      ≡⟨ transport-▷' c (A (c-quad +ℂ c)) (fold•ᶜ (c-quad +ℂ c) .U (ret l)) ⟩
                        tr▷◦
                          ((▷'-FRAC c (A (c-quad +ℂ c)) .𝒞-FRAC.α•) .U
                            (fold•ᶜ (c-quad +ℂ c) .U (ret l)))
                      ≡⟨ cong tr▷◦
                          (sym (●ᵛ.map-∘
                            (η◦ᶜ {A = A (c-quad +ℂ c)} .U)
                            (◯ᶜ (A (c-quad +ℂ c)) .charge c)
                            (fold•ᶜ (c-quad +ℂ c) .U (ret l)))) ⟩
                        tr▷◦
                          (●ᵛ.map (CHARGE {A = ◯ᶜ (A (c-quad +ℂ c))} c .U)
                            ((fold•ᶜ (c-quad +ℂ c) ⨾ᶜ ●ᶜ.map η◦ᶜ) .U (ret l)))
                      ≡⟨ cong tr▷◦
                          (cong (●ᵛ.map (CHARGE {A = ◯ᶜ (A (c-quad +ℂ c))} c .U))
                            (fold•-coherence (c-quad +ℂ c) l)) ⟩
                        η• q▷◦
                      ∎
                  in
                  fracture-map-coh (e-cons c x) q▷• q▷◦ q▷-coh
              ) ⟩
                η•ᶜ {A = ◯ᶜ (A c)} .U
                  (◯ᵛ.map (e-cons c x .U)
                    (transport (cong cmp (sym (▷'-◯ᶜ c (A (c-quad +ℂ c)))))
                      (CHARGE {A = ◯ᶜ (A (c-quad +ℂ c))} c .U
                        ((costᶜ-at (c-quad +ℂ c) ⨾ᶜ η◦ᶜ ⨾ᶜ go◦ (c-quad +ℂ c)) .U (ret l)))))
              ≡⟨ cong (η•ᶜ {A = ◯ᶜ (A c)} .U) (open-cons-charge c x l) ⟩
                (costᶜ-at c ⨾ᶜ η◦ᶜ ⨾ᶜ go◦ c ⨾ᶜ η•ᶜ) .U (ret (x ∷ l))
              ∎
