open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Univalence using (ua)
open import Cubical.Data.Equality.Conversion using (eqToPath)
open import Cubical.Data.Sigma

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
open import Calf.Computation.Potential
open import Cubical.Data.Nat
open import Data.Nat.Combinatorics using (_C_; nC1≡n; nCk+nC[k+1]≡[n+1]C[k+1])

_⊙_ : ℕ → val ℂ → val ℂ
zero ⊙ c = 0ℂ
suc n ⊙ c = c +ℂ (n ⊙ c)

binom : ℕ → ℕ → ℕ
binom n k = _C_ n k

plist₂-potential : val ℂ → val ℂ → ℕ → val ℂ
plist₂-potential c-linear c-quadratic n =
  (n ⊙ c-linear) +ℂ (binom n 2 ⊙ c-quadratic)

module _ where 
  binom-suc-2 : ∀ n → binom (suc n) 2 ≡ n + binom n 2
  binom-suc-2 n =
      binom (suc n) 2
    ≡⟨ sym (eqToPath (nCk+nC[k+1]≡[n+1]C[k+1] n 1)) ⟩
      binom n 1 + binom n 2
    ≡⟨ cong (_+ binom n 2) (eqToPath (nC1≡n n)) ⟩
      n + binom n 2
    ∎
  
  ⊙-+ : ∀ n c₁ c₂ → n ⊙ (c₁ +ℂ c₂) ≡ (n ⊙ c₁) +ℂ (n ⊙ c₂)
  ⊙-+ zero c₁ c₂ = sym (+ℂ-identityˡ 0ℂ)
  ⊙-+ (suc n) c₁ c₂ =
      suc n ⊙ (c₁ +ℂ c₂)
    ≡⟨ cong ((c₁ +ℂ c₂) +ℂ_) (⊙-+ n c₁ c₂) ⟩
      (c₁ +ℂ c₂) +ℂ ((n ⊙ c₁) +ℂ (n ⊙ c₂))
    ≡⟨ +ℂ-assoc c₁ c₂ ((n ⊙ c₁) +ℂ (n ⊙ c₂)) ⟩
      c₁ +ℂ (c₂ +ℂ ((n ⊙ c₁) +ℂ (n ⊙ c₂)))
    ≡⟨ cong (c₁ +ℂ_) (sym (+ℂ-assoc c₂ (n ⊙ c₁) (n ⊙ c₂))) ⟩
      c₁ +ℂ ((c₂ +ℂ (n ⊙ c₁)) +ℂ (n ⊙ c₂))
    ≡⟨ cong (λ c → c₁ +ℂ (c +ℂ (n ⊙ c₂))) (+ℂ-comm c₂ (n ⊙ c₁)) ⟩
      c₁ +ℂ (((n ⊙ c₁) +ℂ c₂) +ℂ (n ⊙ c₂))
    ≡⟨ cong (c₁ +ℂ_) (+ℂ-assoc (n ⊙ c₁) c₂ (n ⊙ c₂)) ⟩
      c₁ +ℂ ((n ⊙ c₁) +ℂ (c₂ +ℂ (n ⊙ c₂)))
    ≡⟨ sym (+ℂ-assoc c₁ (n ⊙ c₁) (c₂ +ℂ (n ⊙ c₂))) ⟩
      (suc n ⊙ c₁) +ℂ (suc n ⊙ c₂)
    ∎
  
  ⊙-+-left : ∀ n m c → (n + m) ⊙ c ≡ (n ⊙ c) +ℂ (m ⊙ c)
  ⊙-+-left zero m c = sym (+ℂ-identityˡ (m ⊙ c))
  ⊙-+-left (suc n) m c =
      (suc n + m) ⊙ c
    ≡⟨ cong (c +ℂ_) (⊙-+-left n m c) ⟩
      c +ℂ ((n ⊙ c) +ℂ (m ⊙ c))
    ≡⟨ sym (+ℂ-assoc c (n ⊙ c) (m ⊙ c)) ⟩
      (suc n ⊙ c) +ℂ (m ⊙ c)
    ∎
  
  plist₂-potential-suc
    : ∀ n c-linear c-quadratic
    → plist₂-potential c-linear c-quadratic (suc n)
      ≡ c-linear +ℂ plist₂-potential (c-quadratic +ℂ c-linear) c-quadratic n
  plist₂-potential-suc n c-linear c-quadratic =
      plist₂-potential c-linear c-quadratic (suc n)
    ≡⟨ cong
        (λ b → (c-linear +ℂ (n ⊙ c-linear)) +ℂ (b ⊙ c-quadratic))
        (binom-suc-2 n) ⟩
      (c-linear +ℂ (n ⊙ c-linear))
        +ℂ ((n + binom n 2) ⊙ c-quadratic)
    ≡⟨ cong
        ((c-linear +ℂ (n ⊙ c-linear)) +ℂ_)
        (⊙-+-left n (binom n 2) c-quadratic) ⟩
      (c-linear +ℂ (n ⊙ c-linear))
        +ℂ ((n ⊙ c-quadratic) +ℂ (binom n 2 ⊙ c-quadratic))
    ≡⟨ +ℂ-assoc c-linear (n ⊙ c-linear)
        ((n ⊙ c-quadratic) +ℂ (binom n 2 ⊙ c-quadratic)) ⟩
      c-linear +ℂ
        ((n ⊙ c-linear)
          +ℂ ((n ⊙ c-quadratic) +ℂ (binom n 2 ⊙ c-quadratic)))
    ≡⟨ cong (c-linear +ℂ_)
        (sym (+ℂ-assoc (n ⊙ c-linear) (n ⊙ c-quadratic) (binom n 2 ⊙ c-quadratic))) ⟩
      c-linear +ℂ
        (((n ⊙ c-linear) +ℂ (n ⊙ c-quadratic))
          +ℂ (binom n 2 ⊙ c-quadratic))
    ≡⟨ cong
        (λ c → c-linear +ℂ (c +ℂ (binom n 2 ⊙ c-quadratic)))
        (+ℂ-comm (n ⊙ c-linear) (n ⊙ c-quadratic)) ⟩
      c-linear +ℂ
        (((n ⊙ c-quadratic) +ℂ (n ⊙ c-linear))
          +ℂ (binom n 2 ⊙ c-quadratic))
    ≡⟨ cong (c-linear +ℂ_)
        (cong (_+ℂ (binom n 2 ⊙ c-quadratic))
          (sym (⊙-+ n c-quadratic c-linear))) ⟩
      c-linear +ℂ plist₂-potential (c-quadratic +ℂ c-linear) c-quadratic n
    ∎

opaque
  PList₂ : val ℂ → val ℂ → 𝒱 → 𝒞
  PList₂ c-linear c-quadratic X =
    Glueᶜ'
      (F (Listᵛ X))
      (F (Listᵛ X))
      (bind' (λ l → F _ .charge (plist₂-potential c-linear c-quadratic (length l)) (ret l)))

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

  pfoldr₂ : ∀ {c-lin c-quad} (A : val ℂ → 𝒞)
    → (∀ c-lin → cmp (A c-lin))
    → (∀ c-lin → val X → (▷'[ c-lin ] (A (c-quad +ℂ c-lin))) ⊸ A c-lin)
    → PList₂ c-lin c-quad X ⊸ A c-lin
  pfoldr₂ {X = X} {c-lin = c-lin} {c-quad = c-quad} A e-nil e-cons =
    subst (PList₂ c-lin c-quad X ⊸_) Glueᶜ'-id $
    squareᶜ'
     {!   !} {!   !} {!   !} 
