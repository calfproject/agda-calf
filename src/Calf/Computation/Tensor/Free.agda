module Calf.Computation.Tensor.Free where

open import Calf.Core.Cost
open import Calf.Value
open import Calf.Value.Product
open import Calf.Computation
open import Calf.Computation.Free

open import Cubical.Foundations.Univalence using (ua→; ua-gluePath)

open import Calf.Computation.Tensor.Base

opaque
  unfolding F

  F-monoidal : (F X ⊗ F Y) ≡ F (X × Y)
  F-monoidal {X} {Y} = {!   !}

par : U (F X) → U (F Y) → U (F (X × Y))
par ex ey = transport (cong U F-monoidal) (ex ∥ ey)

module _ {X : 𝒱ₛ} where
  open import Calf.Computation.Copower

  opaque
    unfolding F

    Σᶜ-F-fwd : ([ x ∈ X ] ⋊ ⊤) ⊸ F ⟨ X ⟩
    Σᶜ-F-fwd .U (x , c) = c , ηᴾ x
    Σᶜ-F-fwd .charge _ _ = refl

    F-Σᶜ-fwd : F ⟨ X ⟩ ⊸ ([ x ∈ X ] ⋊ ⊤)
    F-Σᶜ-fwd .U (c , x) =
      rec (Σᶜ X (const ⊤) .is-preorder) (λ x → x , c) x
    F-Σᶜ-fwd .charge c (c' , x) =
      rec-unique
        (Σᶜ X (const ⊤) .is-preorder)
        (λ x → F-Σᶜ-fwd .U (c +ℂ c' , x))
        (λ x → Σᶜ X (const ⊤) .charge c (F-Σᶜ-fwd .U (c' , x)))
        (λ _ → refl)
        x

    F-Σᶜ-fwd-equiv : isEquivᶜ F-Σᶜ-fwd
    F-Σᶜ-fwd-equiv =
      isoToIsEquiv (iso (F-Σᶜ-fwd .U) (Σᶜ-F-fwd .U) sec retr)
      where
        sec : ∀ e → F-Σᶜ-fwd .U (Σᶜ-F-fwd .U e) ≡ e
        sec _ = refl

        retr : ∀ e → Σᶜ-F-fwd .U (F-Σᶜ-fwd .U e) ≡ e
        retr (c , x) =
          rec-unique
            (F ⟨ X ⟩ .is-preorder)
            (λ x → Σᶜ-F-fwd .U (F-Σᶜ-fwd .U (c , x)))
            (c ,_)
            (λ _ → refl)
            x

    F-Σᶜ : F ⟨ X ⟩ ≡ ([ x ∈ X ] ⋊ ⊤)
    F-Σᶜ = conservativity F-Σᶜ-fwd F-Σᶜ-fwd-equiv

    F-Σᶜ-potential : ∀ (Φ : ⟨ X ⟩ → ℂ)
      → PathP (λ i → F-Σᶜ i ⊸ F-Σᶜ i)
          (bind' λ x → F _ .charge (Φ x) (ret x))
          (Σᶜ-map {X} {const ⊤} (λ x → CHARGE (Φ x)))
    F-Σᶜ-potential Φ =
      ⊸-path F-Σᶜ F-Σᶜ
        (ua→
          {e = F-Σᶜ-fwd .U , F-Σᶜ-fwd-equiv}
          (λ e → ua-gluePath _ (naturality e)))
      where
        naturality : (e : U (F ⟨ X ⟩)) →
          F-Σᶜ-fwd .U (bind' {A = F _} (λ x → F _ .charge (Φ x) (ret x)) .U e)
          ≡ Σᶜ-map {X} {const ⊤} (λ x → CHARGE (Φ x)) .U (F-Σᶜ-fwd .U e)
        naturality (c , x) =
          rec-unique
            (Σᶜ X (const ⊤) .is-preorder)
            (λ x →
              F-Σᶜ-fwd .U
                (bind' {A = F _} (λ x → F _ .charge (Φ x) (ret x)) .U (c , x)))
            (λ x →
              Σᶜ-map {X} {const ⊤} (λ x → CHARGE (Φ x)) .U
                (F-Σᶜ-fwd .U (c , x)))
            (λ x → cong (x ,_) (cong (c +ℂ_) (+ℂ-identityʳ _) ∙ +ℂ-comm c (Φ x)))
            x
