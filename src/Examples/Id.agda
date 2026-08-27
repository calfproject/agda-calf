module Examples.Id where

open import Calf.Core.Cost
open import Calf.Value hiding (id)
open import Calf.Value.Nat
open import Calf.Computation
open import Calf.Computation.Free
open import Calf.Computation.Power


module Easy where
  id : U (ℕ ⇀ F ℕ)
  id n = ret n

  id/bound : U (ℕ ⇀ F ℕ)
  id/bound n = ret n

  id/is-bounded : id ⊑ id/bound
  id/is-bounded = ⊑-funext λ _ → ⊑-refl

  id/correct : BEH → id ≡ ret
  id/correct beh = ⊑-beh' beh id/is-bounded


module Hard where
  id : U (ℕ ⇀ F ℕ)
  id zero = ret 0
  id (suc n) =
    charge` (F _) 1 $
    bind[ F _ ] n' ← id n ⨾
    ret (suc n')

  id/bound : U (ℕ ⇀ F ℕ)
  id/bound n = charge` (F _) n (ret n)

  id/is-bounded : id ⊑ id/bound
  id/is-bounded = ⊑-funext lemma
    where
      lemma : ∀ n → id n ⊑ id/bound n
      lemma zero = ⊑-refl
      lemma (suc n) =
        let open ⊑-Reasoning (F ℕ) in
        ⊑-mono (charge` (F _) 1) $
        begin
          bind[ F _ ] n' ← id n ⨾ ret (suc n')
        ⊑⟨ ⊑-mono (λ e → bind[ F _ ] n' ← e ⨾ ret (suc n')) (lemma n) ⟩
          bind[ F _ ] n' ← id/bound n ⨾ ret (suc n')
        ≡ᴾ⟨ bind/charge`-ret n ⟩
          charge` (F _) n (ret (suc n))
        ∎ᴾ

  id/correct : BEH → id ≡ ret
  id/correct beh = ⊑-beh' beh id/is-bounded ∙ funExt (λ n → charge`/BEH (F _) n beh)


easy≡hard : BEH → Easy.id ≡ Hard.id
easy≡hard beh = Easy.id/correct beh ∙ sym (Hard.id/correct beh)
