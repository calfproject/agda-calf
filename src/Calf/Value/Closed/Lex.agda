module Calf.Value.Closed.Lex where

open import Calf.Core.Abstract
open import Calf.Value
open import Calf.Value.Closed.Base
open import Calf.Value.Unit

open import 1Lab.Set.Pi
open import Cubical.Foundations.CartesianKanOps

●-encode : ∀ {X} → X → ● X → 𝒱
●-encode x (η• x') = ● (x ≡ x')
●-encode x (∗ abs) = 1ᵛ
●-encode x (law x' abs i) = isContr→≡Unit (●-isContr {X = x ≡ x'} abs) i

●-lex : ∀ {X} {x : X} {y : ● X} → η• x ≡ y → ●-encode x y
●-lex {x = x} h = J (λ y _ → ●-encode x y) (η• refl) h

●-unlex : ∀ {X} {x x' : X} → ● (x ≡ x') → η• x ≡ η• x'
●-unlex (η• h) = cong η• h
●-unlex {x = x} {x'} (∗ abs) = law x abs ∙ sym (law x' abs)
●-unlex {x = x} {x'} (law h abs i) =
  isProp→isSet (●-isProp abs) (η• x) (η• x')
    (cong η• h)
    (law x abs ∙ sym (law x' abs))
    i

●-unlex' : ∀ {X} {x : X} {y : ● X} → ●-encode x y → η• x ≡ y
●-unlex' {X} {x} {y} e =
  ind R η•-case ∗-case law-case y e
  where
  R : ● X → 𝒱
  R y = ●-encode x y → η• x ≡ y

  η•-case : (x' : X) → R (η• x')
  η•-case x' e = ●-unlex e

  ∗-case : (abs : ⟨ ABS ⟩) → R (∗ abs)
  ∗-case abs _ = law x abs

  law-case : (x' : X) (abs : ⟨ ABS ⟩) → PathP (λ i → R (law x' abs i)) (η•-case x') (∗-case abs)
  law-case x' abs =
    funext-dep-i0 λ e →
      isProp→PathP
        (λ i → isProp→isSet (●-isProp abs)
          (η• x)
          (law x' abs i))
        (η•-case x' e)
        (∗-case abs (coe0→1 (λ i → ●-encode x (law x' abs i)) e))

●-lex-unlex : ∀ {X} {x x' : X} (e : ● (x ≡ x')) → ●-lex (●-unlex e) ≡ e
●-lex-unlex {x = x} (η• h) =
  J
    (λ x' h → ●-lex (cong η• h) ≡ η• h)
    (JRefl {x = η• x} (λ y _ → ●-encode x y) (η• refl))
    h
●-lex-unlex {x = x} {x'} (∗ abs) =
  ●-isProp abs
    (●-lex (law x abs ∙ sym (law x' abs)))
    (∗ abs)
●-lex-unlex {x = x} {x'} (law h abs i) =
  isProp→PathP
    (λ i → isProp→isSet (●-isProp abs)
      (●-lex (●-unlex (law h abs i)))
      (law h abs i))
    (●-lex-unlex (η• h))
    (●-lex-unlex (∗ abs))
    i

●-unlex-lex : ∀ {X} {x x' : X} (h : η• x ≡ η• x') → ●-unlex (●-lex h) ≡ h
●-unlex-lex {X} {x} h =
  J
    (λ y h → ●-unlex' (●-lex h) ≡ h)
    (cong
      (λ e → ●-unlex' {X = X} {x = x} {y = η• x} e)
      (JRefl {x = η• x} (λ y _ → ●-encode x y) (η• {X = x ≡ x} refl)))
    h
