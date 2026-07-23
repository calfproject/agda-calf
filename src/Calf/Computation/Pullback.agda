module Calf.Computation.Pullback where

open import Calf.Value
open import Calf.Value.Sigma public
open import Calf.Computation

Pullback : ∀ {A B C} → (f : A ⊸ C) (g : B ⊸ C) → 𝒞
Pullback {A} {B} {C} f g .U =
  Σ[ a ∈ U A ] Σ[ b ∈ U B ] U f a ≡ U g b
Pullback {A} {B} {C} f g .is-preorder = {!   !}
  -- isSetΣ (A .is-set) λ a →
  -- isSetΣ (B .is-set) λ b →
  -- isProp→isSet (C .is-set (U f a) (U g b))
Pullback {A} {B} {C} f g .charge c (a , b , p) =
  A .charge c a ,
  B .charge c b ,
  f .charge c a ∙ cong (C .charge c) p ∙ sym (g .charge c b)
Pullback {A} {B} {C} f g .charge/0 =
  ΣPathP (A .charge/0 , ΣPathP (B .charge/0 ,
    isProp→PathP (λ i → is-set C _ _) _ _))
Pullback {A} {B} {C} f g .charge/+ =
  ΣPathP (A .charge/+ , ΣPathP (B .charge/+ ,
    isProp→PathP (λ i → is-set C _ _) _ _))
