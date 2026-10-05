open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence using (ua; ua-gluePath)
open import Cubical.Data.Sigma

-- Much of this structure is an adaptation and extension of:
-- https://agda.monade.li/ErasureOpen.html
module Cubical.Modalities.Extras {ℓ : Level}
  {◯ : Type ℓ → Type ℓ}
  {η : ∀ {X : Type ℓ} → X → ◯ X}
  (elim◯
    : {X : Type ℓ} {Y : ◯ X → Type ℓ}
    → ((x : X) → ◯ (Y (η x))) → (x : ◯ X) → ◯ (Y x))
  (elim◯-β
    : {X : Type ℓ} {Y : ◯ X → Type ℓ} {y : (x : X) → ◯ (Y (η x))}
    → (x : X) → elim◯ {Y = Y} y (η x) ≡ y x)
  (isModal◯≡ : {X : Type ℓ} {x◦ x◦' : ◯ X} → isEquiv (η {X = x◦ ≡ x◦'}))
  (rec◯ : {X : Type ℓ} {Y : Type ℓ} → (X → ◯ Y) → ◯ X → ◯ Y)
  (rec◯-β :
    {X : Type ℓ} {Y : Type ℓ} {y : X → ◯ Y}
    → (x : X) → rec◯ y (η x) ≡ y x)
  where

private variable X Y Z : Type ℓ

isModal isConnected : Type ℓ → Type ℓ
isModal X = isEquiv (η {X = X})
isConnected X = isContr (◯ X)

isModalMap isConnectedMap : (X → Y) → Type _
isModalMap {Y = Y} f = (y : Y) → isModal (fiber f y)
isConnectedMap {Y = Y} f = (y : Y) → isConnected (fiber f y)

isModal+isConnected→isContr : isModal X → isConnected X → isContr X
isModal+isConnected→isContr X-isModal =
  isOfHLevelRespectEquiv 0 (invEquiv (η , X-isModal))

isModal+isConnected→isEquiv : {f : X → Y}
  → isModalMap f → isConnectedMap f → isEquiv f
isModal+isConnected→isEquiv f-isModal f-isConnected .equiv-proof y =
  isModal+isConnected→isContr (f-isModal y) (f-isConnected y)

elim
  : {X : Type ℓ} {Y : ◯ X → Type ℓ}
  → (∀ x → isModal (Y x))
  → ((x : X) → Y (η x)) → (x◦ : ◯ X) → Y x◦
elim Y-isModal y x◦ = invIsEq (Y-isModal x◦) (elim◯ (η ∘ y) x◦)

elim-β
  : ∀ {X : Type ℓ} {Y : ◯ X → Type ℓ} Y-isModal {y : (x : X) → Y (η x)}
  → (x : X) → elim {Y = Y} Y-isModal y (η x) ≡ y x
elim-β Y-isModal {y} x =
  cong (invIsEq (Y-isModal (η x))) (elim◯-β x) ∙ retIsEq (Y-isModal (η x)) (y x)

rec
  : {X : Type ℓ} {Y : Type ℓ}
  → isModal Y
  → (X → Y) → ◯ X → Y
rec = elim ∘ const

rec-β
  : ∀ {X : Type ℓ} {Y : Type ℓ} Y-isModal {y : X → Y}
  → (x : X) → rec Y-isModal y (η x) ≡ y x
rec-β = elim-β ∘ const

rec-isEquiv : (isModalY : isModal Y) {f : X → Y} (e : ◯ X ≃ Y)
  → ((x : X) → equivFun e (η x) ≡ f x) → isEquiv (rec isModalY f)
rec-isEquiv = {!   !}

∘η-≃ : {Y : ◯ X → Type ℓ} → ((x◦ : ◯ X) → isModal (Y x◦))
  → ((x◦ : ◯ X) → Y x◦) ≃ ((x : X) → Y (η x))
∘η-≃ Y-isModal = _∘ η , {!   !}

-- ∘η-isEquiv : ∀ {X Y} → isModal Y → isEquiv (λ (f : ◯ X → Y) → f ∘ η)
-- ∘η-isEquiv Y-isModal =
--   isoToIsEquiv
--     (iso _
--       (rec Y-isModal)
--       (λ g → {!   !}) -- funExt (rec-β {!   !}))
--       (λ f → {! rec-β  !}))

map : (X → Y) → ◯ X → ◯ Y
map f = rec◯ (η ∘ f)

map-β : (f : X → Y) (x : X) → map f (η x) ≡ η (f x)
map-β _ = rec◯-β

map-id : (x◦ : ◯ X) → x◦ ≡ map (idfun _) x◦
map-id = elim (λ _ → isModal◯≡) λ x → sym (map-β (idfun _) x)

map-∘ : (f : X → Y) (g : Y → Z) (x◦ : ◯ X) →
  map g (map f x◦) ≡ map (g ∘ f) x◦
map-∘ f g =
  elim (λ _ → isModal◯≡) λ x →
    cong (map g) (map-β f x) ∙ map-β g (f x) ∙ sym (map-β (g ∘ f) x)

◯-≃ : X ≃ Y → ◯ X ≃ ◯ Y
◯-≃ e = map (equivFun e) , {!   !}

-- map-≃ : A ≃ B → (○ A) ≃ (○ B)
-- map-≃ e = map (e .fst) , is-iso→is-equiv λ where
--   .is-iso.from → map (Equiv.from e)
--   .is-iso.rinv → elim-modal (λ _ → ○-≡-modal) λ b →
--     ap (map (e .fst)) (○-elim-β b) ∙ ○-elim-β (Equiv.from e b) ∙ ap η○ (Equiv.ε e b)
--   .is-iso.linv → elim-modal (λ _ → ○-≡-modal) λ a →
--     ap (map (Equiv.from e)) (○-elim-β a) ∙ ○-elim-β (e .fst a) ∙ ap η○ (Equiv.η e a)

join : ◯ (◯ X) → ◯ X
join = rec◯ (idfun _)

join-identityˡ : {x◦ : ◯ X} → join (η x◦) ≡ x◦
join-identityˡ = {!   !}

map-η-isEquiv : isEquiv (map (η {X}))
map-η-isEquiv =
  isoToIsEquiv
    (iso _
    join
    (elim {!   !} λ _ → cong (rec◯ _) (rec◯-β _) ∙ {!   !})
    {!   !})

bind : ◯ X → (X → ◯ Y) → ◯ Y
bind = flip rec◯

isRetract◯→isModal : (η⁻ : ◯ X → X) → retract η η⁻ → isModal X
isRetract◯→isModal η⁻ ret =
  isoToIsEquiv (iso _ η⁻ (elim (λ _ → isModal◯≡) (cong η ∘ ret)) ret)

  -- retract-○→modal : (η⁻¹ : ○ A → A) → is-left-inverse η⁻¹ η○ → modal A
  -- retract-○→modal η⁻¹ ret = is-iso→is-equiv $
  --   iso η⁻¹ (elim-modal (λ _ → ○-≡-modal) λ a → ap η○ (ret a)) ret

isModalRetract : (s : Y → X) (r : X → Y) → retract s r → isModal X → isModal Y
isModalRetract = {!   !}

  -- retract→modal
  --   : (f : A → B) (g : B → A)
  --   → is-left-inverse f g → modal A → modal B
  -- retract→modal {B = B} f g ret A-modal = retract-○→modal η⁻¹ linv where
  --   η⁻¹ : ○ B → B
  --   η⁻¹ = f ∘ elim-modal (λ _ → A-modal) g
  --   linv : is-left-inverse η⁻¹ η○
  --   linv b = ap f (elim-modal-β (λ _ → A-modal) b) ∙ ret b

isModal-≃ : Y ≃ X → isModal X → isModal Y
isModal-≃ = {!   !}
  -- modal-≃ : B ≃ A → modal A → modal B
  -- modal-≃ e = retract→modal (Equiv.from e) (Equiv.to e) (Equiv.η e)

isConnected-≃ : Y ≃ X → isConnected X → isConnected Y
isConnected-≃ = {!   !}

  -- connected-≃ : B ≃ A → connected A → connected B
  -- connected-≃ e A-conn = Equiv→is-hlevel 0 (map-≃ e) A-conn

  -- ≡-modal : modal A → ∀ {x y : A} → modal (x ≡ y)
  -- ≡-modal A-modal = modal-≃ (ap-equiv (η○ , A-modal)) ○-≡-modal

  -- PathP-modal : {A : I → Type ℓ} → modal (A i0) → ∀ {x y} → modal (PathP A x y)
  -- PathP-modal {A = A} A-modal {x} {y} = subst modal (sym (PathP≡Path⁻ A x y)) (≡-modal A-modal)

isModal◯ : isModal (◯ X)
isModal◯ =
  isoToIsEquiv
    (iso _
      join
      (elim (λ _ → isModal◯≡) (cong η ∘ rec◯-β))
      rec◯-β)

isModalΠ
  : {Y : X → Type ℓ}
  → (∀ x → isModal (Y x))
  → isModal ((x : X) → Y x)
isModalΠ {X} {Y} Y-isModal =
  isRetract◯→isModal
    (λ f x → elim (λ _ → Y-isModal _) (_$ x) f)
    (λ f → funExt λ x → elim-β (λ _ → Y-isModal _) f)

isModal→ : isModal Y → isModal (X → Y)
isModal→ = isModalΠ ∘ const

isModalΣ : {Y : X → Type ℓ}
  → isModal X
  → ((x : X) → isModal (Y x))
  → isModal (Σ X Y)
isModalΣ = {!   !}

isModal× : isModal X → isModal Y → isModal (X × Y)
isModal× X-isModal = isModalΣ X-isModal ∘ const

  -- Σ-modal : {B : A → Type ℓ} → modal A → (∀ a → modal (B a)) → modal (Σ A B)
  -- Σ-modal {B = B} A-modal B-modal = retract-○→modal
  --   (Equiv.from Σ-Π-distrib
  --     ( elim-modal (λ _ → A-modal) fst
  --     , elim-modal (λ _ → B-modal _) λ (a , b) →
  --         subst B (sym (elim-modal-β (λ _ → A-modal) (a , b))) b))
  --   λ (a , b) →
  --        elim-modal-β (λ _ → A-modal) (a , b)
  --     ,ₚ elim-modal-β (λ _ → B-modal _) (a , b) ◁ to-pathp⁻ refl

  -- η-connected : connected-map (η○ {A = A})
  -- η-connected a = contr
  --   (○-elim {P = fibre η○} (λ a → η○ (a , refl)) a)
  --   (elim-modal (λ _ → ○-≡-modal) λ (a' , p) →
  --     J (λ a p → ○-elim (λ x → η○ (x , refl)) a ≡ η○ (a' , p)) (○-elim-β a') p)

  -- ○Σ○≃○Σ : {B : A → Type ℓ} → (○ (Σ A λ a → ○ B a)) ≃ (○ (Σ A B))
  -- ○Σ○≃○Σ .fst = ○-elim λ (a , b) → map (a ,_) b
  -- ○Σ○≃○Σ .snd = is-iso→is-equiv λ where
  --   .is-iso.from → map (Σ-map₂ η○)
  --   .is-iso.rinv → elim-modal (λ _ → ○-≡-modal) λ (a , b) →
  --     ap (○-elim _) (○-elim-β (a , b)) ∙ ○-elim-β (a , η○ b) ∙ ○-elim-β b
  --   .is-iso.linv → elim-modal (λ _ → ○-≡-modal) λ (a , b) →
  --     ap (map _) (○-elim-β (a , b)) ∙ elim-modal
  --       {P = λ b → ○-elim _ (○-elim _ b) ≡ η○ (a , b)} (λ _ → ○-≡-modal)
  --       (λ b → ap (○-elim _) (○-elim-β b) ∙ ○-elim-β (a , b)) b

isConnectedΣ : {Y : X → Type ℓ}
  → isConnected X
  → ((x : X) → isConnected (Y x))
  → isConnected (Σ X Y)
isConnectedΣ = {!   !}

  -- Σ-connected : {B : A → Type ℓ} → connected A → (∀ a → connected (B a)) → connected (Σ A B)
  -- Σ-connected A-conn B-conn = Equiv→is-hlevel 0 (○Σ○≃○Σ e⁻¹)
  --   (connected-≃ (Σ-contr-snd B-conn) A-conn)




-- open import Cubical.Foundations.Equiv
-- open import Cubical.Foundations.Equiv.Properties
--   using (equivAdjointEquiv)
-- open import Cubical.Foundations.Function
-- open import Cubical.Foundations.HLevels
-- open import Cubical.Foundations.Isomorphism
-- open import Cubical.Foundations.Path
--   using (PathP≡Path⁻; PathP≃Path; compPathlEquiv; compPathrEquiv)
-- open import Cubical.Foundations.Univalence
--   using (isEquivTransport; ua; ua-gluePath)
-- open import Cubical.Data.Sigma

-- open Modality M
--   using (isModal≡; isModalToIsEquiv; equivPreservesIsModal; ◯-equiv; ◯-preservesProp)
--   -- hiding (isModal; ◯; η; ◯-rec◯; ◯-rec-β)
--   renaming
--     ( ◯-elim to elim
--     ; ◯-elim-β to elim-β
--     ; ◯-map to map
--     ; ◯-map-β to map-β
--     ; ◯-=-isModal to ◯-≡-isModal
--     ; ◯-isModal to isModal◯
--     ; Π-isModal to isModalΠ
--     ; →-isModal to isModal→
--     )
--   public

--   bind : ◯ X → (X → ◯ Y) → ◯ Y
--   bind x◦ k = join (map k x◦)

--   η-isNatural : (f : X → Y) → η ∘ f ≡ map f ∘ η
--   η-isNatural f = funExt λ x → sym (map-β f x)

--   map-η≡η : map (η {X}) ≡ η
--   map-η≡η = funExt (elim (λ _ → ◯-≡-isModal _ _) (map-β η))

--   opaque
--     map-η-isEquiv : isEquiv (map (η {X}))
--     map-η-isEquiv = subst isEquiv (sym map-η≡η) (isModalToIsEquiv isModal◯)

-- -- ○Σ○ is equivalent to ○Σ
-- module _ {X : Type ℓ} {Y : X → Type ℓ} where
--   ○Σ○≃○Σ : ◯ (Σ X (◯ ∘ Y)) ≃ ◯ (Σ X Y)
--   ○Σ○≃○Σ = isoToEquiv (iso bwd fwd bwd-fwd fwd-bwd)
--     where
--       fwd₀ : Σ X Y → Σ X (◯ ∘ Y)
--       fwd₀ (x , y) = x , η y

--       fwd : ◯ (Σ X Y) → ◯ (Σ X (◯ ∘ Y))
--       fwd = map fwd₀

--       bwd₀ : Σ X (◯ ∘ Y) → ◯ (Σ X Y)
--       bwd₀ (x , y◦) = map (x ,_) y◦

--       bwd : ◯ (Σ X (◯ ∘ Y)) → ◯ (Σ X Y)
--       bwd = rec isModal◯ bwd₀

--       bwd-fwd : ∀ w → bwd (fwd w) ≡ w
--       bwd-fwd = elim (λ _ → ◯-≡-isModal _ _) λ (x , y) →
--           cong bwd (map-β fwd₀ (x , y))
--         ∙ rec-β isModal◯ bwd₀ (x , η y)
--         ∙ map-β (x ,_) y

--       lemma : ∀ x (y◦ : ◯ (Y x)) → map (λ y → x , η y) y◦ ≡ η (x , y◦)
--       lemma x = elim (λ _ → ◯-≡-isModal _ _) λ y → map-β (λ y → x , η y) y

--       fwd-bwd : ∀ w → fwd (bwd w) ≡ w
--       fwd-bwd = elim (λ _ → ◯-≡-isModal _ _) λ (x , y◦) →
--           cong fwd (rec-β isModal◯ bwd₀ (x , y◦))
--         ∙ map-∘ (x ,_) fwd₀ y◦
--         ∙ lemma x y◦

-- -- isModal (inherited) and isConnected
-- module _ where
--   isConnected : Type ℓ → Type ℓ
--   isConnected X = isContr (◯ X)

--   isModalMap : (X → Y) → Type ℓ
--   isModalMap {Y = Y} f = (y : Y) → isModal (fiber f y)

--   isConnectedMap : (X → Y) → Type ℓ
--   isConnectedMap {Y = Y} f = (y : Y) → isConnected (fiber f y)

-- -- lemmas about isModal
-- module _ where
--   isModalΣ : {Y : X → Type ℓ}
--     → isModal X
--     → ((x : X) → isModal (Y x))
--     → isModal (Σ X Y)
--   isModalΣ = Σ-isModal _

--   isModalIsProp : isModal X → isModal (isProp X)
--   isModalIsProp w = isModalΠ λ _ → isModalΠ λ _ → isModal≡ w

isModalPathP : {X : I → Type ℓ} → isModal (X i0) → ∀ {x x'} → isModal (PathP X x x')
isModalPathP = {!   !}

isModal≡ : isModal X → ∀ {x x'} → isModal (x ≡ x')
isModal≡ {X} = isModalPathP {λ _ → X}

--   opaque
--     isModalPathP : {X : I → Type ℓ} → isModal (X i0) → ∀ {x x'} → isModal (PathP X x x')
--     isModalPathP {X = X} h {x} {x'} =
--       subst isModal (sym (PathP≡Path⁻ X x x')) (isModal≡ h)

--   η-ext : {Y : ◯ X → Type ℓ} (_ : (x◦ : ◯ X) → isModal (Y x◦))
--     {y y' : (x◦ : ◯ X) → Y x◦} → y ∘ η ≡ y' ∘ η → y ≡ y'
--   η-ext y p = funExt (elim (λ x◦ → isModal≡ (y x◦)) (funExt⁻ p))

--   ◯-rec-unique : {f : X → Y} (isModalY : isModal Y) {h : ◯ X → Y}
--     → h ∘ η ≡ f → h ≡ rec isModalY f
--   ◯-rec-unique isModalY p =
--     η-ext (λ _ → isModalY) (p ∙ sym (funExt (rec-β isModalY _)))

-- -- lemmas about rec
-- module _ where
--   ◯-rec-map : (isModalZ : isModal Z) (g : Y → Z) (h : X → Y) (x◦ : ◯ X)
--     → rec isModalZ g (map h x◦) ≡ rec isModalZ (g ∘ h) x◦
--   ◯-rec-map isModalZ g h =
--     funExt⁻ $ η-ext (λ _ → isModalZ) $ funExt λ x →
--       cong (rec isModalZ g) (map-β h x)
--     ∙ rec-β isModalZ g (h x) ∙ sym (rec-β isModalZ (g ∘ h) x)

--   ◯-rec-const : (isModalZ : isModal Y) (y : Y) (x◦ : ◯ X) → rec isModalZ (λ _ → y) x◦ ≡ y
--   ◯-rec-const isModalZ y =
--     funExt⁻ (η-ext (λ _ → isModalZ) (funExt (rec-β isModalZ (λ _ → y))))

--   opaque
--     rec-isEquiv : (isModalY : isModal Y) {f : X → Y} (e : ◯ X ≃ Y)
--       → ((x : X) → equivFun e (η x) ≡ f x) → isEquiv (rec isModalY f)
--     rec-isEquiv isModalY e β =
--       subst isEquiv (◯-rec-unique isModalY (funExt β)) (equivIsEquiv e)

◯-ua-gluePath : (e : X ≃ Y) (x◦ : ◯ X) → PathP (λ i → ◯ (ua e i)) x◦ (map (equivFun e) x◦)
◯-ua-gluePath e = {!   !}
  -- elim (λ _ → isModalPathP isModal◯) λ x →
  --   congP (λ _ → η) (ua-gluePath e refl) ▷ sym (map-β (equivFun e) x)

-- -- lemmas about isConnected
-- module _ where
--   opaque
--     isConnected-≃ : X ≃ Y → isConnected X → isConnected Y
--     isConnected-≃ e = isOfHLevelRespectEquiv 0 (◯-equiv e)

--   opaque
--     isConnectedΣ : {Y : X → Type ℓ}
--       → isConnected X
--       → ((x : X) → isConnected (Y x))
--       → isConnected (Σ X Y)
--     isConnectedΣ cX cY =
--       isOfHLevelRespectEquiv 0 ○Σ○≃○Σ
--         (isConnected-≃ (invEquiv (Σ-contractSnd cY)) cX)

isConnectedMapη : isConnectedMap (η {X})
isConnectedMapη = {!   !}
--   isConnectedMapη {X} y = center y , contract y
--     where
--       center : (y : ◯ X) → ◯ (fiber η y)
--       center = elim (λ _ → isModal◯) (λ x → η (x , refl))

--       contract : (y : ◯ X) (w : ◯ (fiber η y)) → center y ≡ w
--       contract y = elim (λ _ → ◯-≡-isModal _ _)
--         (λ (x , p) → J (λ y' p' → center y' ≡ η (x , p'))
--           (elim-β (λ _ → isModal◯) (λ x → η (x , refl)) x)
--           p)

--   opaque
--     isContr→isConnected : isContr X → isConnected X
--     isContr→isConnected (x , contr) =
--       η x , elim (λ _ → ◯-≡-isModal _ _) (cong η ∘ contr)

--   opaque
--     isEquiv→isConnectedMap : {f : X → Y} → isEquiv f → isConnectedMap f
--     isEquiv→isConnectedMap f-equiv y = isContr→isConnected (f-equiv .equiv-proof y)

isConnectedMap-∘ₑ : (e : Y ≃ Z) {f : X → Y}
  → isConnectedMap f → isConnectedMap (equivFun e ∘ f)
isConnectedMap-∘ₑ = {!   !}
--   opaque
--     isConnectedMap-∘ₑ e {f} conn z =
--       isConnected-≃
--         (Σ-cong-equiv-snd λ x → equivAdjointEquiv e)
--         (conn (invEq e z))

--   map-Σ : {X X' : Type ℓ} {Y : X → Type ℓ} {Y' : X' → Type ℓ}
--     (f : X → X') → ((x : X) → Y x → Y' (f x))
--     → Σ X Y → Σ X' Y'
--   map-Σ f g (x , y) = f x , g x y

--   opaque
--     isConnectedMapΣ : {X X' : Type ℓ} {Y : X → Type ℓ} {Y' : X' → Type ℓ}
--       {f : X → X'} {g : (x : X) → Y x → Y' (f x)}
--       → isConnectedMap f → ((x : X) → isConnectedMap (g x))
--       → isConnectedMap (map-Σ {Y' = Y'} f g)
--     isConnectedMapΣ {X} {X'} {Y} {Y'} {f} {g} f-conn g-conn (x' , y') =
--       isConnected-≃ (invEquiv e)
--         (isConnectedΣ (f-conn x') λ (x , h) →
--           isConnectedMap-∘ₑ
--             (transport (λ i → Y' (h i)) , isEquivTransport (λ i → Y' (h i)))
--             (g-conn x)
--             y')
--       where
--         e : fiber (map-Σ {Y' = Y'} f g) (x' , y')
--           ≃ (Σ[ (x , h) ∈ fiber f x' ] fiber (transport (λ i → Y' (h i)) ∘ g x) y')
--         e =
--             fiber (map-Σ {Y' = Y'} f g) (x' , y')
--           ≃⟨ Σ-cong-equiv-snd (λ _ → invEquiv ΣPath≃PathΣ) ⟩
--             (Σ[ (x , y) ∈ Σ X Y ] Σ[ h ∈ f x ≡ x' ]
--               PathP (λ i → Y' (h i)) (g x y) y')
--           ≃⟨ Σ-assoc-≃ ⟩
--             (Σ[ x ∈ X ] Σ[ y ∈ Y x ] Σ[ h ∈ f x ≡ x' ]
--               PathP (λ i → Y' (h i)) (g x y) y')
--           ≃⟨ Σ-cong-equiv-snd (λ x →
--                  invEquiv Σ-assoc-≃
--                ∙ₑ invEquiv (Σ-cong-equiv-fst Σ-swap-≃)
--                ∙ₑ Σ-assoc-≃) ⟩
--             (Σ[ x ∈ X ] Σ[ h ∈ f x ≡ x' ] Σ[ y ∈ Y x ]
--               PathP (λ i → Y' (h i)) (g x y) y')
--           ≃⟨ invEquiv Σ-assoc-≃ ⟩
--             (Σ[ (x , h) ∈ fiber f x' ] Σ[ y ∈ Y x ]
--               PathP (λ i → Y' (h i)) (g x y) y')
--           ≃⟨ Σ-cong-equiv-snd (λ (x , h) → Σ-cong-equiv-snd λ y →
--                PathP≃Path (λ i → Y' (h i)) (g x y) y') ⟩
--             (Σ[ (x , h) ∈ fiber f x' ] fiber (transport (λ i → Y' (h i)) ∘ g x) y')
--           ■

-- -- isModal + isConnected
-- module _ where
--   opaque
--     isModal+isConnected→isContr : isModal X → isConnected X → isContr X
--     isModal+isConnected→isContr X-modal =
--       isOfHLevelRespectEquiv 0 (invEquiv (η , isModalToIsEquiv X-modal))

--   opaque
--     isModal+isConnected→isEquiv : {f : X → Y}
--       → isModalMap f → isConnectedMap f → isEquiv f
--     isModal+isConnected→isEquiv f-modal f-connected .equiv-proof y =
--       isModal+isConnected→isContr (f-modal y) (f-connected y)

-- -- reflection-≃
-- module _ where
--   reflection-inv : {f : X → Y} (w : isModal Y) (conn : isConnectedMap f)
--     → Y → ◯ X
--   reflection-inv w conn y = map fst (conn y .fst)

--   opaque
--     reflection-sec : {f : X → Y} (w : isModal Y) (conn : isConnectedMap f)
--       → section (rec w f) (reflection-inv w conn)
--     reflection-sec {f = f} w conn y =
--         ◯-rec-map w f fst (conn y .fst)
--       ∙ cong (λ k → rec w k (conn y .fst)) (funExt snd)
--       ∙ ◯-rec-const w y (conn y .fst)

--   opaque
--     reflection-ret : {f : X → Y} (w : isModal Y) (conn : isConnectedMap f)
--       → retract (rec w f) (reflection-inv w conn)
--     reflection-ret {f = f} w conn = funExt⁻ (η-ext (λ _ → isModal◯) (funExt λ x →
--         cong (reflection-inv w conn) (rec-β w f x)
--       ∙ cong (map fst) (conn (f x) .snd (η (x , refl)))
--       ∙ map-β fst (x , refl)))

-- rec-isEquiv : {f : X → Y} (Y-isModal : isModal Y) (f-isConnected : isConnectedMap f)
--   → isEquiv (rec Y-isModal f)
-- rec-isEquiv = {!   !}
--   reflection-isEquiv : {f : X → Y} (w : isModal Y) (conn : isConnectedMap f)
--     → isEquiv (rec w f)
--   reflection-isEquiv {f = f} w conn =
--     isoToIsEquiv
--       (iso (rec w f) (reflection-inv w conn)
--         (reflection-sec w conn) (reflection-ret w conn))

--   opaque
--     precomp-η-isEquivΠ : {Y : ◯ X → Type ℓ} (w : (x◦ : ◯ X) → isModal (Y x◦))
--       → isEquiv (λ (h : (x◦ : ◯ X) → Y x◦) → h ∘ η)
--     precomp-η-isEquivΠ w = isoToIsEquiv (iso (_∘ η) (elim w)
--       (λ k → funExt (elim-β w k))
--       (λ h → η-ext w (funExt (elim-β w (h ∘ η)))))

--   precomp-η-isEquiv : (w : isModal Y) → isEquiv (λ (h : ◯ X → Y) → h ∘ η)
--   precomp-η-isEquiv w = precomp-η-isEquivΠ (λ _ → w)

--   precomp-η-≃ : isModal Y → (◯ X → Y) ≃ (X → Y)
--   precomp-η-≃ w = (_∘ η) , precomp-η-isEquiv w

--   opaque
--     reflection-≃ : {f : X → Y} (w : isModal Y) (conn : isConnectedMap f) → ◯ X ≃ Y
--     reflection-≃ {f = f} w conn = rec w f , reflection-isEquiv w conn

--     reflection-β : {f : X → Y} (w : isModal Y) (conn : isConnectedMap f) (x : X)
--       → equivFun (reflection-≃ w conn) (η x) ≡ f x
--     reflection-β {f = f} w conn = rec-β w f

--   opaque
--     reflection-connected : {f : X → Y} (w : isModal Y)
--       → isEquiv (rec w f) → isConnectedMap f
--     reflection-connected {f = f} w h =
--       subst isConnectedMap (funExt (rec-β w f))
--         (isConnectedMap-∘ₑ (rec w f , h) isConnectedMapη)

-- module _ {X : Type ℓ} {Y : ◯ X → Type ℓ} (w : (x◦ : ◯ X) → isModal (Y x◦)) where
--   private
--     c-connected : isConnectedMap (map-Σ {Y' = Y} η (λ x → idfun (Y (η x))))
--     c-connected =
--       isConnectedMapΣ isConnectedMapη λ x → isEquiv→isConnectedMap (idIsEquiv (Y (η x)))

--   ◯Σ-modal : ◯ (Σ X (Y ∘ η)) ≃ Σ (◯ X) Y
--   ◯Σ-modal = reflection-≃ (isModalΣ isModal◯ w) c-connected

--   ◯Σ-modal-β : (x : X) (y : Y (η x))
--     → equivFun ◯Σ-modal (η (x , y)) ≡ (η x , y)
--   ◯Σ-modal-β x y = reflection-β (isModalΣ isModal◯ w) c-connected (x , y)

IsLex : Type _
IsLex = {X : Type ℓ} {x x' : X} → (◯ (x ≡ x')) ≃ (η x ≡ η x')
  -- {X : Type ℓ} {x x' : X} → isEquiv (rec (isModal◯≡ {X} {η x} {η x'}) (cong η))

-- consequences of lexness
module Lex (lex : IsLex) where
--   opaque
--     ≡-connected : isConnected X → {x y : X} → isConnected (x ≡ y)
--     ≡-connected cX {x} {y} =
--       isOfHLevelRespectEquiv 0 (invEquiv (_ , lex))
--         (isContr→isContrPath cX (η x) (η y))

  -- -- Additional properties of *lex* modalities

  -- module _ (○-lex : ∀ {ℓ} {A : Type ℓ} {a b : A} → (○ (a ≡ b)) ≃ (η○ a ≡ η○ b)) where
  --   ≡-connected : connected A → {x y : A} → connected (x ≡ y)
  --   ≡-connected A-conn = Equiv→is-hlevel 0 ○-lex (Path-is-hlevel 0 A-conn)

  --   PathP-connected : {A : I → Type ℓ} → connected (A i0) → ∀ {x y} → connected (PathP A x y)
  --   PathP-connected {A = A} A-conn {x} {y} =
  --     subst connected (sym (PathP≡Path⁻ A x y)) (≡-connected A-conn)

  isConnectedPathP : {X : I → Type ℓ} → isConnected (X i0) → ∀ {x x'} → isConnected (PathP X x x')
  isConnectedPathP = {!   !}

--   opaque
--     isConnectedPathP : {X : I → Type ℓ} → isConnected (X i0) → ∀ {x x'} → isConnected (PathP X x x')
--     isConnectedPathP {X = X} cX {x} {x'} =
--       subst isConnected (sym (PathP≡Path⁻ X x x')) (≡-connected cX)

  opaque
    isSet◯ : isSet X → isSet (◯ X)
    isSet◯ = {!   !}
--     isSet◯ {X = X} isSetX =
--       elim (λ x◦ → isModalΠ λ x◦' → isProp≡-modal x◦ x◦') λ x →
--       elim (isProp≡-modal (η x)) λ x' →
--       isOfHLevelRespectEquiv 1 (_ , lex) (◯-preservesProp (isSetX x x'))
--       where
--         isProp≡-modal : (x◦ x◦' : ◯ X) → isModal (isProp (x◦ ≡ x◦'))
--         isProp≡-modal x◦ x◦' =
--           isModalΠ λ _ → isModalΠ λ _ → isModal≡ (◯-≡-isModal x◦ x◦')

--   ◯-≡-≃ : {x x' : X} → ◯ (x ≡ x') ≃ (η x ≡ η x')
--   ◯-≡-≃ = _ , lex

  module _ {X Y Z : Type ℓ} {f : X → Z} {g : Y → Z} where
--     private
--       pe : (x : X) (y : Y) → ◯ (f x ≡ g y) ≃ (map f (η x) ≡ map g (η y))
--       pe x y = ◯-≡-≃ ∙ₑ compPathrEquiv (sym (map-β g y)) ∙ₑ compPathlEquiv (map-β f x)

--       Pullback◯-isModal : isModal (Σ[ (x◦ , y◦) ∈ ◯ X × ◯ Y ] (map f x◦ ≡ map g y◦))
--       Pullback◯-isModal =
--         isModalΣ (isModalΣ isModal◯ λ _ → isModal◯) λ _ → ◯-≡-isModal _ _

    pullback-η
      : Σ[ (x , y) ∈ X × Y ] (f x ≡ g y)
      → Σ[ (x◦ , y◦) ∈ ◯ X × ◯ Y ] (map f x◦ ≡ map g y◦)
    pullback-η = {!   !}
--     pullback-η = map-Σ (map-Σ η λ _ → η) λ (x , y) → equivFun (pe x y) ∘ η

--     pullback-η-connected : isConnectedMap pullback-η
--     pullback-η-connected =
--       isConnectedMapΣ
--         (isConnectedMapΣ isConnectedMapη λ _ → isConnectedMapη)
--         (λ (x , y) → isConnectedMap-∘ₑ (pe x y) isConnectedMapη)

    opaque
      ◯-pullback
        : ◯ (Σ[ (x , y) ∈ X × Y ] (f x ≡ g y))
        ≃ (Σ[ (x◦ , y◦) ∈ ◯ X × ◯ Y ] (map f x◦ ≡ map g y◦))
      ◯-pullback = {!   !}
--       ◯-pullback = reflection-≃ Pullback◯-isModal pullback-η-connected

      ◯-pullback-β
        : (u : Σ[ (x , y) ∈ X × Y ] (f x ≡ g y))
        → equivFun ◯-pullback (η u) ≡ pullback-η u
      ◯-pullback-β = {!   !}
--       ◯-pullback-β = reflection-β Pullback◯-isModal pullback-η-connected

      ◯-pullback-β₁ :
        (u : Σ[ (x , y) ∈ X × Y ] (f x ≡ g y))
        → equivFun ◯-pullback (η u) .fst .fst ≡ η (u .fst .fst)
      ◯-pullback-β₁ = {!   !}
--       ◯-pullback-β₁ = cong (fst ∘ fst) ∘ ◯-pullback-β

      ◯-pullback-β₂ :
        (u : Σ[ (x , y) ∈ X × Y ] (f x ≡ g y))
        → equivFun ◯-pullback (η u) .fst .snd ≡ η (u .fst .snd)
      ◯-pullback-β₂ = {!   !}
--       ◯-pullback-β₂ = cong (snd ∘ fst) ∘ ◯-pullback-β
