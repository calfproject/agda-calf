module Calf.Value.Closed.Base where

open import Calf.Core.Abstract
open import Calf.Value

data ● (X : 𝒱) : 𝒱 where
  η• : (x : X) → ● X
  ∗ : (abs : ⟨ ABS ⟩) → ● X
  law : (x : X) (abs : ⟨ ABS ⟩) → η• x ≡ ∗ abs

ind : {X : 𝒱} (R : ● X → 𝒱)
  → (η•-case : (x : X) → R (η• x))
  → (∗-case : (abs : ⟨ ABS ⟩) → R (∗ abs))
  → (law-case : (x : X) (abs : ⟨ ABS ⟩) → PathP (λ i → R (law x abs i)) (η•-case x) (∗-case abs))
  → (x• : ● X) → R x•
ind R η•-case ∗-case law-case (η• x) = η•-case x
ind R η•-case ∗-case law-case (∗ abs) = ∗-case abs
ind R η•-case ∗-case law-case (law x abs i) = law-case x abs i

map : {X Y : 𝒱} → (X → Y) → ● X → ● Y
map f (η• x) = η• (f x)
map f (∗ abs) = ∗ abs
map f (law x abs i) = law (f x) abs i

●-path-to-star : {X : 𝒱} → (abs : ⟨ ABS ⟩) → (x : ● X) → x ≡ ∗ abs
●-path-to-star abs (η• x) = law x abs
●-path-to-star abs (∗ q) = cong ∗ (str ABS q abs)
●-path-to-star abs (law x q i) j =
  hcomp
    (λ k → λ
      { (i = i0) → law x abs (j ∧ k)
      ; (i = i1) → law x (str ABS q abs j) k
      ; (j = i0) → law x q (i ∧ k)
      ; (j = i1) → law x abs k })
    (η• x)

join : {X : 𝒱} → ● (● X) → ● X
join (η• x) = x
join (∗ abs) = ∗ abs
join (law x abs i) = ●-path-to-star abs x i

bind : {X Y : 𝒱} → ● X → (X → ● Y) → ● Y
bind x• k = join (map k x•)

●-isContr : {X : 𝒱} → ⟨ ABS ⟩ → isContr (● X)
●-isContr abs .fst = ∗ abs
●-isContr abs .snd x = sym (●-path-to-star abs x)

●-isProp : {X : 𝒱} → ⟨ ABS ⟩ → isProp (● X)
●-isProp abs = isContr→isProp (●-isContr abs)

isModal : 𝒱 → 𝒱
isModal X = isEquiv (η• {X})

isConnected : 𝒱 → 𝒱
isConnected X = isContr (● X)

isModalMap : {X Y : 𝒱} → (X → Y) → 𝒱
isModalMap {Y = Y} f = (y : Y) → isModal (fiber f y)

isConnectedMap : {X Y : 𝒱} → (X → Y) → 𝒱
isConnectedMap {Y = Y} f = (y : Y) → isConnected (fiber f y)

isModal+isConnected→isContr : {X : 𝒱} → isModal X → isConnected X → isContr X
isModal+isConnected→isContr X-modal X-connected =
  isOfHLevelRespectEquiv 0 (invEquiv (η• , X-modal)) X-connected

isModal+isConnected→isEquiv
  : {X Y : 𝒱} {f : X → Y}
  → isModalMap f
  → isConnectedMap f
  → isEquiv f
isModal+isConnected→isEquiv f-modal f-connected .equiv-proof y =
  isModal+isConnected→isContr (f-modal y) (f-connected y)

𝒱• : 𝒱₁
𝒱• = TypeWithStr _ isModal

η-isEquiv : {X : 𝒱} → isEquiv (η• {● X})
η-isEquiv = isoToIsEquiv (iso η• join sec ret)
  where
  ret : {X : 𝒱} → (x : ● X) → join (η• x) ≡ x
  ret x = refl

  sec : {X : 𝒱} → (x : ● (● X)) → η• (join x) ≡ x
  sec (η• x) = refl
  sec (∗ abs) = law (∗ abs) abs
  sec (law x abs i) =
    isProp→PathP
      (λ i → isProp→isSet (●-isProp {X = ● _} abs)
        (η• (●-path-to-star abs x i))
        (law x abs i))
      refl
      (law (∗ abs) abs)
      i
