module Calf.Solver.Nat where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool using (Bool; true; false; if_then_else_; _and_)
open import Cubical.Data.Maybe using (Maybe; just; nothing)
open import Cubical.Data.List using (_++_)
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_; _∸_; _·_)
open import Cubical.Data.Nat.Order using
  (_≤_; isProp≤; zero-≤; ≤-refl; suc-≤-suc; ≤-trans; ≤-+-≤; ≤SumLeft; ≤SumRight;
   ≤-∸-+-cancel)
open import Cubical.Data.Sigma using (fst; snd; _×_)
open import Cubical.Data.Vec using (Vec) renaming ([] to emptyVec; _∷_ to _∷vec_)
open import Cubical.Reflection.Base using (_v∷_; _>>=_; _>>_; _<|>_; varg)
open import Cubical.Tactics.Reflection using (unapply-path)
open import Cubical.Tactics.Reflection.Utilities using (finiteNumberAsTerm)
open import Cubical.Tactics.Reflection.Variables using
  (Vars; appendWithoutRepetition; indexOf)
open import Cubical.Tactics.NatSolver.NatExpression using (Expr; K; ∣; _+'_; _·'_)
open import Cubical.Tactics.NatSolver.HornerForms using (eval)
open import Cubical.Tactics.NatSolver.Solver using (module EqualityToNormalform)

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Reflection hiding (Type)
open import Agda.Builtin.Unit using (⊤)
open import Function using (case_of_)

open EqualityToNormalform renaming (solve to natSolve)

∸-witness : ∀ {m n : ℕ} → (h : m ≤ n) → n ∸ m ≡ fst h
∸-witness {m} {n} h =
  cong fst (isProp≤ ((n ∸ m) , ≤-∸-+-cancel h) h)

natNormRefl :
  ∀ {n : ℕ} (e : Expr n) (xs : Vec ℕ n)
  → eval (normalize e) xs ≡ eval (normalize e) xs
natNormRefl e xs = refl

natRefl : (x : ℕ) → x ≡ x
natRefl x = refl

natCongSuc : (x y : ℕ) → x ≡ y → suc x ≡ suc y
natCongSuc x y p = cong suc p

natCong₂+ :
  (a a′ b b′ : ℕ)
  → a ≡ a′
  → b ≡ b′
  → a + b ≡ a′ + b′
natCong₂+ a a′ b b′ p q = cong₂ _+_ p q

natCong₂· :
  (a a′ b b′ : ℕ)
  → a ≡ a′
  → b ≡ b′
  → a · b ≡ a′ · b′
natCong₂· a a′ b b′ p q = cong₂ _·_ p q

natCong₂∸ :
  (a a′ b b′ : ℕ)
  → a ≡ a′
  → b ≡ b′
  → a ∸ b ≡ a′ ∸ b′
natCong₂∸ a a′ b b′ p q = cong₂ _∸_ p q

natComp :
  (x y z : ℕ)
  → x ≡ y
  → y ≡ z
  → x ≡ z
natComp x y z p q = p ∙ q

finishNatExplicit :
  (lhs lhs′ rhs rhs′ : ℕ)
  → lhs ≡ lhs′
  → lhs′ ≡ rhs′
  → rhs ≡ rhs′
  → lhs ≡ rhs
finishNatExplicit lhs lhs′ rhs rhs′ lhs-step middle rhs-step =
  lhs-step ∙ middle ∙ sym rhs-step

finishLeExplicit :
  (lower lower′ upper upper′ : ℕ)
  → lower ≡ lower′
  → lower′ ≤ upper′
  → upper ≡ upper′
  → lower ≤ upper
finishLeExplicit lower lower′ upper upper′ lower-step middle upper-step =
  subst (λ n → lower ≤ n) (sym upper-step)
    (subst (λ n → n ≤ upper′) (sym lower-step) middle)

leRefl : (m : ℕ) → m ≤ m
leRefl m = ≤-refl

leZero : (n : ℕ) → 0 ≤ n
leZero n = zero-≤

leSuc : (m n : ℕ) → m ≤ n → suc m ≤ suc n
leSuc m n p = suc-≤-suc p

leTrans : (k m n : ℕ) → k ≤ m → m ≤ n → k ≤ n
leTrans k m n p q = ≤-trans p q

lePlus :
  (m n l k : ℕ)
  → m ≤ n
  → l ≤ k
  → m + l ≤ n + k
lePlus m n l k p q = ≤-+-≤ p q

leSumLeft : (n k : ℕ) → n ≤ n + k
leSumLeft n k = ≤SumLeft

leSumRight : (n k : ℕ) → n ≤ k + n
leSumRight n k = ≤SumRight

leWitnessEq : (lower upper : ℕ) → (p : lower ≤ upper) → upper ≡ fst p + lower
leWitnessEq lower upper p = sym (snd p)

private
  record LeFact : Type where
    constructor leFact
    field
      lower : Term
      upper : Term
      proof : Term

  record Rewrite : Type where
    constructor mkRewrite
    field
      term : Term
      step : Term

  isJust : ∀ {A : Type} → Maybe A → Bool
  isJust (just _) = true
  isJust nothing = false
  
  natLit : ℕ → Term
  natLit n = lit (nat n)

  oneTerm : Term
  oneTerm = natLit 1

  zeroTerm : Term
  zeroTerm = natLit 0

  natReflTerm : Term → Term
  natReflTerm t = def (quote natRefl) (t v∷ [])

  visibleTerms : List (Arg Term) → List Term
  visibleTerms [] = []
  visibleTerms (arg (arg-info visible _) t ∷ args) = t ∷ visibleTerms args
  visibleTerms (_ ∷ args) = visibleTerms args

  visible1 : List (Arg Term) → Maybe Term
  visible1 args with visibleTerms args
  ... | t ∷ [] = just t
  ... | _ = nothing

  visible2 : List (Arg Term) → Maybe (Term × Term)
  visible2 args with visibleTerms args
  ... | x ∷ y ∷ [] = just (x , y)
  ... | _ = nothing

  viewNamed2 : Name → Term → Maybe (Term × Term)
  viewNamed2 nm (def f args) with primQNameEquality nm f
  ... | true = visible2 args
  ... | false = nothing
  viewNamed2 _ _ = nothing

  view+ : Term → Maybe (Term × Term)
  view+ = viewNamed2 (quote _+_)

  view· : Term → Maybe (Term × Term)
  view· = viewNamed2 (quote _·_)

  view∸ : Term → Maybe (Term × Term)
  view∸ = viewNamed2 (quote _∸_)

  viewZero : Term → Bool
  viewZero (lit (nat zero)) = true
  viewZero (con (quote zero) []) = true
  viewZero _ = false

  viewSuc : Term → Maybe Term
  viewSuc (lit (nat (suc n))) = just (natLit n)
  viewSuc (con (quote suc) args) = visible1 args
  viewSuc t with view+ t
  ... | just (lit (nat (suc n)) , x) = just (def (quote _+_) (natLit n v∷ x v∷ []))
  ... | _ = nothing

  expandMulByNat : ℕ → Term → Term
  expandMulByNat zero x = zeroTerm
  expandMulByNat (suc n) x = def (quote _+_) (x v∷ expandMulByNat n x v∷ [])

  viewLiteralMul : Term → Maybe Term
  viewLiteralMul t with view· t
  ... | just (lit (nat k) , x) = just (expandMulByNat k x)
  ... | _ = nothing

  termEq : Term → Term → TC Bool
  termEq x y =
    do x′ ← normalise x
       y′ ← normalise y
       returnTC (isJust (indexOf x′ (y′ ∷ [])))

  mk≤-trans : Term → Term → Term → Term → Term → Term
  mk≤-trans lower middle upper p q =
    def (quote leTrans)
      (lower v∷ middle v∷ upper v∷ p v∷ q v∷ [])

  mk≤-+-≤ : Term → Term → Term → Term → Term → Term → Term
  mk≤-+-≤ l₁ u₁ l₂ u₂ p q =
    def (quote lePlus)
      (l₁ v∷ u₁ v∷ l₂ v∷ u₂ v∷ p v∷ q v∷ [])

  mapMaybeTerm : (Term → Term) → Maybe Term → Maybe Term
  mapMaybeTerm f (just t) = just (f t)
  mapMaybeTerm f nothing = nothing

  returnMap : (Term → Term) → TC (Maybe Term) → TC (Maybe Term)
  returnMap f tc =
    tc >>= λ where
      (just t) → returnTC (just (f t))
      nothing → returnTC nothing

  findDirect : Term → Term → List LeFact → TC (Maybe Term)
  findDirect lower upper [] = returnTC nothing
  findDirect lower upper (leFact lower′ upper′ proof ∷ facts) =
    do sameLower ← termEq lower lower′
       sameUpper ← termEq upper upper′
       if sameLower and sameUpper
         then returnTC (just proof)
         else findDirect lower upper facts

  mutual
    synth≤ : ℕ → List LeFact → Term → Term → TC (Maybe Term)
    synth≤ zero facts lower upper = findDirect lower upper facts
    synth≤ (suc fuel) facts lower upper =
      findDirect lower upper facts >>= λ where
        (just proof) → returnTC (just proof)
        nothing → tryRefl fuel facts lower upper

    tryRefl : ℕ → List LeFact → Term → Term → TC (Maybe Term)
    tryRefl fuel facts lower upper =
      termEq lower upper >>= λ where
        true → returnTC (just (def (quote leRefl) (lower v∷ [])))
        false → tryZero fuel facts lower upper

    tryZero : ℕ → List LeFact → Term → Term → TC (Maybe Term)
    tryZero fuel facts lower upper with viewZero lower
    ... | true = returnTC (just (def (quote leZero) (upper v∷ [])))
    ... | false = tryLiteralMul fuel facts lower upper

    tryLiteralMul : ℕ → List LeFact → Term → Term → TC (Maybe Term)
    tryLiteralMul fuel facts lower upper with viewLiteralMul upper
    ... | just upper′ = synth≤ fuel facts lower upper′
    ... | nothing = trySuc fuel facts lower upper

    trySuc : ℕ → List LeFact → Term → Term → TC (Maybe Term)
    trySuc fuel facts lower upper with viewSuc lower | viewSuc upper
    ... | just lower′ | just upper′ =
      returnMap (λ p → def (quote leSuc) (lower′ v∷ upper′ v∷ p v∷ []))
        (synth≤ fuel facts lower′ upper′)
    ... | _ | _ = trySum fuel facts lower upper

    trySum : ℕ → List LeFact → Term → Term → TC (Maybe Term)
    trySum fuel facts lower upper with view+ upper
    ... | just (u₁ , u₂) =
      termEq lower u₁ >>= λ where
        true → returnTC (just (def (quote leSumLeft) (u₁ v∷ u₂ v∷ [])))
        false →
          termEq lower u₂ >>= λ where
            true → returnTC (just (def (quote leSumRight) (u₂ v∷ u₁ v∷ [])))
            false →
              case view+ lower of λ where
                (just _) → tryPlus fuel facts lower upper
                nothing →
                  case viewSuc lower of λ where
                    (just _) → trySucPlus fuel facts lower upper
                    nothing → tryTrans fuel facts lower upper facts
    ... | nothing = tryPlus fuel facts lower upper

    tryPlus : ℕ → List LeFact → Term → Term → TC (Maybe Term)
    tryPlus fuel facts lower upper with view+ lower | view+ upper
    ... | just (l₁ , l₂) | just (u₁ , u₂) =
      synth≤ fuel facts l₁ u₁ >>= λ where
        (just p₁) →
          synth≤ fuel facts l₂ u₂ >>= λ where
            (just p₂) → returnTC (just (mk≤-+-≤ l₁ u₁ l₂ u₂ p₁ p₂))
            nothing → trySucPlus fuel facts lower upper
        nothing → trySucPlus fuel facts lower upper
    ... | _ | _ = trySucPlus fuel facts lower upper

    trySucPlus : ℕ → List LeFact → Term → Term → TC (Maybe Term)
    trySucPlus fuel facts lower upper with viewSuc lower | view+ upper
    ... | just lower′ | just (u₁ , u₂) =
      synth≤ fuel facts oneTerm u₁ >>= λ where
        (just p₁) →
          synth≤ fuel facts lower′ u₂ >>= λ where
            (just p₂) → returnTC (just (mk≤-+-≤ oneTerm u₁ lower′ u₂ p₁ p₂))
            nothing → tryTrans fuel facts lower upper facts
        nothing → tryTrans fuel facts lower upper facts
    ... | _ | _ = tryTrans fuel facts lower upper facts

    tryTrans : ℕ → List LeFact → Term → Term → List LeFact → TC (Maybe Term)
    tryTrans fuel facts lower upper [] = returnTC nothing
    tryTrans fuel facts lower upper (leFact factLower factUpper factProof ∷ rest) =
      termEq lower factLower >>= λ where
        true →
          synth≤ fuel facts factUpper upper >>= λ where
            (just q) → returnTC (just (mk≤-trans lower factUpper upper factProof q))
            nothing → tryTransRight fuel facts lower upper rest factLower factUpper factProof
        false → tryTransRight fuel facts lower upper rest factLower factUpper factProof

    tryTransRight :
      ℕ → List LeFact → Term → Term → List LeFact → Term → Term → Term → TC (Maybe Term)
    tryTransRight fuel facts lower upper rest factLower factUpper factProof =
      termEq upper factUpper >>= λ where
        true →
          synth≤ fuel facts lower factLower >>= λ where
            (just p) → returnTC (just (mk≤-trans lower factLower upper p factProof))
            nothing → tryTrans fuel facts lower upper rest
        false → tryTrans fuel facts lower upper rest

  parse≤Type : Term → Maybe (Term × Term)
  parse≤Type (def f args) with primQNameEquality f (quote _≤_)
  ... | true = visible2 args
  ... | false = nothing
  parse≤Type _ = nothing

  parseSingleAssumption : Term → TC (Maybe Term)
  parseSingleAssumption p =
    (do ty ← inferType p
        case parse≤Type ty of λ where
          (just _) → returnTC (just p)
          nothing →
            do ty′ ← normalise ty
               case parse≤Type ty′ of λ where
                 (just _) → returnTC (just p)
                 nothing → returnTC nothing)
    <|>
    returnTC nothing

  viewPair : Term → Maybe (Term × Term)
  viewPair (con c args) with primQNameEquality c (quote _,_)
  ... | true = visible2 args
  ... | false = nothing
  viewPair _ = nothing

  assumptionFuel : ℕ
  assumptionFuel = 50

  mutual
    parseAssumptionsFuel : ℕ → Term → TC (List Term)
    parseAssumptionsFuel zero t =
      typeError (strErr "Nat solver assumption parser ran out of fuel at: "
        ∷ termErr t ∷ [])
    parseAssumptionsFuel (suc fuel) t =
      parseSingleAssumption t >>= λ where
        (just p) → returnTC (p ∷ [])
        nothing → parseAssumptionBundle fuel t

    parseAssumptionBundle : ℕ → Term → TC (List Term)
    parseAssumptionBundle fuel t with viewPair t
    ... | just (p , q) =
      do ps ← parseAssumptionsFuel fuel p
         qs ← parseAssumptionsFuel fuel q
         returnTC (ps ++ qs)
    ... | nothing =
      typeError (strErr "Expected Nat solver assumptions as a ≤ proof or tuple of ≤ proofs, got: "
        ∷ termErr t ∷ [])

  parseAssumptions : Term → TC (List Term)
  parseAssumptions = parseAssumptionsFuel assumptionFuel

  collectFact : Term → Term → List LeFact → TC (List LeFact)
  collectFact p ty facts =
    case parse≤Type ty of λ where
      (just (lower , upper)) →
        do lower ← normalise lower
           upper ← normalise upper
           returnTC (leFact lower upper p ∷ facts)
      nothing →
        typeError (strErr "Expected a Cubical Nat ≤ assumption, got type: "
          ∷ termErr ty ∷ [])

  collectFacts : List Term → TC (List LeFact)
  collectFacts [] = returnTC []
  collectFacts (p ∷ ps) =
    do ty ← inferType p
       facts ← collectFacts ps
       collectFact p ty facts
         <|>
         (do ty′ ← normalise ty
             collectFact p ty′ facts)

  cong₂+Term : Term → Term → Term → Term → Term → Term → Term
  cong₂+Term x x′ y y′ p q =
    def (quote natCong₂+)
      (x v∷ x′ v∷ y v∷ y′ v∷ p v∷ q v∷ [])

  cong₂·Term : Term → Term → Term → Term → Term → Term → Term
  cong₂·Term x x′ y y′ p q =
    def (quote natCong₂·)
      (x v∷ x′ v∷ y v∷ y′ v∷ p v∷ q v∷ [])

  cong₂∸Term : Term → Term → Term → Term → Term → Term → Term
  cong₂∸Term x x′ y y′ p q =
    def (quote natCong₂∸)
      (x v∷ x′ v∷ y v∷ y′ v∷ p v∷ q v∷ [])

  congSucTerm : Term → Term → Term → Term
  congSucTerm x x′ p =
    def (quote natCongSuc) (x v∷ x′ v∷ p v∷ [])

  compTerm : Term → Term → Term → Term → Term → Term
  compTerm x y z p q =
    def (quote natComp) (x v∷ y v∷ z v∷ p v∷ q v∷ [])

  fstTerm : Term → Term
  fstTerm p = def (quote fst) (p v∷ [])

  leWitnessEqTerm : Term → Term → Term → Term
  leWitnessEqTerm lower upper proof =
    def (quote leWitnessEq) (lower v∷ upper v∷ proof v∷ [])

  rewriteFuel : ℕ
  rewriteFuel = 50

  synthFuel : ℕ
  synthFuel = 8

  rewriteTerm : ℕ → List LeFact → Term → TC Rewrite
  rewriteTerm zero facts t =
    typeError (strErr "Nat solver preprocessing ran out of fuel at: "
      ∷ termErr t ∷ [])
  rewriteTerm (suc fuel) facts t with view+ t
  ... | just (x , y) =
    do rx ← rewriteTerm fuel facts x
       ry ← rewriteTerm fuel facts y
       let x′ = Rewrite.term rx
       let y′ = Rewrite.term ry
       let px = Rewrite.step rx
       let py = Rewrite.step ry
       returnTC
         (mkRewrite
           (def (quote _+_) (x′ v∷ y′ v∷ []))
           (cong₂+Term x x′ y y′ px py))
  ... | nothing with view· t
  ... | just (x , y) =
    do rx ← rewriteTerm fuel facts x
       ry ← rewriteTerm fuel facts y
       let x′ = Rewrite.term rx
       let y′ = Rewrite.term ry
       let px = Rewrite.step rx
       let py = Rewrite.step ry
       returnTC
         (mkRewrite
           (def (quote _·_) (x′ v∷ y′ v∷ []))
           (cong₂·Term x x′ y y′ px py))
  ... | nothing with view∸ t
  ... | just (upper , lower) =
    do rUpper ← rewriteTerm fuel facts upper
       rLower ← rewriteTerm fuel facts lower
       let upper′ = Rewrite.term rUpper
       let lower′ = Rewrite.term rLower
       let originalMinus = def (quote _∸_) (upper v∷ lower v∷ [])
       let rewrittenMinus = def (quote _∸_) (upper′ v∷ lower′ v∷ [])
       let childStep =
             cong₂∸Term upper upper′ lower lower′
               (Rewrite.step rUpper)
               (Rewrite.step rLower)
       guard ← synth≤ synthFuel facts lower′ upper′
       case guard of λ where
         (just proof) →
           let witness = fstTerm proof in
           returnTC
             (mkRewrite witness
               (compTerm originalMinus rewrittenMinus witness
                 childStep
                 (def (quote ∸-witness) (proof v∷ []))))
         nothing →
           typeError
             (strErr "Could not synthesize a checked ≤ guard for subtraction: "
             ∷ termErr lower′
             ∷ strErr " ≤ "
             ∷ termErr upper′
             ∷ [])
  ... | nothing with viewSuc t
  ... | just x =
    do rx ← rewriteTerm fuel facts x
       let x′ = Rewrite.term rx
       let step = Rewrite.step rx
       returnTC (mkRewrite (con (quote suc) (x′ v∷ [])) (congSucTerm x x′ step))
  ... | nothing = returnTC (mkRewrite t (natReflTerm t))

  findUpperRewrite : Term → List LeFact → TC (Maybe Rewrite)
  findUpperRewrite t [] = returnTC nothing
  findUpperRewrite t (leFact lower upper proof ∷ facts) =
    termEq t upper >>= λ where
      true →
        returnTC
          (just
            (mkRewrite
              (def (quote _+_) (fstTerm proof v∷ lower v∷ []))
              (leWitnessEqTerm lower upper proof)))
      false → findUpperRewrite t facts

  mutual
    rewriteBy≤Facts : ℕ → List LeFact → Term → TC Rewrite
    rewriteBy≤Facts zero facts t =
      typeError (strErr "Nat solver ≤-assumption rewriting ran out of fuel at: "
        ∷ termErr t ∷ [])
    rewriteBy≤Facts (suc fuel) facts t =
      findUpperRewrite t facts >>= λ where
        (just r) → returnTC r
        nothing → rewriteBy≤Facts′ fuel facts t

    rewriteBy≤Facts′ : ℕ → List LeFact → Term → TC Rewrite
    rewriteBy≤Facts′ fuel facts t with view+ t
    ... | just (x , y) =
      do rx ← rewriteBy≤Facts fuel facts x
         ry ← rewriteBy≤Facts fuel facts y
         let x′ = Rewrite.term rx
         let y′ = Rewrite.term ry
         let px = Rewrite.step rx
         let py = Rewrite.step ry
         returnTC
           (mkRewrite
             (def (quote _+_) (x′ v∷ y′ v∷ []))
             (cong₂+Term x x′ y y′ px py))
    ... | nothing with view· t
    ... | just (x , y) =
      do rx ← rewriteBy≤Facts fuel facts x
         ry ← rewriteBy≤Facts fuel facts y
         let x′ = Rewrite.term rx
         let y′ = Rewrite.term ry
         let px = Rewrite.step rx
         let py = Rewrite.step ry
         returnTC
           (mkRewrite
             (def (quote _·_) (x′ v∷ y′ v∷ []))
             (cong₂·Term x x′ y y′ px py))
    ... | nothing with view∸ t
    ... | just (x , y) =
      do rx ← rewriteBy≤Facts fuel facts x
         ry ← rewriteBy≤Facts fuel facts y
         let x′ = Rewrite.term rx
         let y′ = Rewrite.term ry
         let px = Rewrite.step rx
         let py = Rewrite.step ry
         returnTC
           (mkRewrite
             (def (quote _∸_) (x′ v∷ y′ v∷ []))
             (cong₂∸Term x x′ y y′ px py))
    ... | nothing with viewSuc t
    ... | just x =
      do rx ← rewriteBy≤Facts fuel facts x
         let x′ = Rewrite.term rx
         let step = Rewrite.step rx
         returnTC (mkRewrite (con (quote suc) (x′ v∷ [])) (congSucTerm x x′ step))
    ... | nothing = returnTC (mkRewrite t (natReflTerm t))

  ExprBuilder : Type
  ExprBuilder = Vars → TC Term

  asVariable : Term → TC (ExprBuilder × Vars)
  asVariable t =
    returnTC
      ((λ vars →
        case indexOf t vars of λ where
          (just n) → returnTC (con (quote ∣) (finiteNumberAsTerm (just n) v∷ []))
          nothing →
            typeError
              (strErr "Internal error: Nat solver variable was not collected: "
              ∷ termErr t
              ∷ []))
      , t ∷ [])

  expressionFuel : ℕ
  expressionFuel = 50

  buildExpression : ℕ → Term → TC (ExprBuilder × Vars)
  buildExpression zero t =
    typeError (strErr "Nat solver expression parser ran out of fuel at: "
      ∷ termErr t ∷ [])
  buildExpression (suc fuel) t with view+ t
  ... | just (x , y) =
    do rx ← buildExpression fuel x
       ry ← buildExpression fuel y
       returnTC
         ((λ vars →
           do x ← fst rx vars
              y ← fst ry vars
              returnTC (con (quote _+'_) (x v∷ y v∷ [])))
         , appendWithoutRepetition (snd rx) (snd ry))
  ... | nothing with view· t
  ... | just (x , y) =
    do rx ← buildExpression fuel x
       ry ← buildExpression fuel y
       returnTC
         ((λ vars →
           do x ← fst rx vars
              y ← fst ry vars
              returnTC (con (quote _·'_) (x v∷ y v∷ [])))
         , appendWithoutRepetition (snd rx) (snd ry))
  ... | nothing with view∸ t
  ... | just _ =
    typeError (strErr "Internal error: subtraction remained after preprocessing: "
      ∷ termErr t ∷ [])
  ... | nothing with viewZero t
  ... | true = returnTC ((λ _ → returnTC (con (quote K) (zeroTerm v∷ []))) , [])
  ... | false with viewSuc t
  ... | just x =
    do rx ← buildExpression fuel x
       returnTC
         ((λ vars →
           do x ← fst rx vars
              returnTC
                (con (quote _+'_)
                  (con (quote K) (oneTerm v∷ []) v∷ x v∷ [])))
         , snd rx)
  ... | nothing with t
  ... | lit (nat n) = returnTC ((λ _ → returnTC (con (quote K) (natLit n v∷ []))) , [])
  ... | _ = asVariable t

  toNatExpression : Term → Term → TC (Term × Term × Vars)
  toNatExpression lhs rhs =
    do rx ← buildExpression expressionFuel lhs
       ry ← buildExpression expressionFuel rhs
       let vars = appendWithoutRepetition (snd rx) (snd ry)
       lhsExpr ← fst rx vars
       rhsExpr ← fst ry vars
       returnTC (lhsExpr , rhsExpr , vars)

  variableVector : Vars → Term
  variableVector [] = con (quote emptyVec) []
  variableVector (t ∷ ts) =
    con (quote _∷vec_) (t v∷ variableVector ts v∷ [])

  natSolverCall : Term → Term → Vars → Term
  natSolverCall lhs rhs vars =
    let xs = variableVector vars in
    def (quote natSolve)
      (varg lhs
      ∷ varg rhs
      ∷ varg xs
      ∷ varg (def (quote natNormRefl) (lhs v∷ xs v∷ []))
      ∷ [])

  solveNatGoalProof : List LeFact → Term → TC Term
  solveNatGoalProof leFacts goal =
    do boundary ← unapply-path goal
       case boundary of λ where
         nothing →
           case parse≤Type goal of λ where
             (just (lower , upper)) →
               do lower ← normalise lower
                  upper ← normalise upper
                  proof? ← synth≤ synthFuel leFacts lower upper
                  case proof? of λ where
                    (just proof) →
                      checkType proof goal
                    nothing →
                      do lowerRewrite ← rewriteTerm rewriteFuel leFacts lower
                         upperRewrite ← rewriteTerm rewriteFuel leFacts upper
                         lowerAfter∸ ← normalise (Rewrite.term lowerRewrite)
                         upperAfter∸ ← normalise (Rewrite.term upperRewrite)
                         lower≤Rewrite ← rewriteBy≤Facts rewriteFuel leFacts lowerAfter∸
                         upper≤Rewrite ← rewriteBy≤Facts rewriteFuel leFacts upperAfter∸
                         lower′ ← normalise (Rewrite.term lower≤Rewrite)
                         upper′ ← normalise (Rewrite.term upper≤Rewrite)
                         proof? ← synth≤ synthFuel leFacts lower′ upper′
                         case proof? of λ where
                           (just middle) →
                             let lowerStep =
                                   compTerm lower lowerAfter∸ lower′
                                     (Rewrite.step lowerRewrite)
                                     (Rewrite.step lower≤Rewrite)
                             in
                             let upperStep =
                                   compTerm upper upperAfter∸ upper′
                                     (Rewrite.step upperRewrite)
                                     (Rewrite.step upper≤Rewrite)
                             in
                             checkType
                               (def (quote finishLeExplicit)
                                 (lower v∷ lower′ v∷ upper v∷ upper′ v∷
                                  lowerStep v∷ middle v∷ upperStep v∷ []))
                               goal
                           nothing →
                             typeError
                               (strErr "Could not synthesize a checked ≤ proof: "
                               ∷ termErr lower′
                               ∷ strErr " ≤ "
                               ∷ termErr upper′
                               ∷ [])
             nothing →
               typeError (strErr "Expected a Cubical Nat path or ≤ goal, got: "
                 ∷ termErr goal ∷ [])
         (just (dom , lhs , rhs)) →
           do unify dom (def (quote ℕ) [])
              lhs ← normalise lhs
              rhs ← normalise rhs
              lhsRewrite ← rewriteTerm rewriteFuel leFacts lhs
              rhsRewrite ← rewriteTerm rewriteFuel leFacts rhs
              lhsAfter∸ ← normalise (Rewrite.term lhsRewrite)
              rhsAfter∸ ← normalise (Rewrite.term rhsRewrite)
              lhs≤Rewrite ← rewriteBy≤Facts rewriteFuel leFacts lhsAfter∸
              rhs≤Rewrite ← rewriteBy≤Facts rewriteFuel leFacts rhsAfter∸
              lhs′ ← normalise (Rewrite.term lhs≤Rewrite)
              rhs′ ← normalise (Rewrite.term rhs≤Rewrite)
              parsed ← toNatExpression lhs′ rhs′
              let lhsExpr = fst parsed
              let rhsExpr = fst (snd parsed)
              let vars = snd (snd parsed)
              let middle = natSolverCall lhsExpr rhsExpr vars
              let lhsStep =
                    compTerm lhs lhsAfter∸ lhs′
                      (Rewrite.step lhsRewrite)
                      (Rewrite.step lhs≤Rewrite)
              let rhsStep =
                    compTerm rhs rhsAfter∸ rhs′
                      (Rewrite.step rhsRewrite)
                      (Rewrite.step rhs≤Rewrite)
              proof ← checkType
                (def (quote finishNatExplicit)
                  (lhs v∷ lhs′ v∷ rhs v∷ rhs′ v∷
                   lhsStep v∷ middle v∷ rhsStep v∷ []))
                goal
              returnTC proof

  solveNatProofFromFacts : List LeFact → Term → TC Term
  solveNatProofFromFacts leFacts hole =
    do goal ← inferType hole
       ((solveNatGoalProof leFacts goal)
         <|>
        (do goal′ ← normalise goal
            solveNatGoalProof leFacts goal′))

  solveNatFromFacts : List LeFact → Term → TC ⊤
  solveNatFromFacts leFacts hole =
    do proof ← solveNatProofFromFacts leFacts hole
       unify hole proof

  debugNatFromFacts : List LeFact → Term → TC ⊤
  debugNatFromFacts leFacts hole =
    do proof ← solveNatProofFromFacts leFacts hole
       typeError (strErr "Generated Nat solver proof term:\n"
         ∷ termErr proof ∷ [])

macro
  solveNat : Term → Term → TC ⊤
  solveNat assumptions hole =
    do assumptionTerms ← parseAssumptions assumptions
       facts ← collectFacts assumptionTerms
       solveNatFromFacts facts hole

  solveNat0 : Term → TC ⊤
  solveNat0 hole =
    solveNatFromFacts [] hole

  debugSolveNat : Term → Term → TC ⊤
  debugSolveNat assumptions hole =
    do assumptionTerms ← parseAssumptions assumptions
       facts ← collectFacts assumptionTerms
       debugNatFromFacts facts hole

  debugSolveNat0 : Term → TC ⊤
  debugSolveNat0 hole =
    debugNatFromFacts [] hole
