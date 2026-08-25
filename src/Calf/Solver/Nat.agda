-- Eventually this should be replaced by something like Rocq's lia
module Calf.Solver.Nat where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (case_of_)
open import Cubical.Data.Bool using (Bool; true; false; if_then_else_; _and_)
open import Cubical.Data.Maybe using (Maybe; just; nothing)
open import Cubical.Data.List using (_++_)
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_; _∸_; _·_)
open import Cubical.Data.Nat.Order using (_≤_)
open import Cubical.Data.Sigma using (fst; snd; _×_)
open import Cubical.Data.Vec using () renaming ([] to emptyVec; _∷_ to _∷vec_)
open import Cubical.Reflection.Base using (_v∷_; _>>=_; _>>_; _<|>_; varg)
open import Cubical.Tactics.Reflection using (unapply-path)
open import Cubical.Tactics.Reflection.Utilities using (finiteNumberAsTerm)
open import Cubical.Tactics.Reflection.Variables using
  (Vars; indexOf)
open import Cubical.Tactics.NatSolver.NatExpression using (K; ∣; _+'_; _·'_)
open import Cubical.Tactics.NatSolver.Solver using (module EqualityToNormalform)

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using () renaming (_==_ to _=ℕ_)
open import Agda.Builtin.Reflection using
  ( Name; Term; Arg; Literal; TC
  ; var; con; def; lit; meta
  ; nat; name
  ; primQNameEquality; primMetaEquality
  ; normalise; returnTC; typeError; strErr; termErr
  ; inferType; checkType; unify
  )
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤)

open EqualityToNormalform renaming (solve to natSolve)
open import Calf.Solver.Nat.Arithmetic public

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
  visibleTerms (varg t ∷ args) = t ∷ visibleTerms args
  visibleTerms (_ ∷ args) = visibleTerms args

  visible2 : List (Arg Term) → Maybe (Term × Term)
  visible2 args with visibleTerms args
  ... | x ∷ y ∷ [] = just (x , y)
  ... | _ = nothing

  viewDef : Name → Term → Maybe (List Term)
  viewDef nm (def f args) with primQNameEquality nm f
  ... | true = just (visibleTerms args)
  ... | false = nothing
  viewDef _ _ = nothing

  view2 : Name → Term → Maybe (Term × Term)
  view2 nm t with viewDef nm t
  ... | just (x ∷ y ∷ []) = just (x , y)
  ... | _ = nothing

  view+ : Term → Maybe (Term × Term)
  view+ = view2 (quote _+_)

  view· : Term → Maybe (Term × Term)
  view· = view2 (quote _·_)

  view∸ : Term → Maybe (Term × Term)
  view∸ = view2 (quote _∸_)

  viewZero : Term → Bool
  viewZero (lit (nat zero)) = true
  viewZero (con (quote zero) []) = true
  viewZero _ = false

  viewSuc : Term → Maybe Term
  viewSuc (lit (nat (suc n))) = just (natLit n)
  viewSuc (con (quote suc) args) with visibleTerms args
  ... | t ∷ [] = just t
  ... | _ = nothing
  viewSuc t with view+ t
  ... | just (lit (nat (suc n)) , x) = just (def (quote _+_) (natLit n v∷ x v∷ []))
  ... | _ = nothing

  termEq : Term → Term → TC Bool
  termEq x y =
    do x′ ← normalise x
       y′ ← normalise y
       returnTC (isJust (indexOf x′ (y′ ∷ [])))

  literalShapeEq : Literal → Literal → Bool
  literalShapeEq (nat m) (nat n) = m =ℕ n
  literalShapeEq (name m) (name n) = primQNameEquality m n
  literalShapeEq (meta m) (meta n) = primMetaEquality m n
  literalShapeEq _ _ = false

  mutual
    termShapeEq : Term → Term → Bool
    termShapeEq (var i args) (var j args′) =
      (i =ℕ j) and argListShapeEq args args′
    termShapeEq (con c args) (con c′ args′) =
      primQNameEquality c c′ and argListShapeEq args args′
    termShapeEq (def f args) (def f′ args′) =
      primQNameEquality f f′ and argListShapeEq args args′
    termShapeEq (lit l) (lit l′) = literalShapeEq l l′
    termShapeEq (meta m args) (meta m′ args′) =
      primMetaEquality m m′ and argListShapeEq args args′
    termShapeEq _ _ = false

    argListShapeEq : List (Arg Term) → List (Arg Term) → Bool
    argListShapeEq [] [] = true
    argListShapeEq [] (varg _ ∷ _) = false
    argListShapeEq [] (_ ∷ args′) = argListShapeEq [] args′
    argListShapeEq (varg _ ∷ _) [] = false
    argListShapeEq (_ ∷ args) [] = argListShapeEq args []
    argListShapeEq (varg t ∷ args)
                   (varg u ∷ args′) =
      termShapeEq t u and argListShapeEq args args′
    argListShapeEq (a@(varg _) ∷ args) (_ ∷ args′) =
      argListShapeEq (a ∷ args) args′
    argListShapeEq (_ ∷ args) args′ = argListShapeEq args args′

  mk≤-trans : Term → Term → Term → Term → Term → Term
  mk≤-trans lower middle upper p q =
    def (quote leTrans)
      (lower v∷ middle v∷ upper v∷ p v∷ q v∷ [])

  mk≤-+-≤ : Term → Term → Term → Term → Term → Term → Term
  mk≤-+-≤ l₁ u₁ l₂ u₂ p q =
    def (quote lePlus)
      (l₁ v∷ u₁ v∷ l₂ v∷ u₂ v∷ p v∷ q v∷ [])

  returnMap : (Term → Term) → TC (Maybe Term) → TC (Maybe Term)
  returnMap f tc =
    tc >>= λ where
      (just t) → returnTC (just (f t))
      nothing → returnTC nothing

  sumTerms : List Term → Term
  sumTerms [] = zeroTerm
  sumTerms (t ∷ []) = t
  sumTerms (t ∷ ts) = def (quote _+_) (t v∷ sumTerms ts v∷ [])

  expressionFuel : ℕ
  expressionFuel = 50

  addendsFuel : ℕ → Term → List Term
  addendsFuel zero t = t ∷ []
  addendsFuel (suc fuel) t with viewZero t
  ... | true = []
  ... | false with view+ t
  ... | just (x , y) = addendsFuel fuel x ++ addendsFuel fuel y
  ... | nothing with viewSuc t
  ... | just x = oneTerm ∷ addendsFuel fuel x
  ... | nothing = t ∷ []

  addends : Term → List Term
  addends = addendsFuel expressionFuel

  removeAddend : Term → List Term → TC (Maybe (List Term))
  removeAddend x [] = returnTC nothing
  removeAddend x (y ∷ ys) =
    termEq x y >>= λ where
      true → returnTC (just ys)
      false →
        removeAddend x ys >>= λ where
          (just ys′) → returnTC (just (y ∷ ys′))
          nothing → returnTC nothing

  removeAddends : List Term → List Term → TC (Maybe (List Term))
  removeAddends [] upper = returnTC (just upper)
  removeAddends (x ∷ xs) upper =
    removeAddend x upper >>= λ where
      (just upper′) → removeAddends xs upper′
      nothing → returnTC nothing

  ExprBuilder : Type
  ExprBuilder = Vars → TC Term

  variableVector : Vars → Term
  variableVector [] = con (quote emptyVec) []
  variableVector (t ∷ ts) =
    con (quote _∷vec_) (t v∷ variableVector ts v∷ [])

  indexOfTermByNormalForm : Term → Vars → TC (Maybe ℕ)
  indexOfTermByNormalForm t [] = returnTC nothing
  indexOfTermByNormalForm t (t′ ∷ vars) =
    termEq t t′ >>= λ where
      true → returnTC (just 0)
      false →
        indexOfTermByNormalForm t vars >>= λ where
          (just n) → returnTC (just (suc n))
          nothing → returnTC nothing

  indexOfTermByShape : Term → Vars → TC (Maybe ℕ)
  indexOfTermByShape t [] = returnTC nothing
  indexOfTermByShape t (t′ ∷ vars) =
    case termShapeEq t t′ of λ where
      true → returnTC (just 0)
      false →
        do tNorm ← normalise t
           t′Norm ← normalise t′
           case termShapeEq tNorm t′Norm of λ where
             true → returnTC (just 0)
             false →
               indexOfTermByShape t vars >>= λ where
                 (just n) → returnTC (just (suc n))
                 nothing → returnTC nothing

  indexOfTerm : Term → Vars → TC (Maybe ℕ)
  indexOfTerm t [] = returnTC nothing
  indexOfTerm t vars with indexOf t vars
  ... | just n = returnTC (just n)
  ... | nothing =
    indexOfTermByShape t vars >>= λ where
      (just n) → returnTC (just n)
      nothing → indexOfTermByNormalForm t vars

  addVariable : Term → Vars → TC Vars
  addVariable t vars =
    indexOfTerm t vars >>= λ where
      (just _) → returnTC vars
      nothing → returnTC (t ∷ vars)

  appendVariables : Vars → Vars → TC Vars
  appendVariables [] vars = returnTC vars
  appendVariables (t ∷ ts) vars =
    do vars′ ← addVariable t vars
       appendVariables ts vars′

  asVariable : Term → TC (ExprBuilder × Vars)
  asVariable t =
    do t′ ← normalise t
       returnTC
         ((λ vars →
           indexOfTerm t′ vars >>= λ where
             (just n) → returnTC (con (quote ∣) (finiteNumberAsTerm (just n) v∷ []))
             nothing →
               typeError
                 (strErr "Internal error: Nat solver variable was not collected: "
                 ∷ termErr t′
                 ∷ []))
         , t′ ∷ [])

  buildExpression : ℕ → Term → TC (ExprBuilder × Vars)
  buildExpression zero t =
    typeError (strErr "Nat solver expression parser ran out of fuel at: "
      ∷ termErr t ∷ [])
  buildExpression (suc fuel) t with view+ t
  ... | just (x , y) =
    do rx ← buildExpression fuel x
       ry ← buildExpression fuel y
       vars ← appendVariables (snd rx) (snd ry)
       returnTC
         ((λ vars →
           do x ← fst rx vars
              y ← fst ry vars
              returnTC (con (quote _+'_) (x v∷ y v∷ [])))
         , vars)
  ... | nothing with view· t
  ... | just (x , y) =
    do rx ← buildExpression fuel x
       ry ← buildExpression fuel y
       vars ← appendVariables (snd rx) (snd ry)
       returnTC
         ((λ vars →
           do x ← fst rx vars
              y ← fst ry vars
              returnTC (con (quote _·'_) (x v∷ y v∷ [])))
         , vars)
  ... | nothing with view∸ t
  ... | just _ = asVariable t
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
       vars ← appendVariables (snd rx) (snd ry)
       lhsExpr ← fst rx vars
       rhsExpr ← fst ry vars
       returnTC (lhsExpr , rhsExpr , vars)

  natSolverCall : Term → Term → Vars → Term
  natSolverCall lhs rhs vars =
    let xs = variableVector vars in
    def (quote natSolve)
      (varg lhs
      ∷ varg rhs
      ∷ varg xs
      ∷ varg (def (quote refl) [])
      ∷ [])

  findDirect : Term → Term → List LeFact → TC (Maybe Term)
  findDirect lower upper [] = returnTC nothing
  findDirect lower upper (leFact lower′ upper′ proof ∷ facts) =
    do sameLower ← termEq lower lower′
       sameUpper ← termEq upper upper′
       if sameLower and sameUpper
         then returnTC (just proof)
         else findDirect lower upper facts

  parse≤Type : Term → Maybe (Term × Term)
  parse≤Type = view2 (quote _≤_)

  Strategy : Type
  Strategy = ℕ → List LeFact → Term → Term → TC (Maybe Term)

  infixr 4 _<<<_
  _<<<_ : TC (Maybe Term) → TC (Maybe Term) → TC (Maybe Term)
  m <<< k = m >>= λ where
    (just p) → returnTC (just p)
    nothing → k

  mutual
    synth≤ : Strategy
    synth≤ zero facts lower upper = findDirect lower upper facts
    synth≤ (suc fuel) facts lower upper =
      sFindDirect   fuel facts lower upper <<<
      sRefl         fuel facts lower upper <<<
      sZero         fuel facts lower upper <<<
      sMulRight     fuel facts lower upper <<<
      sMinusUpper   fuel facts lower upper <<<
      sSuc          fuel facts lower upper <<<
      sSum          fuel facts lower upper <<<
      sPlus         fuel facts lower upper <<<
      sSucPlus      fuel facts lower upper <<<
      sAdditiveDiff fuel facts lower upper <<<
      sTrans        fuel facts lower upper

    sFindDirect : Strategy
    sFindDirect _ facts lower upper = findDirect lower upper facts

    sRefl : Strategy
    sRefl _ _ lower upper =
      termEq lower upper >>= λ where
        true → returnTC (just (def (quote leRefl) (lower v∷ [])))
        false → returnTC nothing

    sZero : Strategy
    sZero _ _ lower upper with viewZero lower
    ... | true = returnTC (just (def (quote leZero) (upper v∷ [])))
    ... | false = returnTC nothing

    sMulRight : Strategy
    sMulRight fuel facts lower upper with view· upper
    ... | just (lit (nat (suc k)) , x) =
      synth≤ fuel facts lower x >>= λ where
        (just p) →
          returnTC
            (just
              (def (quote leMulRight)
                (lower v∷ x v∷ natLit k v∷ p v∷ [])))
        nothing → returnTC nothing
    ... | _ = returnTC nothing

    sMinusUpper : Strategy
    sMinusUpper fuel facts lower upper with view∸ upper
    ... | just (upper′ , subtrahend) =
      let lower+sub = def (quote _+_) (lower v∷ subtrahend v∷ []) in
      synth≤ fuel facts lower+sub upper′ >>= λ where
        (just proof) →
          returnTC
            (just
              (def (quote leMinusRight)
                (lower v∷ upper′ v∷ subtrahend v∷ proof v∷ [])))
        nothing →
          let sub+lower = def (quote _+_) (subtrahend v∷ lower v∷ []) in
          synth≤ fuel facts sub+lower upper′ >>= λ where
            (just proof) →
              returnTC
                (just
                  (def (quote leMinusRightComm)
                    (lower v∷ upper′ v∷ subtrahend v∷ proof v∷ [])))
            nothing → returnTC nothing
    ... | nothing = returnTC nothing

    sSuc : Strategy
    sSuc fuel facts lower upper with viewSuc lower | viewSuc upper
    ... | just lower′ | just upper′ =
      returnMap (λ p → def (quote leSuc) (lower′ v∷ upper′ v∷ p v∷ []))
        (synth≤ fuel facts lower′ upper′)
    ... | _ | _ = returnTC nothing

    sSum : Strategy
    sSum fuel facts lower upper with view+ upper
    ... | just (u₁ , u₂) =
      termEq lower u₁ >>= λ where
        true → returnTC (just (def (quote leSumLeft) (u₁ v∷ u₂ v∷ [])))
        false →
          termEq lower u₂ >>= λ where
            true → returnTC (just (def (quote leSumRight) (u₂ v∷ u₁ v∷ [])))
            false →
              synth≤ fuel facts lower u₁ >>= λ where
                (just p₁) →
                  returnTC
                    (just
                      (mk≤-trans lower u₁ upper p₁
                        (def (quote leSumLeft) (u₁ v∷ u₂ v∷ []))))
                nothing →
                  synth≤ fuel facts lower u₂ >>= λ where
                    (just p₂) →
                      returnTC
                        (just
                          (mk≤-trans lower u₂ upper p₂
                            (def (quote leSumRight) (u₂ v∷ u₁ v∷ []))))
                    nothing → returnTC nothing
    ... | nothing = returnTC nothing

    sPlus : Strategy
    sPlus fuel facts lower upper with view+ lower | view+ upper
    ... | just (l₁ , l₂) | just (u₁ , u₂) =
      synth≤ fuel facts l₁ u₁ >>= λ where
        (just p₁) →
          synth≤ fuel facts l₂ u₂ >>= λ where
            (just p₂) → returnTC (just (mk≤-+-≤ l₁ u₁ l₂ u₂ p₁ p₂))
            nothing → returnTC nothing
        nothing → returnTC nothing
    ... | _ | _ = returnTC nothing

    sSucPlus : Strategy
    sSucPlus fuel facts lower upper with viewSuc lower | view+ upper
    ... | just lower′ | just (u₁ , u₂) =
      synth≤ fuel facts oneTerm u₁ >>= λ where
        (just p₁) →
          synth≤ fuel facts lower′ u₂ >>= λ where
            (just p₂) → returnTC (just (mk≤-+-≤ oneTerm u₁ lower′ u₂ p₁ p₂))
            nothing → returnTC nothing
        nothing → returnTC nothing
    ... | _ | _ = returnTC nothing

    sAdditiveDiff : Strategy
    sAdditiveDiff _ _ lower upper =
      removeAddends (addends lower) (addends upper) >>= λ where
        (just diffTerms) →
          let diff = sumTerms diffTerms in
          let lhs = def (quote _+_) (diff v∷ lower v∷ []) in
          do parsed ← toNatExpression lhs upper
             let lhsExpr = fst parsed
             let rhsExpr = fst (snd parsed)
             let vars = snd (snd parsed)
             returnTC
               (just
                 (con (quote _,_)
                   (diff v∷ natSolverCall lhsExpr rhsExpr vars v∷ [])))
        nothing → returnTC nothing

    sTrans : Strategy
    sTrans fuel facts lower upper = sTransAt fuel facts lower upper facts

    sTransAt :
      ℕ → List LeFact → Term → Term → List LeFact → TC (Maybe Term)
    sTransAt fuel facts lower upper [] = returnTC nothing
    sTransAt fuel facts lower upper (leFact factLower factUpper factProof ∷ rest) =
      termEq lower factLower >>= λ where
        true →
          synth≤ fuel facts factUpper upper >>= λ where
            (just q) → returnTC (just (mk≤-trans lower factUpper upper factProof q))
            nothing → sTransAtRight fuel facts lower upper rest factLower factUpper factProof
        false → sTransAtRight fuel facts lower upper rest factLower factUpper factProof

    sTransAtRight :
      ℕ → List LeFact → Term → Term → List LeFact → Term → Term → Term → TC (Maybe Term)
    sTransAtRight fuel facts lower upper rest factLower factUpper factProof =
      termEq upper factUpper >>= λ where
        true →
          synth≤ fuel facts lower factLower >>= λ where
            (just p) → returnTC (just (mk≤-trans lower factLower upper p factProof))
            nothing → sTransAt fuel facts lower upper rest
        false → sTransAt fuel facts lower upper rest

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
  rewriteFuel : ℕ
  rewriteFuel = 50
  synthFuel : ℕ
  synthFuel = 8

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

  leMinusPlusEqTerm : Term → Term → Term → Term
  leMinusPlusEqTerm lower upper proof =
    def (quote leMinusPlusEq) (lower v∷ upper v∷ proof v∷ [])

  minusZeroRightTerm : Term → Term
  minusZeroRightTerm x =
    def (quote minusZeroRight) (x v∷ [])

  minusZeroLeftTerm : Term → Term
  minusZeroLeftTerm x =
    def (quote minusZeroLeft) (x v∷ [])

  minusSelfTerm : Term → Term
  minusSelfTerm x =
    def (quote minusSelf) (x v∷ [])

  minusPullLeftTerm : Term → Term → Term → Term → Term
  minusPullLeftTerm m n k p =
    def (quote minusPullLeft) (m v∷ n v∷ k v∷ p v∷ [])

  minusPullRightTerm : Term → Term → Term → Term → Term
  minusPullRightTerm m n k p =
    def (quote minusPullRight) (m v∷ n v∷ k v∷ p v∷ [])

  minusPlusRightTerm : Term → Term → Term
  minusPlusRightTerm x k =
    def (quote minusPlusRight) (x v∷ k v∷ [])

  minusPlusLeftTerm : Term → Term → Term
  minusPlusLeftTerm k x =
    def (quote minusPlusLeft) (k v∷ x v∷ [])

  rewriteMinusByPlus : Term → Term → TC (Maybe Rewrite)
  rewriteMinusByPlus upper lower with view+ upper
  ... | just (x , k) =
    termEq lower x >>= λ where
      true →
        returnTC
          (just
            (mkRewrite k
              (minusPlusRightTerm x k)))
      false →
        termEq lower k >>= λ where
          true →
            returnTC
              (just
                (mkRewrite x
                  (minusPlusLeftTerm x k)))
          false → returnTC nothing
  ... | nothing = returnTC nothing

  rewriteMinusFromSum : ℕ → List LeFact → Term → Term → TC (Maybe Rewrite)
  rewriteMinusFromSum zero facts upper lower = returnTC nothing
  rewriteMinusFromSum (suc fuel) facts upper lower with view+ upper
  ... | just (x , y) =
    termEq lower x >>= λ where
      true →
        returnTC
          (just
            (mkRewrite y
              (minusPlusRightTerm x y)))
      false →
        termEq lower y >>= λ where
          true →
            returnTC
              (just
                (mkRewrite x
                  (minusPlusLeftTerm x y)))
          false →
            rewriteMinusFromSum fuel facts x lower >>= λ where
              (just rx) →
                synth≤ synthFuel facts lower x >>= λ where
                  (just guard) →
                    let x∸lower = def (quote _∸_) (x v∷ lower v∷ []) in
                    let diff = def (quote _+_) (Rewrite.term rx v∷ y v∷ []) in
                    let diffStep =
                          cong₂+Term x∸lower (Rewrite.term rx) y y
                            (Rewrite.step rx)
                            (natReflTerm y)
                    in
                    returnTC
                      (just
                        (mkRewrite diff
                          (compTerm
                            (def (quote _∸_)
                              (upper v∷ lower v∷ []))
                            (def (quote _+_) (x∸lower v∷ y v∷ []))
                            diff
                            (minusPullRightTerm lower x y guard)
                            diffStep)))
                  nothing → tryRight
              nothing → tryRight
    where
    tryPullRight : TC (Maybe Rewrite)
    tryPullRight =
      synth≤ synthFuel facts lower y >>= λ where
        (just guard) →
          let diff = def (quote _+_)
                (x v∷ def (quote _∸_) (y v∷ lower v∷ []) v∷ [])
          in
          returnTC
            (just
              (mkRewrite diff
                (minusPullLeftTerm lower y x guard)))
        nothing → returnTC nothing

    tryPullLeft : TC (Maybe Rewrite)
    tryPullLeft =
      synth≤ synthFuel facts lower x >>= λ where
        (just guard) →
          let diff = def (quote _+_)
                (def (quote _∸_) (x v∷ lower v∷ []) v∷ y v∷ [])
          in
          returnTC
            (just
              (mkRewrite diff
                (minusPullRightTerm lower x y guard)))
        nothing → tryPullRight

    tryRight : TC (Maybe Rewrite)
    tryRight =
      rewriteMinusFromSum fuel facts y lower >>= λ where
        (just ry) →
          synth≤ synthFuel facts lower y >>= λ where
            (just guard) →
              let y∸lower = def (quote _∸_) (y v∷ lower v∷ []) in
              let diff = def (quote _+_) (x v∷ Rewrite.term ry v∷ []) in
              let diffStep =
                    cong₂+Term x x y∸lower (Rewrite.term ry)
                      (natReflTerm x)
                      (Rewrite.step ry)
              in
              returnTC
                (just
                  (mkRewrite diff
                    (compTerm
                      (def (quote _∸_)
                        (upper v∷ lower v∷ []))
                      (def (quote _+_) (x v∷ y∸lower v∷ []))
                      diff
                      (minusPullLeftTerm lower y x guard)
                      diffStep)))
            nothing → tryPullLeft
        nothing → tryPullLeft
  ... | nothing = returnTC nothing

  rewriteMinusDirect : ℕ → List LeFact → Term → Term → TC (Maybe Rewrite)
  rewriteMinusDirect fuel facts upper lower with viewZero lower
  ... | true =
    returnTC
      (just
        (mkRewrite upper
          (minusZeroRightTerm upper)))
  ... | false with viewZero upper
  ... | true =
    returnTC
      (just
        (mkRewrite zeroTerm
          (minusZeroLeftTerm lower)))
  ... | false =
    termEq upper lower >>= λ where
      true →
        returnTC
          (just
            (mkRewrite zeroTerm
              (minusSelfTerm upper)))
      false →
        rewriteMinusByPlus upper lower >>= λ where
          (just r) → returnTC (just r)
          nothing → rewriteMinusFromSum fuel facts upper lower

  record RewritePolicy : Type where
    constructor mkPolicy
    field
      fuelErrorPrefix : String
      preHead : Term → TC (Maybe Rewrite)
      onMinus : ℕ → Term → Term → TC (Maybe Rewrite)

  noPreHead : Term → TC (Maybe Rewrite)
  noPreHead _ = returnTC nothing

  noOpMinus : ℕ → Term → Term → TC (Maybe Rewrite)
  noOpMinus _ _ _ = returnTC nothing

  rewriteMinusBasic : Term → Term → TC (Maybe Rewrite)
  rewriteMinusBasic upper lower with viewZero lower
  ... | true =
    returnTC
      (just
        (mkRewrite upper
          (minusZeroRightTerm upper)))
  ... | false with viewZero upper
  ... | true =
    returnTC
      (just
        (mkRewrite zeroTerm
          (minusZeroLeftTerm lower)))
  ... | false =
    termEq upper lower >>= λ where
      true →
        returnTC
          (just
            (mkRewrite zeroTerm
              (minusSelfTerm upper)))
      false → rewriteMinusByPlus upper lower

  findUpperRewrite : Term → List LeFact → TC (Maybe Rewrite)
  findUpperRewrite t [] = returnTC nothing
  findUpperRewrite t (leFact lower upper proof ∷ facts) =
    termEq t upper >>= λ where
      true →
        returnTC
          (just
            (mkRewrite
              (def (quote _+_)
                (def (quote _∸_) (upper v∷ lower v∷ []) v∷ lower v∷ []))
              (leMinusPlusEqTerm lower upper proof)))
      false → findUpperRewrite t facts

  findUpperRewriteWitness : Term → List LeFact → TC (Maybe Rewrite)
  findUpperRewriteWitness t [] = returnTC nothing
  findUpperRewriteWitness t (leFact lower upper proof ∷ facts) =
    termEq t upper >>= λ where
      true →
        returnTC
          (just
            (mkRewrite
              (def (quote _+_) (fstTerm proof v∷ lower v∷ []))
              (leWitnessEqTerm lower upper proof)))
      false → findUpperRewriteWitness t facts

  onMinusElim : List LeFact → ℕ → Term → Term → TC (Maybe Rewrite)
  onMinusElim facts fuel upper′ lower′ =
    rewriteMinusDirect fuel facts upper′ lower′

  onMinusWitness : List LeFact → ℕ → Term → Term → TC (Maybe Rewrite)
  onMinusWitness facts _ upper′ lower′ =
    rewriteMinusBasic upper′ lower′ >>= λ where
      (just r) → returnTC (just r)
      nothing →
        synth≤ synthFuel facts lower′ upper′ >>= λ where
          (just proof) →
            returnTC
              (just
                (mkRewrite (fstTerm proof)
                  (def (quote ∸-witness) (proof v∷ []))))
          nothing →
            typeError
              (strErr "Could not synthesize a checked ≤ guard for subtraction: "
              ∷ termErr lower′
              ∷ strErr " ≤ "
              ∷ termErr upper′
              ∷ [])

  policyMinusElim : List LeFact → RewritePolicy
  policyMinusElim facts =
    mkPolicy "Nat solver preprocessing ran out of fuel at: "
      noPreHead (onMinusElim facts)

  policyMinusElimWitness : List LeFact → RewritePolicy
  policyMinusElimWitness facts =
    mkPolicy "Nat solver witness preprocessing ran out of fuel at: "
      noPreHead (onMinusWitness facts)

  policyUpperRewrite : List LeFact → RewritePolicy
  policyUpperRewrite facts =
    mkPolicy "Nat solver ≤-assumption rewriting ran out of fuel at: "
      (λ t → findUpperRewrite t facts) noOpMinus

  policyUpperRewriteWitness : List LeFact → RewritePolicy
  policyUpperRewriteWitness facts =
    mkPolicy "Nat solver witness ≤-assumption rewriting ran out of fuel at: "
      (λ t → findUpperRewriteWitness t facts) noOpMinus

  mutual
    traverseRewrite : RewritePolicy → ℕ → Term → TC Rewrite
    traverseRewrite pol zero t =
      typeError
        (strErr (RewritePolicy.fuelErrorPrefix pol) ∷ termErr t ∷ [])
    traverseRewrite pol (suc fuel) t =
      RewritePolicy.preHead pol t >>= λ where
        (just r) → returnTC r
        nothing → traverseStructural pol fuel t

    traverseStructural : RewritePolicy → ℕ → Term → TC Rewrite
    traverseStructural pol fuel t with view+ t
    ... | just (x , y) =
      do rx ← traverseRewrite pol fuel x
         ry ← traverseRewrite pol fuel y
         let x′ = Rewrite.term rx
         let y′ = Rewrite.term ry
         returnTC
           (mkRewrite
             (def (quote _+_) (x′ v∷ y′ v∷ []))
             (cong₂+Term x x′ y y′ (Rewrite.step rx) (Rewrite.step ry)))
    ... | nothing with view· t
    ... | just (x , y) =
      do rx ← traverseRewrite pol fuel x
         ry ← traverseRewrite pol fuel y
         let x′ = Rewrite.term rx
         let y′ = Rewrite.term ry
         returnTC
           (mkRewrite
             (def (quote _·_) (x′ v∷ y′ v∷ []))
             (cong₂·Term x x′ y y′ (Rewrite.step rx) (Rewrite.step ry)))
    ... | nothing with view∸ t
    ... | just (upper , lower) =
      do rUpper ← traverseRewrite pol fuel upper
         rLower ← traverseRewrite pol fuel lower
         let upper′ = Rewrite.term rUpper
         let lower′ = Rewrite.term rLower
         let origMinus = def (quote _∸_) (upper v∷ lower v∷ [])
         let rebuilt = def (quote _∸_) (upper′ v∷ lower′ v∷ [])
         let childStep =
               cong₂∸Term upper upper′ lower lower′
                 (Rewrite.step rUpper) (Rewrite.step rLower)
         RewritePolicy.onMinus pol fuel upper′ lower′ >>= λ where
           (just r) →
             returnTC
               (mkRewrite (Rewrite.term r)
                 (compTerm origMinus rebuilt (Rewrite.term r)
                   childStep (Rewrite.step r)))
           nothing →
             returnTC (mkRewrite rebuilt childStep)
    ... | nothing with viewSuc t
    ... | just x =
      do rx ← traverseRewrite pol fuel x
         let x′ = Rewrite.term rx
         returnTC
           (mkRewrite (con (quote suc) (x′ v∷ []))
             (congSucTerm x x′ (Rewrite.step rx)))
    ... | nothing = returnTC (mkRewrite t (natReflTerm t))

  rewriteTerm : ℕ → List LeFact → Term → TC Rewrite
  rewriteTerm fuel facts = traverseRewrite (policyMinusElim facts) fuel

  rewriteBy≤Facts : ℕ → List LeFact → Term → TC Rewrite
  rewriteBy≤Facts fuel facts = traverseRewrite (policyUpperRewrite facts) fuel

  rewriteTermWitness : ℕ → List LeFact → Term → TC Rewrite
  rewriteTermWitness fuel facts = traverseRewrite (policyMinusElimWitness facts) fuel

  rewriteBy≤FactsWitness : ℕ → List LeFact → Term → TC Rewrite
  rewriteBy≤FactsWitness fuel facts = traverseRewrite (policyUpperRewriteWitness facts) fuel

  processSide : RewritePolicy → RewritePolicy → Bool → Term → TC (Term × Term)
  processSide elimPol upperPol threePass t =
    do r1 ← traverseRewrite elimPol rewriteFuel t
       after∸ ← normalise (Rewrite.term r1)
       r2 ← traverseRewrite upperPol rewriteFuel after∸
       case threePass of λ where
         true →
           do r3 ← traverseRewrite elimPol rewriteFuel (Rewrite.term r2)
              final ← normalise (Rewrite.term r3)
              let step =
                    compTerm t (Rewrite.term r1) final
                      (Rewrite.step r1)
                      (compTerm (Rewrite.term r1) (Rewrite.term r2) final
                        (Rewrite.step r2)
                        (Rewrite.step r3))
              returnTC (final , step)
         false →
           do final ← normalise (Rewrite.term r2)
              let step =
                    compTerm t (Rewrite.term r1) final
                      (Rewrite.step r1)
                      (Rewrite.step r2)
              returnTC (final , step)

  solveEqGoal :
    List LeFact → RewritePolicy → RewritePolicy → Bool
    → Term → Term → Term → TC Term
  solveEqGoal leFacts elimPol upperPol threePass goal lhsN rhsN =
    do (lhs′ , lhsStep) ← processSide elimPol upperPol threePass lhsN
       (rhs′ , rhsStep) ← processSide elimPol upperPol threePass rhsN
       parsed ← toNatExpression lhs′ rhs′
       let lhsExpr = fst parsed
       let rhsExpr = fst (snd parsed)
       let vars = snd (snd parsed)
       let middle = natSolverCall lhsExpr rhsExpr vars
       checkType
         (def (quote finishNatExplicit)
           (lhsN v∷ lhs′ v∷ rhsN v∷ rhs′ v∷
            lhsStep v∷ middle v∷ rhsStep v∷ []))
         goal

  solveLeGoal :
    List LeFact → RewritePolicy → RewritePolicy → Bool
    → Term → Term → Term → TC Term
  solveLeGoal leFacts elimPol upperPol threePass goal lowerN upperN =
    do (lower′ , lowerStep) ← processSide elimPol upperPol threePass lowerN
       (upper′ , upperStep) ← processSide elimPol upperPol threePass upperN
       proof? ← synth≤ synthFuel leFacts lower′ upper′
       case proof? of λ where
         (just middle) →
           checkType
             (def (quote finishLeExplicit)
              (lowerN v∷ lower′ v∷ upperN v∷ upper′ v∷
               lowerStep v∷ middle v∷ upperStep v∷ []))
             goal
         nothing →
           typeError
             (strErr "Could not synthesize a checked ≤ proof: "
             ∷ termErr lower′
             ∷ strErr " ≤ "
             ∷ termErr upper′
             ∷ [])

  solveNatGoalProof : List LeFact → Term → TC Term
  solveNatGoalProof leFacts goal =
    do boundary ← unapply-path goal
       case boundary of λ where
         nothing →
           case parse≤Type goal of λ where
             (just (lower , upper)) →
               do lowerN ← normalise lower
                  upperN ← normalise upper
                  proof? ← synth≤ synthFuel leFacts lowerN upperN
                  case proof? of λ where
                    (just proof) →
                      checkType proof goal
                    nothing →
                      (solveLeGoal leFacts
                         (policyMinusElim leFacts) (policyUpperRewrite leFacts)
                         true goal lowerN upperN)
                      <|>
                      (solveLeGoal leFacts
                         (policyMinusElimWitness leFacts) (policyUpperRewriteWitness leFacts)
                         false goal lowerN upperN)
             nothing →
               typeError (strErr "Expected a Cubical Nat path or ≤ goal, got: "
                 ∷ termErr goal ∷ [])
         (just (dom , lhs , rhs)) →
           do unify dom (def (quote ℕ) [])
              lhsN ← normalise lhs
              rhsN ← normalise rhs
              (solveEqGoal leFacts
                 (policyMinusElim leFacts) (policyUpperRewrite leFacts)
                 true goal lhsN rhsN)
               <|>
               (solveEqGoal leFacts
                  (policyMinusElimWitness leFacts) (policyUpperRewriteWitness leFacts)
                  false goal lhsN rhsN)

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
