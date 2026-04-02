{-# OPTIONS --safe #-}

module TReg.CompTheorem where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Empty.Base as Empty using (⊥ ; rec)
open import Cubical.Data.Sigma using (Σ ; Σ-syntax ; _×_ ; _,_ ; fst ; snd)
open import Cubical.Data.List.Base using ([] ; _∷_ ; _++_ ; length)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Nat.Order using (_<_ ; <-wellfounded)
open import Cubical.Data.Nat.Properties using (snotz)
open import Cubical.Data.Unit.Base using (Unit ; tt)
open import Cubical.Induction.WellFounded using (Acc ; acc)

open import TReg.Syntax
open import TReg.Context
open import TReg.Substitution
open import TReg.Measure
open import TReg.Evaluation
open import TReg.Derivability
open import TReg.Computability
open import TReg.Inversion
open import TReg.Presupposition
open import TReg.Structural
open import TReg.TopComp
open import TReg.EqComp
open import TReg.MainTheorem

nonemptyNeNil : {A : RawType} {gamma : Ctx} -> (A ∷ gamma ≡ []) -> ⊥
nonemptyNeNil {gamma = gamma} p = snotz (cong length p)

case_of_ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} -> A -> (A -> B) -> B
case x of f = f x

data CompFitsSubst : Ctx -> Subst -> Type where
  compFitsNil : {sigma : Subst} -> CompFitsSubst [] sigma
  compFitsCons : {gamma : Ctx} {sigma : Subst} {A : RawType} {t : RawTerm}
    -> CompFitsSubst gamma sigma
    -> Computable (hasTy [] t (subTy sigma A))
    -> CompFitsSubst (A ∷ gamma) (consSubst t sigma)

data CompFitsEqSubst : Ctx -> Subst -> Subst -> Type where
  compFitsEqNil : {sigma tau : Subst} -> CompFitsEqSubst [] sigma tau
  compFitsEqCons : {gamma : Ctx} {sigma tau : Subst} {A : RawType} {t u : RawTerm}
    -> CompFitsEqSubst gamma sigma tau
    -> Computable (termEq [] t u (subTy sigma A))
    -> CompFitsEqSubst (A ∷ gamma) (consSubst t sigma) (consSubst u tau)

record ClosedSubstComp (J : JForm) (sigma : Subst) : Type where
  constructor closedSubstComp
  field
    closedComp : Computable (closedSubJ sigma J)
    closedCompFits : CompFitsSubst (ctxOf J) sigma

record ClosedEqSubstComp (J : JForm) (sigma tau : Subst) : Type where
  constructor closedEqSubstComp
  field
    closedEqComp : Computable (closedEqSubJ sigma tau J)
    closedEqCompFits : CompFitsEqSubst (ctxOf J) sigma tau

mutual
  compFSigmaClosed : {A B : RawType}
    -> Computable (isType [] A)
    -> HypComputable (isType (A ∷ []) B)
    -> Computable (isType [] (tySigma A B))
  compFSigmaClosed compA compB =
    compTyClosedSigma
      (fSigma (compToDerivable compA) (hypCompToDerivable compB))
      evalSigma
      (reflTy (fSigma (compToDerivable compA) (hypCompToDerivable compB)))
      compA
      (hypCompToDerivable compB)
  
  compISigmaClosed : {a b : RawTerm} {A B : RawType}
    -> Computable (hasTy [] a A)
    -> Computable (hasTy [] b (subTy (singleSubst a) B))
    -> Computable (isType [] (tySigma A B))
    -> Computable (hasTy [] (tmPair a b) (tySigma A B))
  compISigmaClosed compa compb compSigma =
    compTmClosedSigma
      (iSigma (compToDerivable compa) (compToDerivable compb) (compToDerivable compSigma))
      compSigma
      evalSigma
      evalPair
      (reflTm (iSigma (compToDerivable compa) (compToDerivable compb) (compToDerivable compSigma)))
      compa
      compb
  
  compCSigmaClosed : {b c m : RawTerm} {A B M : RawType}
    -> HypComputable (isType ((tySigma A B) ∷ []) M)
    -> Computable (hasTy [] b A)
    -> Computable (hasTy [] c (subTy (singleSubst b) B))
    -> HypComputable (hasTy (B ∷ A ∷ []) m (sigmaBranchTy M))
    -> Computable
         (termEq [] (tmElSigma (tmPair b c) m) (subTm (sigmaCompSub b c) m)
           (subTy (singleSubst (tmPair b c)) M))
  compCSigmaClosed {b = b} {c = c} {m = m} {A = A} {B = B} {M = M}
    compM compb compc compm@(hypTmOpen neq dm compBranchTy sub subEq) =
    lhsEq body
    where
    db : Derivable (hasTy [] b A)
    db = compToDerivable compb
  
    dc : Derivable (hasTy [] c (subTy (singleSubst b) B))
    dc = compToDerivable compc
  
    dM : Derivable (isType ((tySigma A B) ∷ []) M)
    dM = hypCompToDerivable compM
  
    bodyFits : Σ (FitsSubst [] (B ∷ A ∷ []) (sigmaCompSub b c)) (λ fits -> ComputableFits fits)
    bodyFits = sigmaCompComputableFitsHelper compb compc
  
    rawBody : Computable
      (hasTy [] (subTm (sigmaCompSub b c) m) (subTy (sigmaCompSub b c) (sigmaBranchTy M)))
    rawBody = sub (sigmaCompSub b c) (fst bodyFits) (snd bodyFits)
  
    body : Computable
      (hasTy [] (subTm (sigmaCompSub b c) m) (subTy (singleSubst (tmPair b c)) M))
    body =
      subst
        (λ T -> Computable (hasTy [] (subTm (sigmaCompSub b c) m) T))
        (sigmaBranchTyComp b c M)
        rawBody
  
    dEq : Derivable
      (termEq [] (tmElSigma (tmPair b c) m) (subTm (sigmaCompSub b c) m)
        (subTy (singleSubst (tmPair b c)) M))
    dEq = cSigma dM db dc dm
  
    dLeft : Derivable
      (hasTy [] (tmElSigma (tmPair b c) m) (subTy (singleSubst (tmPair b c)) M))
    dLeft = assocTmLeft dEq
  
    lhsEq :
      Computable
        (hasTy [] (subTm (sigmaCompSub b c) m) (subTy (singleSubst (tmPair b c)) M))
      -> Computable
           (termEq [] (tmElSigma (tmPair b c) m) (subTm (sigmaCompSub b c) m)
             (subTy (singleSubst (tmPair b c)) M))
    lhsEq body@(compTmClosedTop drhs compTy evTy evRhs corrRhs) =
      let
        lhsCorr = transTm dEq corrRhs
        lhsComp =
          compTmClosedTop
            dLeft
            compTy
            evTy
            (evalElSigma evalPair evRhs)
            lhsCorr
      in
      compTmEqClosedTop dEq lhsComp body evTy (evalElSigma evalPair evRhs) evRhs
    lhsEq body@(compTmClosedSigma drhs compTy evTy evRhs corrRhs comp₁ comp₂) =
      let
        lhsCorr = transTm dEq corrRhs
        lhsComp =
          compTmClosedSigma
            dLeft
            compTy
            evTy
            (evalElSigma evalPair evRhs)
            lhsCorr
            comp₁
            comp₂
      in
      compTmEqClosedSigma
        dEq
        lhsComp
        body
        evTy
        (evalElSigma evalPair evRhs)
        evRhs
        (compReflTmClosed comp₁)
        (compReflTmClosed comp₂)
    lhsEq body@(compTmClosedEq drhs compTy evTy evRhs corrRhs compEq) =
      let
        lhsCorr = transTm dEq corrRhs
        lhsComp =
          compTmClosedEq
            dLeft
            compTy
            evTy
            (evalElSigma evalPair evRhs)
            lhsCorr
            compEq
      in
      compTmEqClosedEq
        dEq
        lhsComp
        body
        evTy
        (evalElSigma evalPair evRhs)
        evRhs
        compEq
    lhsEq body@(compTmClosedQtr drhs compTy evTy evRhs corrRhs compa) =
      let
        lhsCorr = transTm dEq corrRhs
        lhsComp =
          compTmClosedQtr
            dLeft
            compTy
            evTy
            (evalElSigma evalPair evRhs)
            lhsCorr
            compa
      in
      compTmEqClosedQtr
        dEq
        lhsComp
        body
        evTy
        (evalElSigma evalPair evRhs)
        evRhs
        compa
        compa
  
  compESigmaClosed : {A B M : RawType} {d d' m m' : RawTerm}
    -> HypComputable (isType ((tySigma A B) ∷ []) M)
    -> Computable (termEq [] d d' (tySigma A B))
    -> HypComputable (termEq (B ∷ A ∷ []) m m' (sigmaBranchTy M))
    -> Computable
         (termEq [] (tmElSigma d m) (tmElSigma d' m') (subTy (singleSubst d) M))
  compESigmaClosed {A = A} {B = B} {M = M} {d = d} {d' = d'} {m = m} {m' = m'}
    compM compdd'
    compmm'@(hypTmEqOpen neq dll' compBranchTy sub subEq) =
    compTransTmClosed leftCan (compTransTmClosed bodyEqD (compSymTmClosed rightCan))
    where
    open ClosedSigmaTmEqInv (invertSigmaTmEq compdd' evalSigma)
  
    compSigma : Computable (isType [] (tySigma A B))
    compSigma = compTmToCompTy sigmaTmEqCompLeft
  
    compPairLeft : Computable (hasTy [] (tmPair sigmaTmEqLeftFst sigmaTmEqLeftSnd) (tySigma A B))
    compPairLeft =
      compISigmaClosed sigmaTmEqLeftCompFstTy sigmaTmEqLeftCompSndTy compSigma
  
    compPairRight : Computable (hasTy [] (tmPair sigmaTmEqRightFst sigmaTmEqRightSnd) (tySigma A B))
    compPairRight =
      compISigmaClosed sigmaTmEqRightCompFstTy sigmaTmEqRightCompSndTy compSigma
  
    compLeftCorr : Computable
      (termEq [] d (tmPair sigmaTmEqLeftFst sigmaTmEqLeftSnd) (tySigma A B))
    compLeftCorr =
      compTmEqClosedSigma
        sigmaTmEqLeftCorrPair
        sigmaTmEqCompLeft
        compPairLeft
        evalSigma
        sigmaTmEqEvalLeftPair
        evalPair
        (compReflTmClosed sigmaTmEqLeftCompFstTy)
        (compReflTmClosed sigmaTmEqLeftCompSndTy)
  
    compRightCorr : Computable
      (termEq [] d' (tmPair sigmaTmEqRightFst sigmaTmEqRightSnd) (tySigma A B))
    compRightCorr =
      compTmEqClosedSigma
        sigmaTmEqRightCorrPair
        sigmaTmEqCompRight
        compPairRight
        evalSigma
        sigmaTmEqEvalRightPair
        evalPair
        (compReflTmClosed sigmaTmEqRightCompFstTy)
        (compReflTmClosed sigmaTmEqRightCompSndTy)
  
    branchFitsEq : Σ
      (FitsEqSubst [] (B ∷ A ∷ [])
        (sigmaCompSub sigmaTmEqLeftFst sigmaTmEqLeftSnd)
        (sigmaCompSub sigmaTmEqRightFst sigmaTmEqRightSnd))
      (λ fitsEq -> ComputableFitsEq fitsEq)
    branchFitsEq = sigmaCompComputableFitsEqHelper sigmaTmEqCompFst sigmaTmEqCompSnd
  
    branchEqPair : Computable
      (termEq []
        (subTm (sigmaCompSub sigmaTmEqLeftFst sigmaTmEqLeftSnd) m)
        (subTm (sigmaCompSub sigmaTmEqRightFst sigmaTmEqRightSnd) m')
        (subTy (singleSubst (tmPair sigmaTmEqLeftFst sigmaTmEqLeftSnd)) M))
    branchEqPair =
      subst
        (λ T ->
          Computable
            (termEq []
              (subTm (sigmaCompSub sigmaTmEqLeftFst sigmaTmEqLeftSnd) m)
              (subTm (sigmaCompSub sigmaTmEqRightFst sigmaTmEqRightSnd) m')
              T))
        (sigmaBranchTyComp sigmaTmEqLeftFst sigmaTmEqLeftSnd M)
        (subEq
          (sigmaCompSub sigmaTmEqLeftFst sigmaTmEqLeftSnd)
          (sigmaCompSub sigmaTmEqRightFst sigmaTmEqRightSnd)
          (fst branchFitsEq)
          (snd branchFitsEq))
  
    bodyEqD : Computable
      (termEq []
        (subTm (sigmaCompSub sigmaTmEqLeftFst sigmaTmEqLeftSnd) m)
        (subTm (sigmaCompSub sigmaTmEqRightFst sigmaTmEqRightSnd) m')
        (subTy (singleSubst d) M))
    bodyEqD =
      compConvTmEqClosed
        branchEqPair
        (compSingleEqSubstTyClosed compM (compSymTmClosed compLeftCorr))
  
    bodyLeft : Computable
      (hasTy []
        (subTm (sigmaCompSub sigmaTmEqLeftFst sigmaTmEqLeftSnd) m)
        (subTy (singleSubst d) M))
    bodyLeft = compTmEqLeft bodyEqD
  
    bodyRight : Computable
      (hasTy []
        (subTm (sigmaCompSub sigmaTmEqRightFst sigmaTmEqRightSnd) m')
        (subTy (singleSubst d) M))
    bodyRight = compTmEqRightClosed bodyEqD
  
    dM : Derivable (isType ((tySigma A B) ∷ []) M)
    dM = hypCompToDerivable compM
  
    dm : Derivable (hasTy (B ∷ A ∷ []) m (sigmaBranchTy M))
    dm = assocTmLeft dll'
  
    dm' : Derivable (hasTy (B ∷ A ∷ []) m' (sigmaBranchTy M))
    dm' = assocTmRight dll'
  
    db : Derivable (hasTy [] sigmaTmEqLeftFst A)
    db = compToDerivable sigmaTmEqLeftCompFstTy
  
    dc : Derivable (hasTy [] sigmaTmEqLeftSnd (subTy (singleSubst sigmaTmEqLeftFst) B))
    dc = compToDerivable sigmaTmEqLeftCompSndTy
  
    de : Derivable (hasTy [] sigmaTmEqRightFst A)
    de = compToDerivable sigmaTmEqRightCompFstTy
  
    df : Derivable (hasTy [] sigmaTmEqRightSnd (subTy (singleSubst sigmaTmEqRightFst) B))
    df = compToDerivable sigmaTmEqRightCompSndTy
  
    dLeftStep : Derivable
      (termEq [] (tmElSigma d m) (tmElSigma (tmPair sigmaTmEqLeftFst sigmaTmEqLeftSnd) m)
        (subTy (singleSubst d) M))
    dLeftStep = eSigmaEq dM sigmaTmEqLeftCorrPair (reflTm dm)
  
    dLeftCanon : Derivable
      (termEq []
        (tmElSigma (tmPair sigmaTmEqLeftFst sigmaTmEqLeftSnd) m)
        (subTm (sigmaCompSub sigmaTmEqLeftFst sigmaTmEqLeftSnd) m)
        (subTy (singleSubst d) M))
    dLeftCanon =
      convEq
        (cSigma dM db dc dm)
        (symTy (singleEqSubstTyHelper dM (compToDerivable compLeftCorr)))
  
    dLeftEq : Derivable
      (termEq []
        (tmElSigma d m)
        (subTm (sigmaCompSub sigmaTmEqLeftFst sigmaTmEqLeftSnd) m)
        (subTy (singleSubst d) M))
    dLeftEq = transTm dLeftStep dLeftCanon
  
    dLeftTy : Derivable (hasTy [] (tmElSigma d m) (subTy (singleSubst d) M))
    dLeftTy = assocTmLeft dLeftEq
  
    dRightCanon0 : Derivable
      (termEq []
        (tmElSigma d' m')
        (subTm (sigmaCompSub sigmaTmEqRightFst sigmaTmEqRightSnd) m')
        (subTy (singleSubst d') M))
    dRightCanon0 =
      transTm
        (eSigmaEq dM sigmaTmEqRightCorrPair (reflTm dm'))
        (convEq
          (cSigma dM de df dm')
          (symTy (singleEqSubstTyHelper dM (compToDerivable compRightCorr))))
  
    dRightEq : Derivable
      (termEq []
        (tmElSigma d' m')
        (subTm (sigmaCompSub sigmaTmEqRightFst sigmaTmEqRightSnd) m')
        (subTy (singleSubst d) M))
    dRightEq =
      convEq
        dRightCanon0
        (symTy (singleEqSubstTyHelper dM (compToDerivable compdd')))
  
    dRightTy : Derivable (hasTy [] (tmElSigma d' m') (subTy (singleSubst d) M))
    dRightTy = assocTmLeft dRightEq
  
    mkLeftCanon :
      Derivable
        (termEq []
          (tmElSigma d m)
          (subTm (sigmaCompSub sigmaTmEqLeftFst sigmaTmEqLeftSnd) m)
          (subTy (singleSubst d) M))
      -> Derivable (hasTy [] (tmElSigma d m) (subTy (singleSubst d) M))
      -> d =>e tmPair sigmaTmEqLeftFst sigmaTmEqLeftSnd
      -> Computable
           (hasTy []
             (subTm (sigmaCompSub sigmaTmEqLeftFst sigmaTmEqLeftSnd) m)
             (subTy (singleSubst d) M))
      -> Computable
           (termEq []
             (tmElSigma d m)
             (subTm (sigmaCompSub sigmaTmEqLeftFst sigmaTmEqLeftSnd) m)
             (subTy (singleSubst d) M))
    mkLeftCanon dEq dLeft evd body@(compTmClosedTop _ compTy evTy evRhs corrRhs) =
      let
        lhsCorr = transTm dEq corrRhs
        lhsComp =
          compTmClosedTop
            dLeft
            compTy
            evTy
            (evalElSigma evd evRhs)
            lhsCorr
      in
      compTmEqClosedTop dEq lhsComp body evTy (evalElSigma evd evRhs) evRhs
    mkLeftCanon dEq dLeft evd body@(compTmClosedSigma _ compTy evTy evRhs corrRhs comp₁ comp₂) =
      let
        lhsCorr = transTm dEq corrRhs
        lhsComp =
          compTmClosedSigma
            dLeft
            compTy
            evTy
            (evalElSigma evd evRhs)
            lhsCorr
            comp₁
            comp₂
      in
      compTmEqClosedSigma
        dEq
        lhsComp
        body
        evTy
        (evalElSigma evd evRhs)
        evRhs
        (compReflTmClosed comp₁)
        (compReflTmClosed comp₂)
    mkLeftCanon dEq dLeft evd body@(compTmClosedEq _ compTy evTy evRhs corrRhs compEq) =
      let
        lhsCorr = transTm dEq corrRhs
        lhsComp =
          compTmClosedEq
            dLeft
            compTy
            evTy
            (evalElSigma evd evRhs)
            lhsCorr
            compEq
      in
      compTmEqClosedEq
        dEq
        lhsComp
        body
        evTy
        (evalElSigma evd evRhs)
        evRhs
        compEq
    mkLeftCanon dEq dLeft evd body@(compTmClosedQtr _ compTy evTy evRhs corrRhs compa) =
      let
        lhsCorr = transTm dEq corrRhs
        lhsComp =
          compTmClosedQtr
            dLeft
            compTy
            evTy
            (evalElSigma evd evRhs)
            lhsCorr
            compa
      in
      compTmEqClosedQtr
        dEq
        lhsComp
        body
        evTy
        (evalElSigma evd evRhs)
        evRhs
        compa
        compa
  
    mkRightCanon :
      Derivable
        (termEq []
          (tmElSigma d' m')
          (subTm (sigmaCompSub sigmaTmEqRightFst sigmaTmEqRightSnd) m')
          (subTy (singleSubst d) M))
      -> Derivable (hasTy [] (tmElSigma d' m') (subTy (singleSubst d) M))
      -> d' =>e tmPair sigmaTmEqRightFst sigmaTmEqRightSnd
      -> Computable
           (hasTy []
             (subTm (sigmaCompSub sigmaTmEqRightFst sigmaTmEqRightSnd) m')
             (subTy (singleSubst d) M))
      -> Computable
           (termEq []
             (tmElSigma d' m')
             (subTm (sigmaCompSub sigmaTmEqRightFst sigmaTmEqRightSnd) m')
             (subTy (singleSubst d) M))
    mkRightCanon dEq dLeft evd body@(compTmClosedTop _ compTy evTy evRhs corrRhs) =
      let
        lhsCorr = transTm dEq corrRhs
        lhsComp =
          compTmClosedTop
            dLeft
            compTy
            evTy
            (evalElSigma evd evRhs)
            lhsCorr
      in
      compTmEqClosedTop dEq lhsComp body evTy (evalElSigma evd evRhs) evRhs
    mkRightCanon dEq dLeft evd body@(compTmClosedSigma _ compTy evTy evRhs corrRhs comp₁ comp₂) =
      let
        lhsCorr = transTm dEq corrRhs
        lhsComp =
          compTmClosedSigma
            dLeft
            compTy
            evTy
            (evalElSigma evd evRhs)
            lhsCorr
            comp₁
            comp₂
      in
      compTmEqClosedSigma
        dEq
        lhsComp
        body
        evTy
        (evalElSigma evd evRhs)
        evRhs
        (compReflTmClosed comp₁)
        (compReflTmClosed comp₂)
    mkRightCanon dEq dLeft evd body@(compTmClosedEq _ compTy evTy evRhs corrRhs compEq) =
      let
        lhsCorr = transTm dEq corrRhs
        lhsComp =
          compTmClosedEq
            dLeft
            compTy
            evTy
            (evalElSigma evd evRhs)
            lhsCorr
            compEq
      in
      compTmEqClosedEq
        dEq
        lhsComp
        body
        evTy
        (evalElSigma evd evRhs)
        evRhs
        compEq
    mkRightCanon dEq dLeft evd body@(compTmClosedQtr _ compTy evTy evRhs corrRhs compa) =
      let
        lhsCorr = transTm dEq corrRhs
        lhsComp =
          compTmClosedQtr
            dLeft
            compTy
            evTy
            (evalElSigma evd evRhs)
            lhsCorr
            compa
      in
      compTmEqClosedQtr
        dEq
        lhsComp
        body
        evTy
        (evalElSigma evd evRhs)
        evRhs
        compa
        compa
  
    leftCan : Computable
      (termEq []
        (tmElSigma d m)
        (subTm (sigmaCompSub sigmaTmEqLeftFst sigmaTmEqLeftSnd) m)
        (subTy (singleSubst d) M))
    leftCan = mkLeftCanon dLeftEq dLeftTy sigmaTmEqEvalLeftPair bodyLeft
  
    rightCan : Computable
      (termEq []
        (tmElSigma d' m')
        (subTm (sigmaCompSub sigmaTmEqRightFst sigmaTmEqRightSnd) m')
        (subTy (singleSubst d) M))
    rightCan = mkRightCanon dRightEq dRightTy sigmaTmEqEvalRightPair bodyRight
  
  compFQtrClosed : {A : RawType}
    -> Computable (isType [] A)
    -> Computable (isType [] (tyQtr A))
  compFQtrClosed compA =
    compTyClosedQtr
      (fQtr (compToDerivable compA))
      evalQtr
      (reflTy (fQtr (compToDerivable compA)))
      compA
  
  compIQtrClosed : {a : RawTerm} {A : RawType}
    -> Computable (hasTy [] a A)
    -> Computable (hasTy [] (tmClass a) (tyQtr A))
  compIQtrClosed compa =
    compTmClosedQtr
      (iQtr (compToDerivable compa))
      (compFQtrClosed (compTmToCompTy compa))
      evalQtr
      evalClass
      (reflTm (iQtr (compToDerivable compa)))
      compa
  
  compIQtrEqClosed : {a b : RawTerm} {A : RawType}
    -> Computable (hasTy [] a A)
    -> Computable (hasTy [] b A)
    -> Computable (termEq [] (tmClass a) (tmClass b) (tyQtr A))
  compIQtrEqClosed compa compb =
    compTmEqClosedQtr
      (iQtrEq (compToDerivable compa) (compToDerivable compb))
      (compIQtrClosed compa)
      (compIQtrClosed compb)
      evalQtr
      evalClass
      evalClass
      compa
      compb
  
  compCQtrClosed : {a l : RawTerm} {A L : RawType}
    -> HypComputable (isType ((tyQtr A) ∷ []) L)
    -> Computable (hasTy [] a A)
    -> HypComputable (hasTy (A ∷ []) l (qtrBranchTy L))
    -> HypComputable
         (termEq (wkTyBy 1 A ∷ A ∷ []) (wkTmBy 1 l) (renTm qtrSecondBranchRen l) (qtrCohTy L))
    -> Computable
         (termEq [] (tmElQtr l (tmClass a)) (subTm (qtrCompSub a) l)
           (subTy (singleSubst (tmClass a)) L))
  compCQtrClosed {a = a} {l = l} {A = A} {L = L}
    compL compa compl@(hypTmOpen neq dl compBranchTy sub subEq) coh =
    lhsEq body
    where
    dL : Derivable (isType ((tyQtr A) ∷ []) L)
    dL = hypCompToDerivable compL
  
    da : Derivable (hasTy [] a A)
    da = compToDerivable compa
  
    dcoh : Derivable
      (termEq (wkTyBy 1 A ∷ A ∷ []) (wkTmBy 1 l) (renTm qtrSecondBranchRen l) (qtrCohTy L))
    dcoh = hypCompToDerivable coh
  
    fits : Σ (FitsSubst [] (A ∷ []) (qtrCompSub a)) (λ fit -> ComputableFits fit)
    fits = qtrCompComputableFitsHelper compa
  
    rawBody : Computable
      (hasTy [] (subTm (qtrCompSub a) l) (subTy (qtrCompSub a) (qtrBranchTy L)))
    rawBody = sub (qtrCompSub a) (fst fits) (snd fits)
  
    body : Computable
      (hasTy [] (subTm (qtrCompSub a) l) (subTy (singleSubst (tmClass a)) L))
    body =
      subst
        (λ T -> Computable (hasTy [] (subTm (qtrCompSub a) l) T))
        (qtrBranchTyComp a L)
        rawBody
  
    dEq : Derivable
      (termEq [] (tmElQtr l (tmClass a)) (subTm (qtrCompSub a) l)
        (subTy (singleSubst (tmClass a)) L))
    dEq = cQtr dL da dl dcoh
  
    dLeft : Derivable
      (hasTy [] (tmElQtr l (tmClass a)) (subTy (singleSubst (tmClass a)) L))
    dLeft = assocTmLeft dEq
  
    lhsEq :
      Computable
        (hasTy [] (subTm (qtrCompSub a) l) (subTy (singleSubst (tmClass a)) L))
      -> Computable
           (termEq [] (tmElQtr l (tmClass a)) (subTm (qtrCompSub a) l)
             (subTy (singleSubst (tmClass a)) L))
    lhsEq body@(compTmClosedTop drhs compTy evTy evRhs corrRhs) =
      let
        lhsCorr = transTm dEq corrRhs
        lhsComp =
          compTmClosedTop
            dLeft
            compTy
            evTy
            (evalElQtr evalClass evRhs)
            lhsCorr
      in
      compTmEqClosedTop dEq lhsComp body evTy (evalElQtr evalClass evRhs) evRhs
    lhsEq body@(compTmClosedSigma drhs compTy evTy evRhs corrRhs comp₁ comp₂) =
      let
        lhsCorr = transTm dEq corrRhs
        lhsComp =
          compTmClosedSigma
            dLeft
            compTy
            evTy
            (evalElQtr evalClass evRhs)
            lhsCorr
            comp₁
            comp₂
      in
      compTmEqClosedSigma
        dEq
        lhsComp
        body
        evTy
        (evalElQtr evalClass evRhs)
        evRhs
        (compReflTmClosed comp₁)
        (compReflTmClosed comp₂)
    lhsEq body@(compTmClosedEq drhs compTy evTy evRhs corrRhs compEq) =
      let
        lhsCorr = transTm dEq corrRhs
        lhsComp =
          compTmClosedEq
            dLeft
            compTy
            evTy
            (evalElQtr evalClass evRhs)
            lhsCorr
            compEq
      in
      compTmEqClosedEq
        dEq
        lhsComp
        body
        evTy
        (evalElQtr evalClass evRhs)
        evRhs
        compEq
    lhsEq body@(compTmClosedQtr drhs compTy evTy evRhs corrRhs compx) =
      let
        lhsCorr = transTm dEq corrRhs
        lhsComp =
          compTmClosedQtr
            dLeft
            compTy
            evTy
            (evalElQtr evalClass evRhs)
            lhsCorr
            compx
      in
      compTmEqClosedQtr
        dEq
        lhsComp
        body
        evTy
        (evalElQtr evalClass evRhs)
        evRhs
        compx
        compx
  
  compEQtrClosed : {A L : RawType} {l l' p p' : RawTerm}
    -> HypComputable (isType ((tyQtr A) ∷ []) L)
    -> Computable (termEq [] p p' (tyQtr A))
    -> HypComputable (termEq (A ∷ []) l l' (qtrBranchTy L))
    -> HypComputable
         (termEq (wkTyBy 1 A ∷ A ∷ []) (wkTmBy 1 l) (renTm qtrSecondBranchRen l) (qtrCohTy L))
    -> HypComputable
         (termEq (wkTyBy 1 A ∷ A ∷ []) (wkTmBy 1 l') (renTm qtrSecondBranchRen l') (qtrCohTy L))
    -> Computable
         (termEq [] (tmElQtr l p) (tmElQtr l' p') (subTy (singleSubst p) L))
  compEQtrClosed {A = A} {L = L} {l = l} {l' = l'} {p = p} {p' = p'}
    compL comppp'
    compll'@(hypTmEqOpen neq dll' compBranchTy sub subEq)
    coh
    coh'@(hypTmEqOpen neqCoh' dcoh'comp compCohTy' subCoh' subEqCoh') =
    compTransTmClosed leftCan (compTransTmClosed bodyEqP (compSymTmClosed rightCan))
    where
    open ClosedQtrTmEqInv (invertQtrTmEq comppp' evalQtr)
  
    compQtr : Computable (isType [] (tyQtr A))
    compQtr = compTmToCompTy qtrTmEqCompLeft
  
    compClassLeft : Computable (hasTy [] (tmClass qtrTmEqLeftRepr) (tyQtr A))
    compClassLeft = compIQtrClosed qtrTmEqCompLeftRepr
  
    compClassRight : Computable (hasTy [] (tmClass qtrTmEqRightRepr) (tyQtr A))
    compClassRight = compIQtrClosed qtrTmEqCompRightRepr
  
    compLeftCorr : Computable
      (termEq [] p (tmClass qtrTmEqLeftRepr) (tyQtr A))
    compLeftCorr =
      compTmEqClosedQtr
        qtrTmEqLeftCorrClass
        qtrTmEqCompLeft
        compClassLeft
        evalQtr
        qtrTmEqEvalLeftClass
        evalClass
        qtrTmEqCompLeftRepr
        qtrTmEqCompLeftRepr
  
    compRightCorr : Computable
      (termEq [] p' (tmClass qtrTmEqRightRepr) (tyQtr A))
    compRightCorr =
      compTmEqClosedQtr
        qtrTmEqRightCorrClass
        qtrTmEqCompRight
        compClassRight
        evalQtr
        qtrTmEqEvalRightClass
        evalClass
        qtrTmEqCompRightRepr
        qtrTmEqCompRightRepr
  
    dL : Derivable (isType ((tyQtr A) ∷ []) L)
    dL = hypCompToDerivable compL
  
    dl : Derivable (hasTy (A ∷ []) l (qtrBranchTy L))
    dl = assocTmLeft dll'
  
    dl' : Derivable (hasTy (A ∷ []) l' (qtrBranchTy L))
    dl' = assocTmRight dll'
  
    dcoh : Derivable
      (termEq (wkTyBy 1 A ∷ A ∷ []) (wkTmBy 1 l) (renTm qtrSecondBranchRen l) (qtrCohTy L))
    dcoh = hypCompToDerivable coh
  
    dcoh' : Derivable
      (termEq (wkTyBy 1 A ∷ A ∷ []) (wkTmBy 1 l') (renTm qtrSecondBranchRen l') (qtrCohTy L))
    dcoh' = hypCompToDerivable coh'
  
    da : Derivable (hasTy [] qtrTmEqLeftRepr A)
    da = compToDerivable qtrTmEqCompLeftRepr
  
    db : Derivable (hasTy [] qtrTmEqRightRepr A)
    db = compToDerivable qtrTmEqCompRightRepr
  
    dHeadTyPath : A ≡ subTy (qtrCompSub qtrTmEqLeftRepr) (wkTyBy 1 A)
    dHeadTyPath =
      sym
        (cong (subTy (qtrCompSub qtrTmEqLeftRepr)) (renTyKeepSubstBy 1 A)
          ∙ subTyComp (qtrCompSub qtrTmEqLeftRepr) (keepSubstBy 1) A
          ∙ cong (λ rho -> subTy rho A) (funExt λ n -> refl)
          ∙ subTyId A)
  
    dbOnHead : Derivable
      (hasTy [] qtrTmEqRightRepr (subTy (qtrCompSub qtrTmEqLeftRepr) (wkTyBy 1 A)))
    dbOnHead = subst (λ T -> Derivable (hasTy [] qtrTmEqRightRepr T)) dHeadTyPath db
  
    compbOnHead : Computable
      (hasTy [] qtrTmEqRightRepr (subTy (qtrCompSub qtrTmEqLeftRepr) (wkTyBy 1 A)))
    compbOnHead =
      subst
        (λ T -> Computable (hasTy [] qtrTmEqRightRepr T))
        dHeadTyPath
        qtrTmEqCompRightRepr
  
    branchFitsLeft : Σ (FitsSubst [] (A ∷ []) (qtrCompSub qtrTmEqLeftRepr)) (λ fits -> ComputableFits fits)
    branchFitsLeft = qtrCompComputableFitsHelper qtrTmEqCompLeftRepr
  
    branchEqClassA : Computable
      (termEq []
        (subTm (qtrCompSub qtrTmEqLeftRepr) l)
        (subTm (qtrCompSub qtrTmEqLeftRepr) l')
        (subTy (singleSubst (tmClass qtrTmEqLeftRepr)) L))
    branchEqClassA =
      subst
        (λ T ->
          Computable
            (termEq []
              (subTm (qtrCompSub qtrTmEqLeftRepr) l)
              (subTm (qtrCompSub qtrTmEqLeftRepr) l')
              T))
        (qtrBranchTyComp qtrTmEqLeftRepr L)
        (sub
          (qtrCompSub qtrTmEqLeftRepr)
          (fst branchFitsLeft)
          (snd branchFitsLeft))
  
    cohFitsRight : FitsSubst [] (wkTyBy 1 A ∷ A ∷ [])
      (consSubst qtrTmEqRightRepr (consSubst qtrTmEqLeftRepr idSubst))
    cohFitsRight =
      fitsCons
        (fst (qtrCompComputableFitsHelper qtrTmEqCompLeftRepr))
        dbOnHead
  
    cohFitsRightComp : ComputableFits cohFitsRight
    cohFitsRightComp =
      compFitsCons
        (snd (qtrCompComputableFitsHelper qtrTmEqCompLeftRepr))
        compbOnHead
  
    cohEqClassA : Computable
      (termEq []
        (subTm (qtrCompSub qtrTmEqLeftRepr) l')
        (subTm (qtrCompSub qtrTmEqRightRepr) l')
        (subTy (singleSubst (tmClass qtrTmEqLeftRepr)) L))
    cohEqClassA =
      subst
        (λ t ->
          Computable
            (termEq []
              t
              (subTm (qtrCompSub qtrTmEqRightRepr) l')
              (subTy (singleSubst (tmClass qtrTmEqLeftRepr)) L)))
        (qtrCohLeftTmComp qtrTmEqLeftRepr qtrTmEqRightRepr l')
        (subst
          (λ u ->
            Computable
              (termEq []
                (subTm (consSubst qtrTmEqRightRepr (consSubst qtrTmEqLeftRepr idSubst))
                  (wkTmBy 1 l'))
                u
                (subTy (singleSubst (tmClass qtrTmEqLeftRepr)) L)))
          (qtrCohRightTmComp qtrTmEqLeftRepr qtrTmEqRightRepr l')
          (subst
            (λ T ->
              Computable
                (termEq []
                  (subTm (consSubst qtrTmEqRightRepr (consSubst qtrTmEqLeftRepr idSubst))
                    (wkTmBy 1 l'))
                  (subTm (consSubst qtrTmEqRightRepr (consSubst qtrTmEqLeftRepr idSubst))
                    (renTm qtrSecondBranchRen l'))
                  T))
            (qtrCohTyComp qtrTmEqLeftRepr qtrTmEqRightRepr L)
            (subCoh'
              (consSubst qtrTmEqRightRepr (consSubst qtrTmEqLeftRepr idSubst))
              cohFitsRight
              cohFitsRightComp)))
  
    bodyEqClassA : Computable
      (termEq []
        (subTm (qtrCompSub qtrTmEqLeftRepr) l)
        (subTm (qtrCompSub qtrTmEqRightRepr) l')
        (subTy (singleSubst (tmClass qtrTmEqLeftRepr)) L))
    bodyEqClassA = compTransTmClosed branchEqClassA cohEqClassA
  
    bodyEqP : Computable
      (termEq []
        (subTm (qtrCompSub qtrTmEqLeftRepr) l)
        (subTm (qtrCompSub qtrTmEqRightRepr) l')
        (subTy (singleSubst p) L))
    bodyEqP =
      compConvTmEqClosed
        bodyEqClassA
        (compSingleEqSubstTyClosed compL (compSymTmClosed compLeftCorr))
  
    bodyLeft : Computable
      (hasTy []
        (subTm (qtrCompSub qtrTmEqLeftRepr) l)
        (subTy (singleSubst p) L))
    bodyLeft = compTmEqLeft bodyEqP
  
    bodyRight : Computable
      (hasTy []
        (subTm (qtrCompSub qtrTmEqRightRepr) l')
        (subTy (singleSubst p) L))
    bodyRight = compTmEqRightClosed bodyEqP
  
    dLeftStep : Derivable
      (termEq [] (tmElQtr l p) (tmElQtr l (tmClass qtrTmEqLeftRepr)) (subTy (singleSubst p) L))
    dLeftStep =
      eQtrEq
        dL
        (compToDerivable compLeftCorr)
        (reflTm dl)
        dcoh
        dcoh
  
    dLeftCanon : Derivable
      (termEq []
        (tmElQtr l (tmClass qtrTmEqLeftRepr))
        (subTm (qtrCompSub qtrTmEqLeftRepr) l)
        (subTy (singleSubst p) L))
    dLeftCanon =
      convEq
        (cQtr dL da dl dcoh)
        (symTy (singleEqSubstTyHelper dL (compToDerivable compLeftCorr)))
  
    dLeftEq : Derivable
      (termEq []
        (tmElQtr l p)
        (subTm (qtrCompSub qtrTmEqLeftRepr) l)
        (subTy (singleSubst p) L))
    dLeftEq = transTm dLeftStep dLeftCanon
  
    dLeftTy : Derivable (hasTy [] (tmElQtr l p) (subTy (singleSubst p) L))
    dLeftTy = assocTmLeft dLeftEq
  
    dRightCanon0 : Derivable
      (termEq []
        (tmElQtr l' p')
        (subTm (qtrCompSub qtrTmEqRightRepr) l')
        (subTy (singleSubst p') L))
    dRightCanon0 =
      transTm
        (eQtrEq dL (compToDerivable compRightCorr) (reflTm dl') dcoh' dcoh')
        (convEq
          (cQtr dL db dl' dcoh')
          (symTy (singleEqSubstTyHelper dL (compToDerivable compRightCorr))))
  
    dRightEq : Derivable
      (termEq []
        (tmElQtr l' p')
        (subTm (qtrCompSub qtrTmEqRightRepr) l')
        (subTy (singleSubst p) L))
    dRightEq =
      convEq
        dRightCanon0
        (symTy (singleEqSubstTyHelper dL (compToDerivable comppp')))
  
    dRightTy : Derivable (hasTy [] (tmElQtr l' p') (subTy (singleSubst p) L))
    dRightTy = assocTmLeft dRightEq
  
    mkLeftCanon :
      Derivable
        (termEq []
          (tmElQtr l p)
          (subTm (qtrCompSub qtrTmEqLeftRepr) l)
          (subTy (singleSubst p) L))
      -> Derivable (hasTy [] (tmElQtr l p) (subTy (singleSubst p) L))
      -> p =>e tmClass qtrTmEqLeftRepr
      -> Computable
           (hasTy []
             (subTm (qtrCompSub qtrTmEqLeftRepr) l)
             (subTy (singleSubst p) L))
      -> Computable
           (termEq []
             (tmElQtr l p)
             (subTm (qtrCompSub qtrTmEqLeftRepr) l)
             (subTy (singleSubst p) L))
    mkLeftCanon dEq dLeft evp body@(compTmClosedTop _ compTy evTy evRhs corrRhs) =
      let
        lhsCorr = transTm dEq corrRhs
        lhsComp =
          compTmClosedTop
            dLeft
            compTy
            evTy
            (evalElQtr evp evRhs)
            lhsCorr
      in
      compTmEqClosedTop dEq lhsComp body evTy (evalElQtr evp evRhs) evRhs
    mkLeftCanon dEq dLeft evp body@(compTmClosedSigma _ compTy evTy evRhs corrRhs comp₁ comp₂) =
      let
        lhsCorr = transTm dEq corrRhs
        lhsComp =
          compTmClosedSigma
            dLeft
            compTy
            evTy
            (evalElQtr evp evRhs)
            lhsCorr
            comp₁
            comp₂
      in
      compTmEqClosedSigma
        dEq
        lhsComp
        body
        evTy
        (evalElQtr evp evRhs)
        evRhs
        (compReflTmClosed comp₁)
        (compReflTmClosed comp₂)
    mkLeftCanon dEq dLeft evp body@(compTmClosedEq _ compTy evTy evRhs corrRhs compEq) =
      let
        lhsCorr = transTm dEq corrRhs
        lhsComp =
          compTmClosedEq
            dLeft
            compTy
            evTy
            (evalElQtr evp evRhs)
            lhsCorr
            compEq
      in
      compTmEqClosedEq
        dEq
        lhsComp
        body
        evTy
        (evalElQtr evp evRhs)
        evRhs
        compEq
    mkLeftCanon dEq dLeft evp body@(compTmClosedQtr _ compTy evTy evRhs corrRhs compx) =
      let
        lhsCorr = transTm dEq corrRhs
        lhsComp =
          compTmClosedQtr
            dLeft
            compTy
            evTy
            (evalElQtr evp evRhs)
            lhsCorr
            compx
      in
      compTmEqClosedQtr
        dEq
        lhsComp
        body
        evTy
        (evalElQtr evp evRhs)
        evRhs
        compx
        compx
  
    mkRightCanon :
      Derivable
        (termEq []
          (tmElQtr l' p')
          (subTm (qtrCompSub qtrTmEqRightRepr) l')
          (subTy (singleSubst p) L))
      -> Derivable (hasTy [] (tmElQtr l' p') (subTy (singleSubst p) L))
      -> p' =>e tmClass qtrTmEqRightRepr
      -> Computable
           (hasTy []
             (subTm (qtrCompSub qtrTmEqRightRepr) l')
             (subTy (singleSubst p) L))
      -> Computable
           (termEq []
             (tmElQtr l' p')
             (subTm (qtrCompSub qtrTmEqRightRepr) l')
             (subTy (singleSubst p) L))
    mkRightCanon dEq dLeft evp body@(compTmClosedTop _ compTy evTy evRhs corrRhs) =
      let
        lhsCorr = transTm dEq corrRhs
        lhsComp =
          compTmClosedTop
            dLeft
            compTy
            evTy
            (evalElQtr evp evRhs)
            lhsCorr
      in
      compTmEqClosedTop dEq lhsComp body evTy (evalElQtr evp evRhs) evRhs
    mkRightCanon dEq dLeft evp body@(compTmClosedSigma _ compTy evTy evRhs corrRhs comp₁ comp₂) =
      let
        lhsCorr = transTm dEq corrRhs
        lhsComp =
          compTmClosedSigma
            dLeft
            compTy
            evTy
            (evalElQtr evp evRhs)
            lhsCorr
            comp₁
            comp₂
      in
      compTmEqClosedSigma
        dEq
        lhsComp
        body
        evTy
        (evalElQtr evp evRhs)
        evRhs
        (compReflTmClosed comp₁)
        (compReflTmClosed comp₂)
    mkRightCanon dEq dLeft evp body@(compTmClosedEq _ compTy evTy evRhs corrRhs compEq) =
      let
        lhsCorr = transTm dEq corrRhs
        lhsComp =
          compTmClosedEq
            dLeft
            compTy
            evTy
            (evalElQtr evp evRhs)
            lhsCorr
            compEq
      in
      compTmEqClosedEq
        dEq
        lhsComp
        body
        evTy
        (evalElQtr evp evRhs)
        evRhs
        compEq
    mkRightCanon dEq dLeft evp body@(compTmClosedQtr _ compTy evTy evRhs corrRhs compx) =
      let
        lhsCorr = transTm dEq corrRhs
        lhsComp =
          compTmClosedQtr
            dLeft
            compTy
            evTy
            (evalElQtr evp evRhs)
            lhsCorr
            compx
      in
      compTmEqClosedQtr
        dEq
        lhsComp
        body
        evTy
        (evalElQtr evp evRhs)
        evRhs
        compx
        compx
  
    leftCan : Computable
      (termEq []
        (tmElQtr l p)
        (subTm (qtrCompSub qtrTmEqLeftRepr) l)
        (subTy (singleSubst p) L))
    leftCan = mkLeftCanon dLeftEq dLeftTy qtrTmEqEvalLeftClass bodyLeft
  
    rightCan : Computable
      (termEq []
        (tmElQtr l' p')
        (subTm (qtrCompSub qtrTmEqRightRepr) l')
        (subTy (singleSubst p) L))
    rightCan = mkRightCanon dRightEq dRightTy qtrTmEqEvalRightClass bodyRight
  
  subSubJIntoPath : {theta gamma delta : Ctx} {rho sigma : Subst} {J : JForm}
    -> subJInto theta rho (subJInto gamma sigma J) ≡ subJInto theta (compSub rho sigma) J
  subSubJIntoPath {J = isType delta A} =
    cong (isType _) (subTyComp _ _ A)
  subSubJIntoPath {J = typeEq delta A B} =
    cong₂ (typeEq _)
      (subTyComp _ _ A)
      (subTyComp _ _ B)
  subSubJIntoPath {J = hasTy delta t A} =
    cong₂ (hasTy _)
      (subTmComp _ _ t)
      (subTyComp _ _ A)
  subSubJIntoPath {J = termEq delta t u A} =
    cong₃ (termEq _)
      (subTmComp _ _ t)
      (subTmComp _ _ u)
      (subTyComp _ _ A)
  
  subEqJIntoPath : {theta gamma delta : Ctx} {rho sigma tau : Subst} {J : JForm}
    -> subJInto theta rho (eqSubJInto gamma sigma tau J)
     ≡ eqSubJInto theta (compSub rho sigma) (compSub rho tau) J
  subEqJIntoPath {J = isType delta A} =
    cong₂ (typeEq _)
      (subTyComp _ _ A)
      (subTyComp _ _ A)
  subEqJIntoPath {J = typeEq delta A B} =
    cong₂ (typeEq _)
      (subTyComp _ _ A)
      (subTyComp _ _ B)
  subEqJIntoPath {J = hasTy delta t A} =
    cong₃ (termEq _)
      (subTmComp _ _ t)
      (subTmComp _ _ t)
      (subTyComp _ _ A)
  subEqJIntoPath {J = termEq delta t u A} =
    cong₃ (termEq _)
      (subTmComp _ _ t)
      (subTmComp _ _ u)
      (subTyComp _ _ A)
  
  eqSubSubJIntoPath : {theta gamma delta : Ctx} {rho eta sigma : Subst} {J : JForm}
    -> eqSubJInto theta rho eta (subJInto gamma sigma J)
     ≡ eqSubJInto theta (compSub rho sigma) (compSub eta sigma) J
  eqSubSubJIntoPath {J = isType delta A} =
    cong₂ (typeEq _)
      (subTyComp _ _ A)
      (subTyComp _ _ A)
  eqSubSubJIntoPath {J = typeEq delta A B} =
    cong₂ (typeEq _)
      (subTyComp _ _ A)
      (subTyComp _ _ B)
  eqSubSubJIntoPath {J = hasTy delta t A} =
    cong₃ (termEq _)
      (subTmComp _ _ t)
      (subTmComp _ _ t)
      (subTyComp _ _ A)
  eqSubSubJIntoPath {J = termEq delta t u A} =
    cong₃ (termEq _)
      (subTmComp _ _ t)
      (subTmComp _ _ u)
      (subTyComp _ _ A)
  
  eqSubEqJIntoPath : {theta gamma delta : Ctx} {rho eta sigma tau : Subst} {J : JForm}
    -> eqSubJInto theta rho eta (eqSubJInto gamma sigma tau J)
     ≡ eqSubJInto theta (compSub rho sigma) (compSub eta tau) J
  eqSubEqJIntoPath {J = isType delta A} =
    cong₂ (typeEq _)
      (subTyComp _ _ A)
      (subTyComp _ _ A)
  eqSubEqJIntoPath {J = typeEq delta A B} =
    cong₂ (typeEq _)
      (subTyComp _ _ A)
      (subTyComp _ _ B)
  eqSubEqJIntoPath {J = hasTy delta t A} =
    cong₃ (termEq _)
      (subTmComp _ _ t)
      (subTmComp _ _ t)
      (subTyComp _ _ A)
  eqSubEqJIntoPath {J = termEq delta t u A} =
    cong₃ (termEq _)
      (subTmComp _ _ t)
      (subTmComp _ _ u)
      (subTyComp _ _ A)
  
  wkJKeepPath : {delta : Ctx} {J : JForm}
    -> subJInto (delta ++ ctxOf J) (keepSubstBy (length delta)) J ≡ wkJBy delta J
  wkJKeepPath {delta = delta} {J = isType gamma A} =
    cong (isType _) (sym (renTyKeepSubstBy (length delta) A))
  wkJKeepPath {delta = delta} {J = typeEq gamma A B} =
    cong₂ (typeEq _)
      (sym (renTyKeepSubstBy (length delta) A))
      (sym (renTyKeepSubstBy (length delta) B))
  wkJKeepPath {delta = delta} {J = hasTy gamma t A} =
    cong₂ (hasTy _)
      (sym (renTmKeepSubstBy (length delta) t))
      (sym (renTyKeepSubstBy (length delta) A))
  wkJKeepPath {delta = delta} {J = termEq gamma t u A} =
    cong₃ (termEq _)
      (sym (renTmKeepSubstBy (length delta) t))
      (sym (renTmKeepSubstBy (length delta) u))
      (sym (renTyKeepSubstBy (length delta) A))
  
  compSubKeepBy : (sigma : Subst) (k : ℕ)
    -> compSub sigma (keepSubstBy k) ≡ dropSubstBy k sigma
  compSubKeepBy sigma k = funExt λ n -> refl
  
  subTyWkBy : (sigma : Subst) (k : ℕ) (A : RawType)
    -> subTy sigma (wkTyBy k A) ≡ subTy (dropSubstBy k sigma) A
  subTyWkBy sigma k A =
    cong (subTy sigma) (renTyKeepSubstBy k A)
    ∙ subTyComp sigma (keepSubstBy k) A
    ∙ cong (λ rho -> subTy rho A) (compSubKeepBy sigma k)
  
  subTmWkBy : (sigma : Subst) (k : ℕ) (t : RawTerm)
    -> subTm sigma (wkTmBy k t) ≡ subTm (dropSubstBy k sigma) t
  subTmWkBy sigma k t =
    cong (subTm sigma) (renTmKeepSubstBy k t)
    ∙ subTmComp sigma (keepSubstBy k) t
    ∙ cong (λ rho -> subTm rho t) (compSubKeepBy sigma k)
  
  wkTyBy0 : (A : RawType) -> wkTyBy 0 A ≡ A
  wkTyBy0 A =
    renTyKeepSubstBy 0 A
    ∙ cong (λ sigma -> subTy sigma A) keepSubstBy0Id
    ∙ subTyId A
  
  wkTmBy0 : (t : RawTerm) -> wkTmBy 0 t ≡ t
  wkTmBy0 t =
    renTmKeepSubstBy 0 t
    ∙ cong (λ sigma -> subTm sigma t) keepSubstBy0Id
    ∙ subTmId t
  
  dropCons : (t : RawTerm) (sigma : Subst) (k : ℕ)
    -> dropSubstBy (suc k) (consSubst t sigma) ≡ dropSubstBy k sigma
  dropCons t sigma k = funExt λ n -> refl
  
  subTyWkStep : (t : RawTerm) (sigma : Subst) (k : ℕ) (A : RawType)
    -> subTy (consSubst t sigma) (wkTyBy (suc k) A)
     ≡ subTy sigma (wkTyBy k A)
  subTyWkStep t sigma k A =
    subTyWkBy (consSubst t sigma) (suc k) A
    ∙ cong (λ rho -> subTy rho A) (dropCons t sigma k)
    ∙ sym (subTyWkBy sigma k A)
  
  lookupVarFits : {delta gamma : Ctx} {A : RawType} {sigma : Subst}
    -> FitsSubst [] (delta ++ (A ∷ gamma)) sigma
    -> Derivable
         (hasTy [] (subTm sigma (var (length delta)))
           (subTy sigma (wkTyBy (suc (length delta)) A)))
  lookupVarFits {delta = []} {A = A}
    (fitsCons {sigma = sigma} {t = t} fits dt) =
    subst
      (λ T -> Derivable (hasTy [] t T))
      (sym (subTyWkStep t sigma 0 A ∙ cong (subTy sigma) (wkTyBy0 A)))
      dt
  lookupVarFits {delta = D ∷ delta} {A = A}
    (fitsCons {sigma = sigma} {t = t} fits dt) =
    subst
      (λ T -> Derivable (hasTy [] (subTm sigma (var (length delta))) T))
      (sym (subTyWkStep t sigma (suc (length delta)) A))
      (lookupVarFits {delta = delta} {A = A} {sigma = sigma} fits)
  
  lookupVarFitsEq : {delta gamma : Ctx} {A : RawType} {sigma tau : Subst}
    -> FitsEqSubst [] (delta ++ (A ∷ gamma)) sigma tau
    -> Derivable
         (termEq [] (subTm sigma (var (length delta))) (subTm tau (var (length delta)))
           (subTy sigma (wkTyBy (suc (length delta)) A)))
  lookupVarFitsEq {delta = []} {A = A}
    (fitsEqCons {sigma = sigma} {tau = tau} {t = t} {u = u} fitsEq dtu) =
    subst
      (λ T -> Derivable (termEq [] t u T))
      (sym (subTyWkStep t sigma 0 A ∙ cong (subTy sigma) (wkTyBy0 A)))
      dtu
  lookupVarFitsEq {delta = D ∷ delta} {A = A}
    (fitsEqCons {sigma = sigma} {tau = tau} {t = t} {u = u} fitsEq dtu) =
    subst
      (λ T ->
        Derivable
          (termEq [] (subTm sigma (var (length delta))) (subTm tau (var (length delta))) T))
      (sym (subTyWkStep t sigma (suc (length delta)) A))
      (lookupVarFitsEq {delta = delta} {A = A} {sigma = sigma} {tau = tau} fitsEq)
  
  lookupCompFits : {delta gamma : Ctx} {A : RawType} {sigma : Subst}
    -> CompFitsSubst (delta ++ (A ∷ gamma)) sigma
    -> Computable
         (hasTy [] (subTm sigma (var (length delta)))
           (subTy sigma (wkTyBy (suc (length delta)) A)))
  lookupCompFits {delta = []} {A = A}
    (compFitsCons {sigma = sigma} {t = t} fits compt) =
    subst
      (λ T -> Computable (hasTy [] t T))
      (sym (subTyWkStep t sigma 0 A ∙ cong (subTy sigma) (wkTyBy0 A)))
      compt
  lookupCompFits {delta = D ∷ delta} {A = A}
    (compFitsCons {sigma = sigma} {t = t} fits compt) =
    subst
      (λ T -> Computable (hasTy [] (subTm sigma (var (length delta))) T))
      (sym (subTyWkStep t sigma (suc (length delta)) A))
      (lookupCompFits {delta = delta} {A = A} {sigma = sigma} fits)
  
  lookupCompFitsEq : {delta gamma : Ctx} {A : RawType} {sigma tau : Subst}
    -> CompFitsEqSubst (delta ++ (A ∷ gamma)) sigma tau
    -> Computable
         (termEq [] (subTm sigma (var (length delta))) (subTm tau (var (length delta)))
           (subTy sigma (wkTyBy (suc (length delta)) A)))
  lookupCompFitsEq {delta = []} {A = A}
    (compFitsEqCons {sigma = sigma} {tau = tau} {t = t} {u = u} fitsEq comptu) =
    subst
      (λ T -> Computable (termEq [] t u T))
      (sym (subTyWkStep t sigma 0 A ∙ cong (subTy sigma) (wkTyBy0 A)))
      comptu
  lookupCompFitsEq {delta = D ∷ delta} {A = A}
    (compFitsEqCons {sigma = sigma} {tau = tau} {t = t} {u = u} fitsEq comptu) =
    subst
      (λ T ->
        Computable
          (termEq [] (subTm sigma (var (length delta))) (subTm tau (var (length delta))) T))
      (sym (subTyWkStep t sigma (suc (length delta)) A))
      (lookupCompFitsEq {delta = delta} {A = A} {sigma = sigma} {tau = tau} fitsEq)
  
  dropFits : {delta : Ctx} {sigma : Subst}
    -> (drop : Ctx)
    -> FitsSubst [] (drop ++ delta) sigma
    -> FitsSubst [] delta (dropSubstBy (length drop) sigma)
  dropFits {delta = delta} {sigma = sigma} [] fits = fits
  dropFits {delta = delta} {sigma = sigma} (A ∷ drop)
    (fitsCons {sigma = sigmaTail} {t = t} fits dt) =
    subst
      (λ rho -> FitsSubst [] delta rho)
      (dropCons t sigmaTail (length drop))
      (dropFits {delta = delta} {sigma = sigmaTail} drop fits)
  
  dropFitsEq : {delta : Ctx} {sigma tau : Subst}
    -> (drop : Ctx)
    -> FitsEqSubst [] (drop ++ delta) sigma tau
    -> FitsEqSubst [] delta (dropSubstBy (length drop) sigma) (dropSubstBy (length drop) tau)
  dropFitsEq {delta = delta} {sigma = sigma} {tau = tau} [] fitsEq = fitsEq
  dropFitsEq {delta = delta} {sigma = sigma} {tau = tau} (A ∷ drop)
    (fitsEqCons {sigma = sigmaTail} {tau = tauTail} {t = t} {u = u} fitsEq dtu) =
    subst
      (λ rho ->
        FitsEqSubst [] delta rho
          (dropSubstBy (suc (length drop)) (consSubst u tauTail)))
      (dropCons t sigmaTail (length drop))
      (subst
        (λ rho ->
          FitsEqSubst [] delta
            (dropSubstBy (suc (length drop)) (consSubst t sigmaTail))
            rho)
        (dropCons u tauTail (length drop))
        (dropFitsEq {delta = delta} {sigma = sigmaTail} {tau = tauTail} drop fitsEq))
  
  dropCompFits : {delta : Ctx} {sigma : Subst}
    -> (drop : Ctx)
    -> CompFitsSubst (drop ++ delta) sigma
    -> CompFitsSubst delta (dropSubstBy (length drop) sigma)
  dropCompFits {delta = delta} {sigma = sigma} [] compFits = compFits
  dropCompFits {delta = delta} {sigma = sigma} (A ∷ drop)
    (compFitsCons {sigma = sigmaTail} {t = t} compFits compt) =
    subst
      (λ rho -> CompFitsSubst delta rho)
      (dropCons t sigmaTail (length drop))
      (dropCompFits {delta = delta} {sigma = sigmaTail} drop compFits)
  
  dropCompFitsEq : {delta : Ctx} {sigma tau : Subst}
    -> (drop : Ctx)
    -> CompFitsEqSubst (drop ++ delta) sigma tau
    -> CompFitsEqSubst delta (dropSubstBy (length drop) sigma) (dropSubstBy (length drop) tau)
  dropCompFitsEq {delta = delta} {sigma = sigma} {tau = tau} [] compFitsEq = compFitsEq
  dropCompFitsEq {delta = delta} {sigma = sigma} {tau = tau} (A ∷ drop)
    (compFitsEqCons {sigma = sigmaTail} {tau = tauTail} {t = t} {u = u} compFitsEq comptu) =
    subst
      (λ rho ->
        CompFitsEqSubst delta rho
          (dropSubstBy (suc (length drop)) (consSubst u tauTail)))
      (dropCons t sigmaTail (length drop))
      (subst
        (λ rho ->
          CompFitsEqSubst delta
            (dropSubstBy (suc (length drop)) (consSubst t sigmaTail))
            rho)
        (dropCons u tauTail (length drop))
        (dropCompFitsEq {delta = delta} {sigma = sigmaTail} {tau = tauTail} drop compFitsEq))
  
  closedEqSubTy : {gamma : Ctx} {A : RawType} {sigma tau : Subst}
    -> Derivable (isType [] A)
    -> CtxWF gamma
    -> Derivable (typeEq gamma (subTy sigma A) (subTy tau A))
  closedEqSubTy {gamma = gamma} {sigma = sigma} {tau = tau} dA wf =
    eqSubTyRule dA
      (fitsEqNil {gamma = gamma} {delta = []} {sigma = sigma} {tau = tau} wf)
  
  closedEqSubTyEq : {gamma : Ctx} {A B : RawType} {sigma tau : Subst}
    -> Derivable (typeEq [] A B)
    -> CtxWF gamma
    -> Derivable (typeEq gamma (subTy sigma A) (subTy tau B))
  closedEqSubTyEq {gamma = gamma} {sigma = sigma} {tau = tau} dAB wf =
    eqSubTyEqRule dAB
      (fitsEqNil {gamma = gamma} {delta = []} {sigma = sigma} {tau = tau} wf)
  
  closedEqSubTm : {gamma : Ctx} {t : RawTerm} {A : RawType} {sigma tau : Subst}
    -> Derivable (hasTy [] t A)
    -> CtxWF gamma
    -> Derivable (termEq gamma (subTm sigma t) (subTm tau t) (subTy sigma A))
  closedEqSubTm {gamma = gamma} {sigma = sigma} {tau = tau} dt wf =
    eqSubTmRule dt
      (fitsEqNil {gamma = gamma} {delta = []} {sigma = sigma} {tau = tau} wf)
  
  closedEqSubTmEq : {gamma : Ctx} {t u : RawTerm} {A : RawType} {sigma tau : Subst}
    -> Derivable (termEq [] t u A)
    -> CtxWF gamma
    -> Derivable (termEq gamma (subTm sigma t) (subTm tau u) (subTy sigma A))
  closedEqSubTmEq {gamma = gamma} {sigma = sigma} {tau = tau} dtu wf =
    eqSubTmEqRule dtu
      (fitsEqNil {gamma = gamma} {delta = []} {sigma = sigma} {tau = tau} wf)
  
  liftFits : {theta gamma : Ctx} {A : RawType} {sigma : Subst}
    -> FitsSubst theta gamma sigma
    -> Derivable (isType theta (subTy sigma A))
    -> FitsSubst (subTy sigma A ∷ theta) (A ∷ gamma)
         (consSubst (var zero) (compSub (keepSubstBy 1) sigma))
  liftFits {theta = theta} {gamma = gamma} {A = A} {sigma = sigma} fits dAσ =
    fitsCons tail headVar
    where
    wfAσ : CtxWF (subTy sigma A ∷ theta)
    wfAσ = wfCons (fitsSubstCtxWF fits) dAσ
  
    tail : FitsSubst (subTy sigma A ∷ theta) gamma (compSub (keepSubstBy 1) sigma)
    tail =
      composeFits
        (fitsKeep {delta = subTy sigma A ∷ []} {gamma = theta} wfAσ)
        fits
  
    headVar0 : Derivable
      (hasTy (subTy sigma A ∷ theta) (var zero) (wkTyBy 1 (subTy sigma A)))
    headVar0 = varStar {gamma = theta} {delta = []} {A = subTy sigma A} wfAσ dAσ
  
    headVar : Derivable
      (hasTy (subTy sigma A ∷ theta) (var zero) (subTy (compSub (keepSubstBy 1) sigma) A))
    headVar =
      subst
        (λ T -> Derivable (hasTy (subTy sigma A ∷ theta) (var zero) T))
        (renTyKeepSubstBy 1 (subTy sigma A) ∙ subTyComp (keepSubstBy 1) sigma A)
        headVar0
  
  liftFitsOne : {gamma : Ctx} {A : RawType} {sigma : Subst}
    -> FitsSubst [] gamma sigma
    -> Derivable (isType [] (subTy sigma A))
    -> FitsSubst (subTy sigma A ∷ []) (A ∷ gamma)
         (consSubst (var zero) (compSub (keepSubstBy 1) sigma))
  liftFitsOne = liftFits
  
  liftFitsEq : {theta gamma : Ctx} {A : RawType} {sigma tau : Subst}
    -> FitsEqSubst theta gamma sigma tau
    -> Derivable (isType theta (subTy sigma A))
    -> FitsEqSubst (subTy sigma A ∷ theta) (A ∷ gamma)
         (consSubst (var zero) (compSub (keepSubstBy 1) sigma))
         (consSubst (var zero) (compSub (keepSubstBy 1) tau))
  liftFitsEq {theta = theta} {gamma = gamma} {A = A} {sigma = sigma} {tau = tau} fitsEq dAσ =
    fitsEqCons tail (reflTm headVar)
    where
    wfAσ : CtxWF (subTy sigma A ∷ theta)
    wfAσ = wfCons (fitsEqSubstCtxWF fitsEq) dAσ
  
    tail : FitsEqSubst (subTy sigma A ∷ theta) gamma
      (compSub (keepSubstBy 1) sigma)
      (compSub (keepSubstBy 1) tau)
    tail =
      composeFitsEq
        (fitsKeep {delta = subTy sigma A ∷ []} {gamma = theta} wfAσ)
        fitsEq
  
    headVar0 : Derivable
      (hasTy (subTy sigma A ∷ theta) (var zero) (wkTyBy 1 (subTy sigma A)))
    headVar0 = varStar {gamma = theta} {delta = []} {A = subTy sigma A} wfAσ dAσ
  
    headVar : Derivable
      (hasTy (subTy sigma A ∷ theta) (var zero) (subTy (compSub (keepSubstBy 1) sigma) A))
    headVar =
      subst
        (λ T -> Derivable (hasTy (subTy sigma A ∷ theta) (var zero) T))
        (renTyKeepSubstBy 1 (subTy sigma A) ∙ subTyComp (keepSubstBy 1) sigma A)
        headVar0
  
  liftFitsEqOne : {gamma : Ctx} {A : RawType} {sigma tau : Subst}
    -> FitsEqSubst [] gamma sigma tau
    -> Derivable (isType [] (subTy sigma A))
    -> FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma)
         (consSubst (var zero) (compSub (keepSubstBy 1) sigma))
         (consSubst (var zero) (compSub (keepSubstBy 1) tau))
  liftFitsEqOne = liftFitsEq
  
  liftSubstCompKeep : (sigma : Subst)
    -> consSubst (var zero) (compSub (keepSubstBy 1) sigma) ≡ liftSubst sigma
  liftSubstCompKeep sigma = funExt λ where
    zero -> refl
    (suc n) -> sym (renTmKeepSubstBy 1 (sigma n))
  
  reflFitsEq : {gamma delta : Ctx} {sigma : Subst}
    -> FitsSubst gamma delta sigma
    -> FitsEqSubst gamma delta sigma sigma
  reflFitsEq {gamma = gamma} {sigma = sigma} (fitsNil wf) =
    fitsEqNil {gamma = gamma} {delta = []} {sigma = sigma} {tau = sigma} wf
  reflFitsEq (fitsCons fits dt) =
    fitsEqCons (reflFitsEq fits) (reflTm dt)
  
  compSubIdLeft : (sigma : Subst) -> compSub idSubst sigma ≡ sigma
  compSubIdLeft sigma = funExt λ n -> subTmId (sigma n)
  
  oneBinderCompSub : (tau sigma : Subst)
    -> consSubst (tau zero) (compSub (dropSubstBy 1 tau) sigma) ≡ compSub tau (liftSubst sigma)
  oneBinderCompSub tau sigma = funExt λ where
    zero -> refl
    (suc n) -> sym (subTmRen tau suc (sigma n))
  
  twoBinderCompSub : (tau sigma : Subst)
    -> consSubst (tau zero) (consSubst (tau (suc zero)) (compSub (dropSubstBy 2 tau) sigma))
         ≡ compSub tau (liftSubst (liftSubst sigma))
  twoBinderCompSub tau sigma = funExt λ where
    zero -> refl
    (suc zero) -> refl
    (suc (suc n)) ->
      sym
        (cong (subTm tau) (renTmComp suc suc (sigma n))
          ∙ subTmRen tau (compRen suc suc) (sigma n))
  
  composeOneBinder : {gamma : Ctx} {A : RawType} {sigma tau : Subst}
    -> FitsSubst [] gamma sigma
    -> Derivable (isType [] (subTy sigma A))
    -> FitsSubst [] (subTy sigma A ∷ []) tau
    -> FitsSubst [] (A ∷ gamma) (compSub tau (liftSubst sigma))
  composeOneBinder {gamma = gamma} {A = A} {sigma = sigma} {tau = tau} fits dAσ fits2 =
    subst
      (λ rho -> FitsSubst [] (A ∷ gamma) rho)
      (cong (compSub tau) (liftSubstCompKeep sigma))
      (composeFits fits2 (liftFitsOne fits dAσ))
  
  composeOneBinderEq : {gamma : Ctx} {A : RawType} {sigma tau₁ tau₂ : Subst}
    -> FitsSubst [] gamma sigma
    -> Derivable (isType [] (subTy sigma A))
    -> FitsEqSubst [] (subTy sigma A ∷ []) tau₁ tau₂
    -> FitsEqSubst [] (A ∷ gamma) (compSub tau₁ (liftSubst sigma)) (compSub tau₂ (liftSubst sigma))
  composeOneBinderEq {gamma = gamma} {A = A} {sigma = sigma} {tau₁ = tau₁} {tau₂ = tau₂} fits dAσ fitsEq =
    subst
      (λ rho -> FitsEqSubst [] (A ∷ gamma) rho (compSub tau₂ (liftSubst sigma)))
      (cong (compSub tau₁) (liftSubstCompKeep sigma))
      (subst
        (λ rho ->
          FitsEqSubst [] (A ∷ gamma)
            (compSub tau₁ (consSubst (var zero) (compSub (keepSubstBy 1) sigma)))
            rho)
        (cong (compSub tau₂) (liftSubstCompKeep sigma))
        (composeEqFits fitsEq (liftFitsOne fits dAσ)))
  
  composeTwoBinders : {gamma : Ctx} {A B : RawType} {sigma tau : Subst}
    -> FitsSubst [] gamma sigma
    -> Derivable (isType [] (subTy sigma A))
    -> Derivable (isType (subTy sigma A ∷ []) (subTy (liftSubst sigma) B))
    -> FitsSubst [] (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) tau
    -> FitsSubst [] (B ∷ A ∷ gamma) (compSub tau (liftSubst (liftSubst sigma)))
  composeTwoBinders {gamma = gamma} {A = A} {B = B} {sigma = sigma} {tau = tau} fits dAσ dBσ fits2 =
    let
      lifted1 : FitsSubst (subTy sigma A ∷ []) (A ∷ gamma) (liftSubst sigma)
      lifted1 =
        subst
          (λ rho -> FitsSubst (subTy sigma A ∷ []) (A ∷ gamma) rho)
          (liftSubstCompKeep sigma)
          (liftFitsOne fits dAσ)
    in
    subst
      (λ rho -> FitsSubst [] (B ∷ A ∷ gamma) rho)
      (cong (compSub tau) (liftSubstCompKeep (liftSubst sigma)))
      (composeFits fits2 (liftFits lifted1 dBσ))
  
  composeTwoBindersEq : {gamma : Ctx} {A B : RawType} {sigma tau₁ tau₂ : Subst}
    -> FitsSubst [] gamma sigma
    -> Derivable (isType [] (subTy sigma A))
    -> Derivable (isType (subTy sigma A ∷ []) (subTy (liftSubst sigma) B))
    -> FitsEqSubst [] (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) tau₁ tau₂
    -> FitsEqSubst [] (B ∷ A ∷ gamma)
         (compSub tau₁ (liftSubst (liftSubst sigma)))
         (compSub tau₂ (liftSubst (liftSubst sigma)))
  composeTwoBindersEq {gamma = gamma} {A = A} {B = B} {sigma = sigma} {tau₁ = tau₁} {tau₂ = tau₂} fits dAσ dBσ fitsEq =
    let
      lifted1 : FitsSubst (subTy sigma A ∷ []) (A ∷ gamma) (liftSubst sigma)
      lifted1 =
        subst
          (λ rho -> FitsSubst (subTy sigma A ∷ []) (A ∷ gamma) rho)
          (liftSubstCompKeep sigma)
          (liftFitsOne fits dAσ)
    in
    subst
      (λ rho ->
        FitsEqSubst [] (B ∷ A ∷ gamma) rho (compSub tau₂ (liftSubst (liftSubst sigma))))
      (cong (compSub tau₁) (liftSubstCompKeep (liftSubst sigma)))
      (subst
        (λ rho ->
          FitsEqSubst [] (B ∷ A ∷ gamma)
            (compSub tau₁ (consSubst (var zero) (compSub (keepSubstBy 1) (liftSubst sigma))))
            rho)
        (cong (compSub tau₂) (liftSubstCompKeep (liftSubst sigma)))
        (composeEqFits fitsEq (liftFits lifted1 dBσ)))
  
  singleSubstCompLift : (sigma : Subst) (t : RawTerm)
    -> compSub (singleSubst (subTm sigma t)) (liftSubst sigma) ≡ compSub sigma (singleSubst t)
  singleSubstCompLift sigma t = funExt λ where
    zero -> refl
    (suc n) ->
      subTmRen (singleSubst (subTm sigma t)) suc (sigma n)
      ∙ cong (λ rho -> subTm rho (sigma n)) (funExt λ k -> refl)
      ∙ subTmId (sigma n)
  
  qtrBranchSubLiftComp : (sigma : Subst)
    -> compSub (liftSubst sigma) qtrBranchSub ≡ compSub qtrBranchSub (liftSubst sigma)
  qtrBranchSubLiftComp sigma = funExt λ where
    zero -> refl
    (suc n) ->
      sym (subTmId (renTm suc (sigma n)))
      ∙ subTmRen idSubst suc (sigma n)
      ∙ cong (λ rho -> subTm rho (sigma n)) (sym (funExt λ k -> refl))
      ∙ sym (subTmRen qtrBranchSub suc (sigma n))
  
  sigmaCompSubLiftComp : (sigma : Subst) (b c : RawTerm)
    -> compSub sigma (sigmaCompSub b c)
     ≡ compSub (sigmaCompSub (subTm sigma b) (subTm sigma c)) (liftSubst (liftSubst sigma))
  sigmaCompSubLiftComp sigma b c = funExt λ where
    zero -> refl
    (suc zero) -> refl
    (suc (suc n)) ->
      sym (subTmId (sigma n))
      ∙ cong
          (λ rho -> subTm rho (sigma n))
          (sym (funExt λ k -> refl))
      ∙ sym (subTmRen (sigmaCompSub (subTm sigma b) (subTm sigma c)) (compRen suc suc) (sigma n))
      ∙ cong
          (λ t -> subTm (sigmaCompSub (subTm sigma b) (subTm sigma c)) t)
          (sym (renTmComp suc suc (sigma n)))
  
  sigmaMotSubLiftComp : (sigma : Subst)
    -> compSub (liftSubst (liftSubst sigma)) sigmaMotSub ≡ compSub sigmaMotSub (liftSubst sigma)
  sigmaMotSubLiftComp sigma = funExt λ where
    zero -> refl
    (suc n) ->
      renTmComp suc suc (sigma n)
      ∙ sym (subTmId (renTm (addRen 2) (sigma n)))
      ∙ subTmRen idSubst (addRen 2) (sigma n)
      ∙ sym (subTmRen sigmaMotSub suc (sigma n))
  
  qtrCohSubLiftComp : (sigma : Subst)
    -> compSub (liftSubst (liftSubst sigma)) qtrCohSub ≡ compSub qtrCohSub (liftSubst sigma)
  qtrCohSubLiftComp sigma = funExt λ where
    zero -> refl
    (suc n) ->
      renTmComp suc suc (sigma n)
      ∙ sym (subTmId (renTm (addRen 2) (sigma n)))
      ∙ subTmRen idSubst (addRen 2) (sigma n)
      ∙ sym (subTmRen qtrCohSub suc (sigma n))
  
  sigmaBranchTyLiftComp : (sigma : Subst) (M : RawType)
    -> subTy (liftSubst (liftSubst sigma)) (sigmaBranchTy M)
         ≡ sigmaBranchTy (subTy (liftSubst sigma) M)
  sigmaBranchTyLiftComp sigma M =
    subTyComp (liftSubst (liftSubst sigma)) sigmaMotSub M
    ∙ cong (λ rho -> subTy rho M) (sigmaMotSubLiftComp sigma)
    ∙ sym (subTyComp sigmaMotSub (liftSubst sigma) M)
  
  qtrBranchTyLiftComp : (sigma : Subst) (L : RawType)
    -> subTy (liftSubst sigma) (qtrBranchTy L)
         ≡ qtrBranchTy (subTy (liftSubst sigma) L)
  qtrBranchTyLiftComp sigma L =
    subTyComp (liftSubst sigma) qtrBranchSub L
    ∙ cong (λ rho -> subTy rho L) (qtrBranchSubLiftComp sigma)
    ∙ sym (subTyComp qtrBranchSub (liftSubst sigma) L)
  
  qtrCohTyLiftComp : (sigma : Subst) (L : RawType)
    -> subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)
         ≡ qtrCohTy (subTy (liftSubst sigma) L)
  qtrCohTyLiftComp sigma L =
    subTyComp (liftSubst (liftSubst sigma)) qtrCohSub L
    ∙ cong (λ rho -> subTy rho L) (qtrCohSubLiftComp sigma)
    ∙ sym (subTyComp qtrCohSub (liftSubst sigma) L)
  
  qtrSecondBranchRenPath : qtrSecondBranchRen ≡ raiseRen suc
  qtrSecondBranchRenPath = funExt λ where
    zero -> refl
    (suc n) -> refl
  
  qtrSecondBranchSubLiftComp : (sigma : Subst)
    -> (λ n -> liftSubst (liftSubst sigma) (qtrSecondBranchRen n))
         ≡ renSub qtrSecondBranchRen (liftSubst sigma)
  qtrSecondBranchSubLiftComp sigma = funExt λ where
    zero -> refl
    (suc n) ->
      renTmComp suc suc (sigma n)
      ∙ cong
          (λ rho -> renTm rho (sigma n))
          (funExt λ where
            zero -> refl
            (suc k) -> refl)
      ∙ sym (renTmComp qtrSecondBranchRen suc (sigma n))
  
  qtrSecondBranchTmLiftComp : (sigma : Subst) (l : RawTerm)
    -> subTm (liftSubst (liftSubst sigma)) (renTm qtrSecondBranchRen l)
         ≡ renTm qtrSecondBranchRen (subTm (liftSubst sigma) l)
  qtrSecondBranchTmLiftComp sigma l =
    subTmRen (liftSubst (liftSubst sigma)) qtrSecondBranchRen l
    ∙ cong
        (λ theta -> subTm theta l)
        (qtrSecondBranchSubLiftComp sigma)
    ∙ sym (renTmSub qtrSecondBranchRen (liftSubst sigma) l)
  
  qtrCompSubLiftComp : (sigma : Subst) (a : RawTerm)
    -> compSub sigma (qtrCompSub a)
         ≡ compSub (qtrCompSub (subTm sigma a)) (liftSubst sigma)
  qtrCompSubLiftComp sigma a =
    cong
      (compSub sigma)
      (sym (singleSubstConsKeep a ∙ cong (consSubst a) keepSubstBy0Id))
    ∙ sym (singleSubstCompLift sigma a)
    ∙ cong
        (λ rho -> compSub rho (liftSubst sigma))
        (singleSubstConsKeep (subTm sigma a)
          ∙ cong (consSubst (subTm sigma a)) keepSubstBy0Id)
  
  qtrBranchTyWk : (L : RawType)
    -> wkTyBy 1 (qtrBranchTy L) ≡ qtrCohTy L
  qtrBranchTyWk L =
    renTySub suc qtrBranchSub L
    ∙ cong
        (λ rho -> subTy rho L)
        (funExt λ where
          zero -> refl
          (suc n) -> refl)
  
  fitsToCompFits : {gamma : Ctx} {sigma : Subst}
    -> FitsSubst [] gamma sigma
    -> CompFitsSubst gamma sigma
  fitsToCompFits (fitsNil wf) = compFitsNil
  fitsToCompFits (fitsCons {sigma = sigmaTail} {A = A} {t = t} fits dt) =
    compFitsCons
      (fitsToCompFits fits)
      (subst
        (λ J -> Computable J)
        (cong₂ (hasTy [])
          (subTmId t)
          (subTyId (subTy sigmaTail A)))
        (substDerivTmComp
          dt
          (fitsNil {gamma = []} {delta = []} {sigma = idSubst} wfNil)
          compFitsNil))

  fitsEqToCompFitsEq : {gamma : Ctx} {sigma tau : Subst}
    -> FitsEqSubst [] gamma sigma tau
    -> CompFitsEqSubst gamma sigma tau
  fitsEqToCompFitsEq (fitsEqNil wf) = compFitsEqNil
  fitsEqToCompFitsEq (fitsEqCons {sigma = sigmaTail} {A = A} {t = t} {u = u} fitsEq dtu) =
    compFitsEqCons
      (fitsEqToCompFitsEq fitsEq)
      (subst
        (λ J -> Computable J)
        (cong₃ (termEq [])
          (subTmId t)
          (subTmId u)
          (subTyId (subTy sigmaTail A)))
        (substDerivTmEqComp
          dtu
          (fitsNil {gamma = []} {delta = []} {sigma = idSubst} wfNil)
          compFitsNil))

  packClosedSubst : {J : JForm} {sigma : Subst}
    -> FitsSubst [] (ctxOf J) sigma
    -> Computable (closedSubJ sigma J)
    -> ClosedSubstComp J sigma
  packClosedSubst fits comp = closedSubstComp comp (fitsToCompFits fits)

  packClosedEqSubst : {J : JForm} {sigma tau : Subst}
    -> FitsEqSubst [] (ctxOf J) sigma tau
    -> Computable (closedEqSubJ sigma tau J)
    -> ClosedEqSubstComp J sigma tau
  packClosedEqSubst fitsEq comp = closedEqSubstComp comp (fitsEqToCompFitsEq fitsEq)

  composeCompFits : {gamma delta : Ctx} {sigma sigma' : Subst}
    -> FitsSubst gamma delta sigma'
    -> FitsSubst [] gamma sigma
    -> CompFitsSubst gamma sigma
    -> CompFitsSubst delta (compSub sigma sigma')
  composeCompFits fits' fits cFits =
    compFitsEqLeft (composeCompFitsEq fits cFits (reflFitsEq fits'))

  composeCompEqFits : {gamma delta : Ctx} {sigma tau sigma' : Subst}
    -> FitsEqSubst [] gamma sigma tau
    -> CompFitsEqSubst gamma sigma tau
    -> FitsSubst gamma delta sigma'
    -> CompFitsEqSubst delta (compSub sigma sigma') (compSub tau sigma')
  composeCompEqFits fitsEq cFitsEq (fitsNil wf) = compFitsEqNil
  composeCompEqFits {sigma = sigma} {tau = tau} fitsEq cFitsEq
    (fitsCons {delta = delta} {sigma = sigma'} {A = A} {t = t} fits' dt) =
    subst
      (λ zeta -> CompFitsEqSubst (A ∷ delta) zeta (compSub tau (consSubst t sigma')))
      (sym (compSubCons sigma t sigma'))
      (subst
        (λ zeta ->
          CompFitsEqSubst (A ∷ delta) (consSubst (subTm sigma t) (compSub sigma sigma')) zeta)
        (sym (compSubCons tau t sigma'))
        (compFitsEqCons
          (composeCompEqFits fitsEq cFitsEq fits')
          (subst
            (λ T -> Computable (termEq [] (subTm sigma t) (subTm tau t) T))
            (subTyComp sigma sigma' A)
            (eqSubDerivTmComp dt fitsEq cFitsEq))))

  composeCompFitsEq : {gamma delta : Ctx} {sigma sigma' tau' : Subst}
    -> FitsSubst [] gamma sigma
    -> CompFitsSubst gamma sigma
    -> FitsEqSubst gamma delta sigma' tau'
    -> CompFitsEqSubst delta (compSub sigma sigma') (compSub sigma tau')
  composeCompFitsEq fits cFits fitsEq' =
    composeCompEqFitsEq (reflFitsEq fits) (reflCompFitsEq cFits) fitsEq'

  composeCompEqFitsEq : {gamma delta : Ctx} {sigma tau sigma' tau' : Subst}
    -> FitsEqSubst [] gamma sigma tau
    -> CompFitsEqSubst gamma sigma tau
    -> FitsEqSubst gamma delta sigma' tau'
    -> CompFitsEqSubst delta (compSub sigma sigma') (compSub tau tau')
  composeCompEqFitsEq fitsEq cFitsEq (fitsEqNil wf) = compFitsEqNil
  composeCompEqFitsEq {sigma = sigma} {tau = tau} fitsEq cFitsEq
    (fitsEqCons {delta = delta} {sigma = sigma'} {tau = tau'} {A = A} {t = t} {u = u} fitsEq' dtu) =
    subst
      (λ zeta -> CompFitsEqSubst (A ∷ delta) zeta (compSub tau (consSubst u tau')))
      (sym (compSubCons sigma t sigma'))
      (subst
        (λ zeta ->
          CompFitsEqSubst (A ∷ delta) (consSubst (subTm sigma t) (compSub sigma sigma')) zeta)
        (sym (compSubCons tau u tau'))
        (compFitsEqCons
          (composeCompEqFitsEq fitsEq cFitsEq fitsEq')
          (subst
            (λ T -> Computable (termEq [] (subTm sigma t) (subTm tau u) T))
            (subTyComp sigma sigma' A)
            (eqSubDerivTmEqComp dtu fitsEq cFitsEq))))

  singleClosedCompFits : {A : RawType} {tau : Subst}
    -> FitsSubst [] (A ∷ []) tau
    -> CompFitsSubst (A ∷ []) tau
  singleClosedCompFits (fitsCons {sigma = sigmaTail} {A = A} {t = t} (fitsNil wf) dt) =
    compFitsCons
      {sigma = sigmaTail}
      compFitsNil
      (subst
        (λ J -> Computable J)
        (cong₂ (hasTy [])
          (subTmId t)
          (subTyId (subTy sigmaTail A)))
        (substDerivTmComp dt (fitsNil {gamma = []} {delta = []} {sigma = idSubst} wfNil) compFitsNil))

  singleClosedCompFitsEq : {A : RawType} {tau₁ tau₂ : Subst}
    -> FitsEqSubst [] (A ∷ []) tau₁ tau₂
    -> CompFitsEqSubst (A ∷ []) tau₁ tau₂
  singleClosedCompFitsEq (fitsEqCons {sigma = sigmaTail} {A = A} {t = t} {u = u} (fitsEqNil wf) dtu) =
    compFitsEqCons
      {sigma = sigmaTail}
      compFitsEqNil
      (subst
        (λ J -> Computable J)
        (cong₃ (termEq [])
          (subTmId t)
          (subTmId u)
          (subTyId (subTy sigmaTail A)))
        (substDerivTmEqComp dtu (fitsNil {gamma = []} {delta = []} {sigma = idSubst} wfNil) compFitsNil))

  doubleClosedCompFits : {A B : RawType} {tau : Subst}
    -> FitsSubst [] (B ∷ A ∷ []) tau
    -> CompFitsSubst (B ∷ A ∷ []) tau
  doubleClosedCompFits
    (fitsCons
      {sigma = sigmaTail1} {A = B} {t = t1}
      (fitsCons {sigma = sigmaTail0} {A = A} {t = t0} (fitsNil wf) dt0)
      dt1) =
    compFitsCons
      {sigma = sigmaTail1}
      (compFitsCons
        {sigma = sigmaTail0}
        compFitsNil
        (subst
          (λ J -> Computable J)
          (cong₂ (hasTy [])
            (subTmId t0)
            (subTyId (subTy sigmaTail0 A)))
          (substDerivTmComp dt0 (fitsNil {gamma = []} {delta = []} {sigma = idSubst} wfNil) compFitsNil)))
      (subst
        (λ J -> Computable J)
        (cong₂ (hasTy [])
          (subTmId t1)
          (subTyId (subTy sigmaTail1 B)))
        (substDerivTmComp dt1 (fitsNil {gamma = []} {delta = []} {sigma = idSubst} wfNil) compFitsNil))

  doubleClosedCompFitsEq : {A B : RawType} {tau₁ tau₂ : Subst}
    -> FitsEqSubst [] (B ∷ A ∷ []) tau₁ tau₂
    -> CompFitsEqSubst (B ∷ A ∷ []) tau₁ tau₂
  doubleClosedCompFitsEq
    (fitsEqCons
      {sigma = sigmaTail1} {tau = tauTail1} {A = B} {t = t1} {u = u1}
      (fitsEqCons {sigma = sigmaTail0} {tau = tauTail0} {A = A} {t = t0} {u = u0} (fitsEqNil wf) dtu0)
      dtu1) =
    compFitsEqCons
      {sigma = sigmaTail1} {tau = tauTail1}
      (compFitsEqCons
        {sigma = sigmaTail0} {tau = tauTail0}
        compFitsEqNil
        (subst
          (λ J -> Computable J)
          (cong₃ (termEq [])
            (subTmId t0)
            (subTmId u0)
            (subTyId (subTy sigmaTail0 A)))
          (substDerivTmEqComp dtu0 (fitsNil {gamma = []} {delta = []} {sigma = idSubst} wfNil) compFitsNil)))
      (subst
        (λ J -> Computable J)
        (cong₃ (termEq [])
          (subTmId t1)
          (subTmId u1)
          (subTyId (subTy sigmaTail1 B)))
        (substDerivTmEqComp dtu1 (fitsNil {gamma = []} {delta = []} {sigma = idSubst} wfNil) compFitsNil))

  substClosedCompFits : {gamma : Ctx} {sigma rho : Subst}
    -> CompFitsSubst gamma sigma
    -> CompFitsSubst gamma (compSub rho sigma)
  substClosedCompFits {rho = rho} compFitsNil = compFitsNil
  substClosedCompFits {rho = rho}
    (compFitsCons {gamma = gamma} {sigma = sigma} {A = A} {t = t} cFits compt) =
    subst
      (λ zeta -> CompFitsSubst (A ∷ gamma) zeta)
      (sym (compSubCons rho t sigma))
      (compFitsCons
        (substClosedCompFits {sigma = sigma} {rho = rho} cFits)
        (subst
          (λ T -> Computable (hasTy [] (subTm rho t) T))
          (subTyComp rho sigma A)
          (compTmEqLeft
            (eqSubDerivTmComp
              (compToDerivable compt)
              (fitsEqNil {gamma = []} {delta = []} {sigma = rho} {tau = idSubst} wfNil)
              compFitsEqNil))))

  eqSubClosedCompFits : {gamma : Ctx} {sigma rho eta : Subst}
    -> CompFitsSubst gamma sigma
    -> CompFitsEqSubst gamma (compSub rho sigma) (compSub eta sigma)
  eqSubClosedCompFits {rho = rho} {eta = eta} compFitsNil = compFitsEqNil
  eqSubClosedCompFits {rho = rho} {eta = eta}
    (compFitsCons {gamma = gamma} {sigma = sigma} {A = A} {t = t} cFits compt) =
    subst
      (λ zeta -> CompFitsEqSubst (A ∷ gamma) zeta (compSub eta (consSubst t sigma)))
      (sym (compSubCons rho t sigma))
      (subst
        (λ zeta ->
          CompFitsEqSubst (A ∷ gamma) (consSubst (subTm rho t) (compSub rho sigma)) zeta)
        (sym (compSubCons eta t sigma))
        (compFitsEqCons
          (eqSubClosedCompFits {sigma = sigma} {rho = rho} {eta = eta} cFits)
          (subst
            (λ T -> Computable (termEq [] (subTm rho t) (subTm eta t) T))
            (subTyComp rho sigma A)
            (eqSubDerivTmComp
              (compToDerivable compt)
              (fitsEqNil {gamma = []} {delta = []} {sigma = rho} {tau = eta} wfNil)
              compFitsEqNil))))

  reflCompFitsEq : {gamma : Ctx} {sigma : Subst}
    -> CompFitsSubst gamma sigma
    -> CompFitsEqSubst gamma sigma sigma
  reflCompFitsEq {gamma = gamma} {sigma = sigma} cFits =
    subst
      (λ rho -> CompFitsEqSubst gamma rho sigma)
      (compSubIdLeft sigma)
      (subst
        (λ rho -> CompFitsEqSubst gamma (compSub idSubst sigma) rho)
        (compSubIdLeft sigma)
        (eqSubClosedCompFits {sigma = sigma} {rho = idSubst} {eta = idSubst} cFits))

  composeOneBinderComp : {gamma : Ctx} {A : RawType} {sigma tau : Subst}
    -> FitsSubst [] (subTy sigma A ∷ []) tau
    -> CompFitsSubst gamma sigma
    -> CompFitsSubst (A ∷ gamma) (compSub tau (liftSubst sigma))
  composeOneBinderComp fits cFits =
    compFitsEqLeft (composeOneBinderCompEq cFits (reflFitsEq fits))

  composeOneBinderCompEq : {gamma : Ctx} {A : RawType} {sigma tau₁ tau₂ : Subst}
    -> CompFitsSubst gamma sigma
    -> FitsEqSubst [] (subTy sigma A ∷ []) tau₁ tau₂
    -> CompFitsEqSubst (A ∷ gamma)
         (compSub tau₁ (liftSubst sigma))
         (compSub tau₂ (liftSubst sigma))
  composeOneBinderCompEq {gamma = gamma} {A = A} {sigma = sigma} {tau₁ = tau₁} {tau₂ = tau₂} cFits
    (fitsEqCons {sigma = tauTail₁} {tau = tauTail₂} {t = t} {u = u} (fitsEqNil wf) dtu) =
    subst
      (λ rho -> CompFitsEqSubst (A ∷ gamma) rho (compSub tau₂ (liftSubst sigma)))
      (oneBinderCompSub tau₁ sigma)
      (subst
        (λ rho ->
          CompFitsEqSubst (A ∷ gamma)
            (consSubst t (compSub tauTail₁ sigma))
            rho)
        (oneBinderCompSub tau₂ sigma)
        (compFitsEqCons
          (eqSubClosedCompFits
            {rho = tauTail₁}
            {eta = tauTail₂}
            cFits)
          (subst
            (λ T -> Computable (termEq [] t u T))
            (subTyComp tauTail₁ sigma A)
            (subst
              (λ J -> Computable J)
              (cong₃ (termEq [])
                (subTmId t)
                (subTmId u)
                (subTyId (subTy tauTail₁ (subTy sigma A))))
              (substDerivTmEqComp
                dtu
                (fitsNil {gamma = []} {delta = []} {sigma = idSubst} wfNil)
                compFitsNil)))))

  composeTwoBindersComp : {gamma : Ctx} {A B : RawType} {sigma tau : Subst}
    -> CompFitsSubst gamma sigma
    -> FitsSubst [] (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) tau
    -> CompFitsSubst (B ∷ A ∷ gamma) (compSub tau (liftSubst (liftSubst sigma)))
  composeTwoBindersComp cFits fits =
    compFitsEqLeft (composeTwoBindersCompEq cFits (reflFitsEq fits))

  composeTwoBindersCompEq : {gamma : Ctx} {A B : RawType} {sigma tau₁ tau₂ : Subst}
    -> CompFitsSubst gamma sigma
    -> FitsEqSubst [] (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) tau₁ tau₂
    -> CompFitsEqSubst (B ∷ A ∷ gamma)
         (compSub tau₁ (liftSubst (liftSubst sigma)))
         (compSub tau₂ (liftSubst (liftSubst sigma)))
  composeTwoBindersCompEq {gamma = gamma} {A = A} {B = B} {sigma = sigma} {tau₁ = tau₁} {tau₂ = tau₂}
    cFits
    (fitsEqCons {sigma = tauTail₁} {tau = etaTail₁} {t = t₁} {u = u₁}
      (fitsEqCons {sigma = tauTail₀} {tau = etaTail₀} {t = t₀} {u = u₀} (fitsEqNil wf) dtu₀)
      dtu₁) =
    subst
      (λ rho ->
        CompFitsEqSubst (B ∷ A ∷ gamma) rho (compSub tau₂ (liftSubst (liftSubst sigma))))
      (twoBinderCompSub tau₁ sigma)
      (subst
        (λ rho ->
          CompFitsEqSubst (B ∷ A ∷ gamma)
            (consSubst t₁ (consSubst t₀ (compSub tauTail₀ sigma)))
            rho)
        (twoBinderCompSub tau₂ sigma)
        (compFitsEqCons
          (compFitsEqCons
            (eqSubClosedCompFits
              {rho = tauTail₀}
              {eta = etaTail₀}
              cFits)
            (subst
              (λ T -> Computable (termEq [] t₀ u₀ T))
              (subTyComp tauTail₀ sigma A)
              (subst
                (λ J -> Computable J)
                (cong₃ (termEq [])
                  (subTmId t₀)
                  (subTmId u₀)
                  (subTyId (subTy tauTail₀ (subTy sigma A))))
                (substDerivTmEqComp
                  dtu₀
                  (fitsNil {gamma = []} {delta = []} {sigma = idSubst} wfNil)
                  compFitsNil))))
          (subst
            (λ T -> Computable (termEq [] t₁ u₁ T))
            (subTyComp tauTail₁ (liftSubst sigma) B
              ∙ cong (λ rho -> subTy rho B) (sym (oneBinderCompSub tauTail₁ sigma)))
            (subst
              (λ J -> Computable J)
              (cong₃ (termEq [])
                (subTmId t₁)
                (subTmId u₁)
                (subTyId (subTy tauTail₁ (subTy (liftSubst sigma) B))))
              (substDerivTmEqComp
                dtu₁
                (fitsNil {gamma = []} {delta = []} {sigma = idSubst} wfNil)
                compFitsNil)))))

  eqSubClosedCompFitsEq : {gamma : Ctx} {sigma tau rho eta : Subst}
    -> CompFitsEqSubst gamma sigma tau
    -> CompFitsEqSubst gamma (compSub rho sigma) (compSub eta tau)
  eqSubClosedCompFitsEq {rho = rho} {eta = eta} compFitsEqNil = compFitsEqNil
  eqSubClosedCompFitsEq {rho = rho} {eta = eta}
    (compFitsEqCons {gamma = gamma} {sigma = sigma} {tau = tau} {A = A} {t = t} {u = u} cFitsEq comptu) =
    subst
      (λ zeta -> CompFitsEqSubst (A ∷ gamma) zeta (compSub eta (consSubst u tau)))
      (sym (compSubCons rho t sigma))
      (subst
        (λ zeta ->
          CompFitsEqSubst (A ∷ gamma) (consSubst (subTm rho t) (compSub rho sigma)) zeta)
        (sym (compSubCons eta u tau))
        (compFitsEqCons
          (eqSubClosedCompFitsEq {sigma = sigma} {tau = tau} {rho = rho} {eta = eta} cFitsEq)
          (subst
            (λ T -> Computable (termEq [] (subTm rho t) (subTm eta u) T))
            (subTyComp rho sigma A)
            (eqSubDerivTmEqComp
              (compToDerivable comptu)
              (fitsEqNil {gamma = []} {delta = []} {sigma = rho} {tau = eta} wfNil)
              compFitsEqNil))))

  composeOneBinderEqComp : {gamma : Ctx} {A : RawType} {sigma tau rho : Subst}
    -> FitsSubst [] (subTy sigma A ∷ []) rho
    -> CompFitsEqSubst gamma sigma tau
    -> CompFitsEqSubst (A ∷ gamma)
         (compSub rho (liftSubst sigma))
         (compSub rho (liftSubst tau))
  composeOneBinderEqComp fits cFitsEq =
    composeOneBinderEqCompEq cFitsEq (reflFitsEq fits)

  composeOneBinderEqCompEq : {gamma : Ctx} {A : RawType} {sigma tau rho eta : Subst}
    -> CompFitsEqSubst gamma sigma tau
    -> FitsEqSubst [] (subTy sigma A ∷ []) rho eta
    -> CompFitsEqSubst (A ∷ gamma)
         (compSub rho (liftSubst sigma))
         (compSub eta (liftSubst tau))
  composeOneBinderEqCompEq {gamma = gamma} {A = A} {sigma = sigma} {tau = tau} {rho = rho} {eta = eta}
    cFitsEq
    (fitsEqCons {sigma = rhoTail} {tau = etaTail} {t = t} {u = u} (fitsEqNil wf) dtu) =
    subst
      (λ zeta -> CompFitsEqSubst (A ∷ gamma) zeta (compSub eta (liftSubst tau)))
      (oneBinderCompSub rho sigma)
      (subst
        (λ zeta ->
          CompFitsEqSubst (A ∷ gamma)
            (consSubst t (compSub rhoTail sigma))
            zeta)
        (oneBinderCompSub eta tau)
        (compFitsEqCons
          (eqSubClosedCompFitsEq
            {sigma = sigma}
            {tau = tau}
            {rho = rhoTail}
            {eta = etaTail}
            cFitsEq)
          (subst
            (λ T -> Computable (termEq [] t u T))
            (subTyComp rhoTail sigma A)
            (subst
              (λ J -> Computable J)
              (cong₃ (termEq [])
                (subTmId t)
                (subTmId u)
                (subTyId (subTy rhoTail (subTy sigma A))))
              (substDerivTmEqComp
                dtu
                (fitsNil {gamma = []} {delta = []} {sigma = idSubst} wfNil)
                compFitsNil)))))

  composeTwoBindersEqComp : {gamma : Ctx} {A B : RawType} {sigma tau rho : Subst}
    -> CompFitsEqSubst gamma sigma tau
    -> FitsSubst [] (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) rho
    -> CompFitsEqSubst (B ∷ A ∷ gamma)
         (compSub rho (liftSubst (liftSubst sigma)))
         (compSub rho (liftSubst (liftSubst tau)))
  composeTwoBindersEqComp cFitsEq fits =
    composeTwoBindersEqCompEq cFitsEq (reflFitsEq fits)

  composeTwoBindersEqCompEq : {gamma : Ctx} {A B : RawType} {sigma tau rho eta : Subst}
    -> CompFitsEqSubst gamma sigma tau
    -> FitsEqSubst [] (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) rho eta
    -> CompFitsEqSubst (B ∷ A ∷ gamma)
         (compSub rho (liftSubst (liftSubst sigma)))
         (compSub eta (liftSubst (liftSubst tau)))
  composeTwoBindersEqCompEq
    {gamma = gamma} {A = A} {B = B} {sigma = sigma} {tau = tau} {rho = rho} {eta = eta}
    cFitsEq
    (fitsEqCons {sigma = rhoTail₁} {tau = etaTail₁} {t = t₁} {u = u₁}
      (fitsEqCons {sigma = rhoTail₀} {tau = etaTail₀} {t = t₀} {u = u₀} (fitsEqNil wf) dtu₀)
      dtu₁) =
    subst
      (λ zeta ->
        CompFitsEqSubst (B ∷ A ∷ gamma) zeta (compSub eta (liftSubst (liftSubst tau))))
      (twoBinderCompSub rho sigma)
      (subst
        (λ zeta ->
          CompFitsEqSubst (B ∷ A ∷ gamma)
            (consSubst t₁ (consSubst t₀ (compSub rhoTail₀ sigma)))
            zeta)
        (twoBinderCompSub eta tau)
        (compFitsEqCons
          (compFitsEqCons
            (eqSubClosedCompFitsEq
              {sigma = sigma}
              {tau = tau}
              {rho = rhoTail₀}
              {eta = etaTail₀}
              cFitsEq)
            (subst
              (λ T -> Computable (termEq [] t₀ u₀ T))
              (subTyComp rhoTail₀ sigma A)
              (subst
                (λ J -> Computable J)
                (cong₃ (termEq [])
                  (subTmId t₀)
                  (subTmId u₀)
                  (subTyId (subTy rhoTail₀ (subTy sigma A))))
                (substDerivTmEqComp
                  dtu₀
                  (fitsNil {gamma = []} {delta = []} {sigma = idSubst} wfNil)
                  compFitsNil))))
          (subst
            (λ T -> Computable (termEq [] t₁ u₁ T))
            (subTyComp rhoTail₁ (liftSubst sigma) B
              ∙ cong (λ zeta -> subTy zeta B) (sym (oneBinderCompSub rhoTail₁ sigma)))
            (subst
              (λ J -> Computable J)
              (cong₃ (termEq [])
                (subTmId t₁)
                (subTmId u₁)
                (subTyId (subTy rhoTail₁ (subTy (liftSubst sigma) B))))
              (substDerivTmEqComp
                dtu₁
                (fitsNil {gamma = []} {delta = []} {sigma = idSubst} wfNil)
                compFitsNil)))))

  substOpenTy1 : {gamma : Ctx} {A B : RawType} {sigma : Subst}
    -> FitsSubst [] gamma sigma
    -> CompFitsSubst gamma sigma
    -> Derivable (isType [] (subTy sigma A))
    -> Computable (isType (A ∷ gamma) B)
    -> Computable (isType (subTy sigma A ∷ []) (subTy (liftSubst sigma) B))
  substOpenTy1 {A = A} {B = B} {sigma = sigma} fits cFits dAσ (compTyOpen neqBody dBody sub subEq) =
    subst
      (λ T -> Computable (isType (subTy sigma A ∷ []) T))
      (cong (λ rho -> subTy rho B) (liftSubstCompKeep sigma))
      (compTyOpen
        nonemptyNeNil
        (substTyRule dBody (liftFitsOne fits dAσ))
        (λ tau fits2 ->
          let
            composedFits = composeOneBinder fits dAσ fits2
            closed =
              sub
                (compSub tau (liftSubst sigma))
                composedFits
          in
          packClosedSubst fits2
            (subst
              (λ T -> Computable (isType [] T))
              (sym
                (cong (λ rho -> subTy tau (subTy rho B)) (liftSubstCompKeep sigma)
                  ∙ subTyComp tau (liftSubst sigma) B))
              (ClosedSubstComp.closedComp closed)))
        (λ tau₁ tau₂ fitsEq2 ->
          let
            composedFitsEq = composeOneBinderEq fits dAσ fitsEq2
            closedEq =
              subEq
                (compSub tau₁ (liftSubst sigma))
                (compSub tau₂ (liftSubst sigma))
                composedFitsEq
          in
          packClosedEqSubst fitsEq2
            (subst
              (λ J -> Computable J)
              (sym
                (cong₂ (typeEq [])
                  (cong (λ rho -> subTy tau₁ (subTy rho B)) (liftSubstCompKeep sigma)
                    ∙ subTyComp tau₁ (liftSubst sigma) B)
                  (cong (λ rho -> subTy tau₂ (subTy rho B)) (liftSubstCompKeep sigma)
                    ∙ subTyComp tau₂ (liftSubst sigma) B)))
              (ClosedEqSubstComp.closedEqComp closedEq))))

  substOpenTyEq1 : {gamma : Ctx} {A B C : RawType} {sigma : Subst}
    -> FitsSubst [] gamma sigma
    -> CompFitsSubst gamma sigma
    -> Derivable (isType [] (subTy sigma A))
    -> Computable (typeEq (A ∷ gamma) B C)
    -> Computable (typeEq (subTy sigma A ∷ []) (subTy (liftSubst sigma) B) (subTy (liftSubst sigma) C))
  substOpenTyEq1 {A = A} {B = B} {C = C} {sigma = sigma} fits cFits dAσ (compTyEqOpen neqBody dBody compLeft sub subEq) =
    subst
      (λ J -> Computable J)
      (cong₂ (typeEq (subTy sigma A ∷ []))
        (cong (λ rho -> subTy rho B) (liftSubstCompKeep sigma))
        (cong (λ rho -> subTy rho C) (liftSubstCompKeep sigma)))
      (compTyEqOpen
        nonemptyNeNil
        (substTyEqRule dBody (liftFitsOne fits dAσ))
        (subst
          (λ T -> Computable (isType (subTy sigma A ∷ []) T))
          (sym (cong (λ rho -> subTy rho B) (liftSubstCompKeep sigma)))
          (substOpenTy1 fits cFits dAσ compLeft))
        (λ tau fits2 ->
          let
            composedFits = composeOneBinder fits dAσ fits2
            closed =
              sub
                (compSub tau (liftSubst sigma))
                composedFits
          in
          packClosedSubst fits2
            (subst
              (λ J -> Computable J)
              (sym
                (cong₂ (typeEq [])
                  (cong (λ rho -> subTy tau (subTy rho B)) (liftSubstCompKeep sigma)
                    ∙ subTyComp tau (liftSubst sigma) B)
                  (cong (λ rho -> subTy tau (subTy rho C)) (liftSubstCompKeep sigma)
                    ∙ subTyComp tau (liftSubst sigma) C)))
              (ClosedSubstComp.closedComp closed)))
        (λ tau₁ tau₂ fitsEq2 ->
          let
            composedFitsEq = composeOneBinderEq fits dAσ fitsEq2
            closedEq =
              subEq
                (compSub tau₁ (liftSubst sigma))
                (compSub tau₂ (liftSubst sigma))
                composedFitsEq
          in
          packClosedEqSubst fitsEq2
            (subst
              (λ J -> Computable J)
              (sym
                (cong₂ (typeEq [])
                  (cong (λ rho -> subTy tau₁ (subTy rho B)) (liftSubstCompKeep sigma)
                    ∙ subTyComp tau₁ (liftSubst sigma) B)
                  (cong (λ rho -> subTy tau₂ (subTy rho C)) (liftSubstCompKeep sigma)
                    ∙ subTyComp tau₂ (liftSubst sigma) C)))
              (ClosedEqSubstComp.closedEqComp closedEq))))

  substOpenTm1 : {gamma : Ctx} {A T : RawType} {t : RawTerm} {sigma : Subst}
    -> FitsSubst [] gamma sigma
    -> CompFitsSubst gamma sigma
    -> Derivable (isType [] (subTy sigma A))
    -> Computable (hasTy (A ∷ gamma) t T)
    -> Computable
         (hasTy (subTy sigma A ∷ [])
           (subTm (liftSubst sigma) t)
           (subTy (liftSubst sigma) T))
  substOpenTm1 {A = A} {T = T} {t = t} {sigma = sigma} fits cFits dAσ (compTmOpen neqBody dBody compTy sub subEq) =
    subst
      (λ J -> Computable J)
      (cong₂
        (hasTy (subTy sigma A ∷ []))
        (cong (λ rho -> subTm rho t) (liftSubstCompKeep sigma))
        (cong (λ rho -> subTy rho T) (liftSubstCompKeep sigma)))
      (compTmOpen
        nonemptyNeNil
        (substTmRule dBody (liftFitsOne fits dAσ))
        (subst
          (λ T' -> Computable (isType (subTy sigma A ∷ []) T'))
          (sym (cong (λ rho -> subTy rho T) (liftSubstCompKeep sigma)))
          (substOpenTy1 fits cFits dAσ compTy))
        (λ tau fits2 ->
          let
            composedFits = composeOneBinder fits dAσ fits2
            closed =
              sub
                (compSub tau (liftSubst sigma))
                composedFits
          in
          packClosedSubst fits2
            (subst
              (λ J -> Computable J)
              (sym
                (cong₂ (hasTy [])
                  (cong (λ rho -> subTm tau (subTm rho t)) (liftSubstCompKeep sigma)
                    ∙ subTmComp tau (liftSubst sigma) t)
                  (cong (λ rho -> subTy tau (subTy rho T)) (liftSubstCompKeep sigma)
                    ∙ subTyComp tau (liftSubst sigma) T)))
              (ClosedSubstComp.closedComp closed)))
        (λ tau₁ tau₂ fitsEq2 ->
          let
            composedFitsEq = composeOneBinderEq fits dAσ fitsEq2
            closedEq =
              subEq
                (compSub tau₁ (liftSubst sigma))
                (compSub tau₂ (liftSubst sigma))
                composedFitsEq
          in
          packClosedEqSubst fitsEq2
            (subst
              (λ J -> Computable J)
              (sym
                (cong₃ (termEq [])
                  (cong (λ rho -> subTm tau₁ (subTm rho t)) (liftSubstCompKeep sigma)
                    ∙ subTmComp tau₁ (liftSubst sigma) t)
                  (cong (λ rho -> subTm tau₂ (subTm rho t)) (liftSubstCompKeep sigma)
                    ∙ subTmComp tau₂ (liftSubst sigma) t)
                  (cong (λ rho -> subTy tau₁ (subTy rho T)) (liftSubstCompKeep sigma)
                    ∙ subTyComp tau₁ (liftSubst sigma) T)))
              (ClosedEqSubstComp.closedEqComp closedEq))))

  substOpenTmEq1 : {gamma : Ctx} {A T : RawType} {t u : RawTerm} {sigma : Subst}
    -> FitsSubst [] gamma sigma
    -> CompFitsSubst gamma sigma
    -> Derivable (isType [] (subTy sigma A))
    -> Computable (termEq (A ∷ gamma) t u T)
    -> Computable
         (termEq (subTy sigma A ∷ [])
           (subTm (liftSubst sigma) t)
           (subTm (liftSubst sigma) u)
           (subTy (liftSubst sigma) T))
  substOpenTmEq1 {A = A} {T = T} {t = t} {u = u} {sigma = sigma} fits cFits dAσ (compTmEqOpen neqBody dBody compTm sub subEq) =
    subst
      (λ J -> Computable J)
      (cong₃
        (termEq (subTy sigma A ∷ []))
        (cong (λ rho -> subTm rho t) (liftSubstCompKeep sigma))
        (cong (λ rho -> subTm rho u) (liftSubstCompKeep sigma))
        (cong (λ rho -> subTy rho T) (liftSubstCompKeep sigma)))
      (compTmEqOpen
        nonemptyNeNil
        (substTmEqRule dBody (liftFitsOne fits dAσ))
        (subst
          (λ J -> Computable J)
          (sym
            (cong₂
              (hasTy (subTy sigma A ∷ []))
              (cong (λ rho -> subTm rho t) (liftSubstCompKeep sigma))
              (cong (λ rho -> subTy rho T) (liftSubstCompKeep sigma))))
          (substOpenTm1 fits cFits dAσ compTm))
        (λ tau fits2 ->
          let
            composedFits = composeOneBinder fits dAσ fits2
            closed =
              sub
                (compSub tau (liftSubst sigma))
                composedFits
          in
          packClosedSubst fits2
            (subst
              (λ J -> Computable J)
              (sym
                (cong₃ (termEq [])
                  (cong (λ rho -> subTm tau (subTm rho t)) (liftSubstCompKeep sigma)
                    ∙ subTmComp tau (liftSubst sigma) t)
                  (cong (λ rho -> subTm tau (subTm rho u)) (liftSubstCompKeep sigma)
                    ∙ subTmComp tau (liftSubst sigma) u)
                  (cong (λ rho -> subTy tau (subTy rho T)) (liftSubstCompKeep sigma)
                    ∙ subTyComp tau (liftSubst sigma) T)))
              (ClosedSubstComp.closedComp closed)))
        (λ tau₁ tau₂ fitsEq2 ->
          let
            composedFitsEq = composeOneBinderEq fits dAσ fitsEq2
            closedEq =
              subEq
                (compSub tau₁ (liftSubst sigma))
                (compSub tau₂ (liftSubst sigma))
                composedFitsEq
          in
          packClosedEqSubst fitsEq2
            (subst
              (λ J -> Computable J)
              (sym
                (cong₃ (termEq [])
                  (cong (λ rho -> subTm tau₁ (subTm rho t)) (liftSubstCompKeep sigma)
                    ∙ subTmComp tau₁ (liftSubst sigma) t)
                  (cong (λ rho -> subTm tau₂ (subTm rho u)) (liftSubstCompKeep sigma)
                    ∙ subTmComp tau₂ (liftSubst sigma) u)
                  (cong (λ rho -> subTy tau₁ (subTy rho T)) (liftSubstCompKeep sigma)
                    ∙ subTyComp tau₁ (liftSubst sigma) T)))
              (ClosedEqSubstComp.closedEqComp closedEq))))

  substOpenTy2 : {gamma : Ctx} {A B T : RawType} {sigma : Subst}
    -> FitsSubst [] gamma sigma
    -> CompFitsSubst gamma sigma
    -> Derivable (isType [] (subTy sigma A))
    -> Derivable (isType (subTy sigma A ∷ []) (subTy (liftSubst sigma) B))
    -> Computable (isType (B ∷ A ∷ gamma) T)
    -> Computable
         (isType (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ [])
           (subTy (liftSubst (liftSubst sigma)) T))
  substOpenTy2 {gamma = gamma} {A = A} {B = B} {T = T} {sigma = sigma} fits cFits dAσ dBσ dT =
    let
      lifted1 : FitsSubst (subTy sigma A ∷ []) (A ∷ gamma) (liftSubst sigma)
      lifted1 =
        subst
          (λ rho -> FitsSubst (subTy sigma A ∷ []) (A ∷ gamma) rho)
          (liftSubstCompKeep sigma)
          (liftFitsOne fits dAσ)
    in
    case dT of λ where
      (compTyOpen neqBody dBody sub subEq) ->
        subst
          (λ T' -> Computable (isType (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) T'))
          (cong (λ rho -> subTy rho T) (liftSubstCompKeep (liftSubst sigma)))
          (compTyOpen
            nonemptyNeNil
            (substTyRule dBody (liftFits lifted1 dBσ))
            (λ tau fits2 ->
              let
                composedFits = composeTwoBinders fits dAσ dBσ fits2
                closed =
                  sub
                    (compSub tau (liftSubst (liftSubst sigma)))
                    composedFits
              in
              packClosedSubst fits2
                (subst
                  (λ T' -> Computable (isType [] T'))
                  (sym
                    (cong (λ rho -> subTy tau (subTy rho T)) (liftSubstCompKeep (liftSubst sigma))
                      ∙ subTyComp tau (liftSubst (liftSubst sigma)) T))
                  (ClosedSubstComp.closedComp closed)))
            (λ tau₁ tau₂ fitsEq2 ->
              let
                composedFitsEq = composeTwoBindersEq fits dAσ dBσ fitsEq2
                closedEq =
                  subEq
                    (compSub tau₁ (liftSubst (liftSubst sigma)))
                    (compSub tau₂ (liftSubst (liftSubst sigma)))
                    composedFitsEq
              in
              packClosedEqSubst fitsEq2
                (subst
                  (λ J -> Computable J)
                  (sym
                    (cong₂ (typeEq [])
                      (cong (λ rho -> subTy tau₁ (subTy rho T)) (liftSubstCompKeep (liftSubst sigma))
                        ∙ subTyComp tau₁ (liftSubst (liftSubst sigma)) T)
                      (cong (λ rho -> subTy tau₂ (subTy rho T)) (liftSubstCompKeep (liftSubst sigma))
                        ∙ subTyComp tau₂ (liftSubst (liftSubst sigma)) T)))
                  (ClosedEqSubstComp.closedEqComp closedEq))))

  substOpenTm2 : {gamma : Ctx} {A B T : RawType} {t : RawTerm} {sigma : Subst}
    -> FitsSubst [] gamma sigma
    -> CompFitsSubst gamma sigma
    -> Derivable (isType [] (subTy sigma A))
    -> Derivable (isType (subTy sigma A ∷ []) (subTy (liftSubst sigma) B))
    -> Computable (hasTy (B ∷ A ∷ gamma) t T)
    -> Computable
         (hasTy (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ [])
           (subTm (liftSubst (liftSubst sigma)) t)
           (subTy (liftSubst (liftSubst sigma)) T))
  substOpenTm2 {gamma = gamma} {A = A} {B = B} {T = T} {t = t} {sigma = sigma} fits cFits dAσ dBσ dt =
    let
      lifted1 : FitsSubst (subTy sigma A ∷ []) (A ∷ gamma) (liftSubst sigma)
      lifted1 =
        subst
          (λ rho -> FitsSubst (subTy sigma A ∷ []) (A ∷ gamma) rho)
          (liftSubstCompKeep sigma)
          (liftFitsOne fits dAσ)
    in
    case dt of λ where
      (compTmOpen neqBody dBody compTy sub subEq) ->
        subst
          (λ J -> Computable J)
          (cong₂
            (hasTy (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []))
            (cong (λ rho -> subTm rho t) (liftSubstCompKeep (liftSubst sigma)))
            (cong (λ rho -> subTy rho T) (liftSubstCompKeep (liftSubst sigma))))
          (compTmOpen
            nonemptyNeNil
            (substTmRule dBody (liftFits lifted1 dBσ))
            (subst
              (λ T' ->
                Computable (isType (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) T'))
              (sym (cong (λ rho -> subTy rho T) (liftSubstCompKeep (liftSubst sigma))))
              (substOpenTy2 fits cFits dAσ dBσ compTy))
            (λ tau fits2 ->
              let
                composedFits = composeTwoBinders fits dAσ dBσ fits2
                closed =
                  sub
                    (compSub tau (liftSubst (liftSubst sigma)))
                    composedFits
              in
              packClosedSubst fits2
                (subst
                  (λ J -> Computable J)
                  (sym
                    (cong₂ (hasTy [])
                      (cong (λ rho -> subTm tau (subTm rho t)) (liftSubstCompKeep (liftSubst sigma))
                        ∙ subTmComp tau (liftSubst (liftSubst sigma)) t)
                      (cong (λ rho -> subTy tau (subTy rho T)) (liftSubstCompKeep (liftSubst sigma))
                        ∙ subTyComp tau (liftSubst (liftSubst sigma)) T)))
                  (ClosedSubstComp.closedComp closed)))
            (λ tau₁ tau₂ fitsEq2 ->
              let
                composedFitsEq = composeTwoBindersEq fits dAσ dBσ fitsEq2
                closedEq =
                  subEq
                    (compSub tau₁ (liftSubst (liftSubst sigma)))
                    (compSub tau₂ (liftSubst (liftSubst sigma)))
                    composedFitsEq
              in
              packClosedEqSubst fitsEq2
                (subst
                  (λ J -> Computable J)
                  (sym
                    (cong₃ (termEq [])
                      (cong (λ rho -> subTm tau₁ (subTm rho t)) (liftSubstCompKeep (liftSubst sigma))
                        ∙ subTmComp tau₁ (liftSubst (liftSubst sigma)) t)
                      (cong (λ rho -> subTm tau₂ (subTm rho t)) (liftSubstCompKeep (liftSubst sigma))
                        ∙ subTmComp tau₂ (liftSubst (liftSubst sigma)) t)
                      (cong (λ rho -> subTy tau₁ (subTy rho T)) (liftSubstCompKeep (liftSubst sigma))
                        ∙ subTyComp tau₁ (liftSubst (liftSubst sigma)) T)))
                  (ClosedEqSubstComp.closedEqComp closedEq))))

  substOpenTmEq2 : {gamma : Ctx} {A B T : RawType} {t u : RawTerm} {sigma : Subst}
    -> FitsSubst [] gamma sigma
    -> CompFitsSubst gamma sigma
    -> Derivable (isType [] (subTy sigma A))
    -> Derivable (isType (subTy sigma A ∷ []) (subTy (liftSubst sigma) B))
    -> Computable (termEq (B ∷ A ∷ gamma) t u T)
    -> Computable
         (termEq (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ [])
           (subTm (liftSubst (liftSubst sigma)) t)
           (subTm (liftSubst (liftSubst sigma)) u)
           (subTy (liftSubst (liftSubst sigma)) T))
  substOpenTmEq2 {gamma = gamma} {A = A} {B = B} {T = T} {t = t} {u = u} {sigma = sigma} fits cFits dAσ dBσ dtu =
    let
      lifted1 : FitsSubst (subTy sigma A ∷ []) (A ∷ gamma) (liftSubst sigma)
      lifted1 =
        subst
          (λ rho -> FitsSubst (subTy sigma A ∷ []) (A ∷ gamma) rho)
          (liftSubstCompKeep sigma)
          (liftFitsOne fits dAσ)
    in
    case dtu of λ where
      (compTmEqOpen neqBody dBody compTm sub subEq) ->
        subst
          (λ J -> Computable J)
          (cong₃
            (termEq (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []))
            (cong (λ rho -> subTm rho t) (liftSubstCompKeep (liftSubst sigma)))
            (cong (λ rho -> subTm rho u) (liftSubstCompKeep (liftSubst sigma)))
            (cong (λ rho -> subTy rho T) (liftSubstCompKeep (liftSubst sigma))))
          (compTmEqOpen
            nonemptyNeNil
            (substTmEqRule dBody (liftFits lifted1 dBσ))
            (subst
              (λ J -> Computable J)
              (sym
                (cong₂
                  (hasTy (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []))
                  (cong (λ rho -> subTm rho t) (liftSubstCompKeep (liftSubst sigma)))
                  (cong (λ rho -> subTy rho T) (liftSubstCompKeep (liftSubst sigma)))))
              (substOpenTm2 fits cFits dAσ dBσ compTm))
            (λ tau fits2 ->
              let
                composedFits = composeTwoBinders fits dAσ dBσ fits2
                closed =
                  sub
                    (compSub tau (liftSubst (liftSubst sigma)))
                    composedFits
              in
              packClosedSubst fits2
                (subst
                  (λ J -> Computable J)
                  (sym
                    (cong₃ (termEq [])
                      (cong (λ rho -> subTm tau (subTm rho t)) (liftSubstCompKeep (liftSubst sigma))
                        ∙ subTmComp tau (liftSubst (liftSubst sigma)) t)
                      (cong (λ rho -> subTm tau (subTm rho u)) (liftSubstCompKeep (liftSubst sigma))
                        ∙ subTmComp tau (liftSubst (liftSubst sigma)) u)
                      (cong (λ rho -> subTy tau (subTy rho T)) (liftSubstCompKeep (liftSubst sigma))
                        ∙ subTyComp tau (liftSubst (liftSubst sigma)) T)))
                  (ClosedSubstComp.closedComp closed)))
            (λ tau₁ tau₂ fitsEq2 ->
              let
                composedFitsEq = composeTwoBindersEq fits dAσ dBσ fitsEq2
                closedEq =
                  subEq
                    (compSub tau₁ (liftSubst (liftSubst sigma)))
                    (compSub tau₂ (liftSubst (liftSubst sigma)))
                    composedFitsEq
              in
              packClosedEqSubst fitsEq2
                (subst
                  (λ J -> Computable J)
                  (sym
                    (cong₃ (termEq [])
                      (cong (λ rho -> subTm tau₁ (subTm rho t)) (liftSubstCompKeep (liftSubst sigma))
                        ∙ subTmComp tau₁ (liftSubst (liftSubst sigma)) t)
                      (cong (λ rho -> subTm tau₂ (subTm rho u)) (liftSubstCompKeep (liftSubst sigma))
                        ∙ subTmComp tau₂ (liftSubst (liftSubst sigma)) u)
                    (cong (λ rho -> subTy tau₁ (subTy rho T)) (liftSubstCompKeep (liftSubst sigma))
                        ∙ subTyComp tau₁ (liftSubst (liftSubst sigma)) T)))
                  (ClosedEqSubstComp.closedEqComp closedEq))))

  substSccTy1 : {gamma : Ctx} {A B : RawType} {sigma : Subst}
    -> FitsSubst [] gamma sigma
    -> CompFitsSubst gamma sigma
    -> Derivable (isType [] (subTy sigma A))
    -> Derivable (isType (A ∷ gamma) B)
    -> Computable (isType (subTy sigma A ∷ []) (subTy (liftSubst sigma) B))
  substSccTy1 {A = A} {B = B} {sigma = sigma} fits cFits dAσ dB =
    subst
      (λ T -> Computable (isType (subTy sigma A ∷ []) T))
      (cong (λ rho -> subTy rho B) (liftSubstCompKeep sigma))
      (compTyOpen
        nonemptyNeNil
        (substTyRule dB (liftFitsOne fits dAσ))
        (λ tau fits2 ->
          packClosedSubst fits2
            (subst
              (λ T -> Computable (isType [] T))
              (sym
                (cong (λ rho -> subTy tau (subTy rho B)) (liftSubstCompKeep sigma)
                  ∙ subTyComp tau (liftSubst sigma) B))
              (substDerivTyComp
                dB
                (composeOneBinder fits dAσ fits2)
                (composeOneBinderComp fits2 cFits))))
        (λ tau₁ tau₂ fitsEq2 ->
          packClosedEqSubst fitsEq2
            (subst
              (λ J -> Computable J)
              (sym
                (cong₂ (typeEq [])
                  (cong (λ rho -> subTy tau₁ (subTy rho B)) (liftSubstCompKeep sigma)
                    ∙ subTyComp tau₁ (liftSubst sigma) B)
                  (cong (λ rho -> subTy tau₂ (subTy rho B)) (liftSubstCompKeep sigma)
                    ∙ subTyComp tau₂ (liftSubst sigma) B)))
              (eqSubDerivTyComp
                dB
                (composeOneBinderEq fits dAσ fitsEq2)
                (composeOneBinderCompEq cFits fitsEq2)))))

  substSccTy2 : {gamma : Ctx} {A B T : RawType} {sigma : Subst}
    -> FitsSubst [] gamma sigma
    -> CompFitsSubst gamma sigma
    -> Derivable (isType [] (subTy sigma A))
    -> Derivable (isType (subTy sigma A ∷ []) (subTy (liftSubst sigma) B))
    -> Derivable (isType (B ∷ A ∷ gamma) T)
    -> Computable
         (isType (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ [])
           (subTy (liftSubst (liftSubst sigma)) T))
  substSccTy2 {gamma = gamma} {A = A} {B = B} {T = T} {sigma = sigma} fits cFits dAσ dBσ dT =
    let
      lifted1 : FitsSubst (subTy sigma A ∷ []) (A ∷ gamma) (liftSubst sigma)
      lifted1 =
        subst
          (λ rho -> FitsSubst (subTy sigma A ∷ []) (A ∷ gamma) rho)
          (liftSubstCompKeep sigma)
          (liftFitsOne fits dAσ)
    in
    subst
      (λ T' -> Computable (isType (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) T'))
      (cong (λ rho -> subTy rho T) (liftSubstCompKeep (liftSubst sigma)))
      (compTyOpen
        nonemptyNeNil
        (substTyRule dT (liftFits lifted1 dBσ))
        (λ tau fits2 ->
          packClosedSubst fits2
            (subst
              (λ T' -> Computable (isType [] T'))
              (sym
                (cong (λ rho -> subTy tau (subTy rho T)) (liftSubstCompKeep (liftSubst sigma))
                  ∙ subTyComp tau (liftSubst (liftSubst sigma)) T))
              (substDerivTyComp
                dT
                (composeTwoBinders fits dAσ dBσ fits2)
                (composeTwoBindersComp cFits fits2))))
        (λ tau₁ tau₂ fitsEq2 ->
          packClosedEqSubst fitsEq2
            (subst
              (λ J -> Computable J)
              (sym
                (cong₂ (typeEq [])
                  (cong (λ rho -> subTy tau₁ (subTy rho T)) (liftSubstCompKeep (liftSubst sigma))
                    ∙ subTyComp tau₁ (liftSubst (liftSubst sigma)) T)
                  (cong (λ rho -> subTy tau₂ (subTy rho T)) (liftSubstCompKeep (liftSubst sigma))
                    ∙ subTyComp tau₂ (liftSubst (liftSubst sigma)) T)))
              (eqSubDerivTyComp
                dT
                (composeTwoBindersEq fits dAσ dBσ fitsEq2)
                (composeTwoBindersCompEq cFits fitsEq2)))))

  substSccTm1 : {gamma : Ctx} {A T : RawType} {t : RawTerm} {sigma : Subst}
    -> FitsSubst [] gamma sigma
    -> CompFitsSubst gamma sigma
    -> Derivable (isType [] (subTy sigma A))
    -> Derivable (hasTy (A ∷ gamma) t T)
    -> Computable
         (hasTy (subTy sigma A ∷ [])
           (subTm (liftSubst sigma) t)
           (subTy (liftSubst sigma) T))
  substSccTm1 {A = A} {T = T} {t = t} {sigma = sigma} fits cFits dAσ dt =
    subst
      (λ J -> Computable J)
      (cong₂
        (hasTy (subTy sigma A ∷ []))
        (cong (λ rho -> subTm rho t) (liftSubstCompKeep sigma))
        (cong (λ rho -> subTy rho T) (liftSubstCompKeep sigma)))
      (compTmOpen
        nonemptyNeNil
        (substTmRule dt (liftFitsOne fits dAσ))
        (subst
          (λ T' -> Computable (isType (subTy sigma A ∷ []) T'))
          (sym (cong (λ rho -> subTy rho T) (liftSubstCompKeep sigma)))
          (substSccTy1 fits cFits dAσ (assocTy dt)))
        (λ tau fits2 ->
          packClosedSubst fits2
            (subst
              (λ J -> Computable J)
              (sym
                (cong₂ (hasTy [])
                  (cong (λ rho -> subTm tau (subTm rho t)) (liftSubstCompKeep sigma)
                    ∙ subTmComp tau (liftSubst sigma) t)
                  (cong (λ rho -> subTy tau (subTy rho T)) (liftSubstCompKeep sigma)
                    ∙ subTyComp tau (liftSubst sigma) T)))
              (substDerivTmComp
                dt
                (composeOneBinder fits dAσ fits2)
                (composeOneBinderComp fits2 cFits))))
        (λ tau₁ tau₂ fitsEq2 ->
          packClosedEqSubst fitsEq2
            (subst
              (λ J -> Computable J)
              (sym
                (cong₃ (termEq [])
                  (cong (λ rho -> subTm tau₁ (subTm rho t)) (liftSubstCompKeep sigma)
                    ∙ subTmComp tau₁ (liftSubst sigma) t)
                  (cong (λ rho -> subTm tau₂ (subTm rho t)) (liftSubstCompKeep sigma)
                    ∙ subTmComp tau₂ (liftSubst sigma) t)
                  (cong (λ rho -> subTy tau₁ (subTy rho T)) (liftSubstCompKeep sigma)
                    ∙ subTyComp tau₁ (liftSubst sigma) T)))
              (eqSubDerivTmComp
                dt
                (composeOneBinderEq fits dAσ fitsEq2)
                (composeOneBinderCompEq cFits fitsEq2)))))

  substSccTmEq1 : {gamma : Ctx} {A T : RawType} {t u : RawTerm} {sigma : Subst}
    -> FitsSubst [] gamma sigma
    -> CompFitsSubst gamma sigma
    -> Derivable (isType [] (subTy sigma A))
    -> Derivable (termEq (A ∷ gamma) t u T)
    -> Computable
         (termEq (subTy sigma A ∷ [])
           (subTm (liftSubst sigma) t)
           (subTm (liftSubst sigma) u)
           (subTy (liftSubst sigma) T))
  substSccTmEq1 {A = A} {T = T} {t = t} {u = u} {sigma = sigma} fits cFits dAσ dtu =
    subst
      (λ J -> Computable J)
      (cong₃
        (termEq (subTy sigma A ∷ []))
        (cong (λ rho -> subTm rho t) (liftSubstCompKeep sigma))
        (cong (λ rho -> subTm rho u) (liftSubstCompKeep sigma))
        (cong (λ rho -> subTy rho T) (liftSubstCompKeep sigma)))
      (compTmEqOpen
        nonemptyNeNil
        (substTmEqRule dtu (liftFitsOne fits dAσ))
        (subst
          (λ J -> Computable J)
          (sym
            (cong₂
              (hasTy (subTy sigma A ∷ []))
              (cong (λ rho -> subTm rho t) (liftSubstCompKeep sigma))
              (cong (λ rho -> subTy rho T) (liftSubstCompKeep sigma))))
          (substSccTm1 fits cFits dAσ (assocTmLeft dtu)))
        (λ tau fits2 ->
          packClosedSubst fits2
            (subst
              (λ J -> Computable J)
              (sym
                (cong₃ (termEq [])
                  (cong (λ rho -> subTm tau (subTm rho t)) (liftSubstCompKeep sigma)
                    ∙ subTmComp tau (liftSubst sigma) t)
                  (cong (λ rho -> subTm tau (subTm rho u)) (liftSubstCompKeep sigma)
                    ∙ subTmComp tau (liftSubst sigma) u)
                  (cong (λ rho -> subTy tau (subTy rho T)) (liftSubstCompKeep sigma)
                    ∙ subTyComp tau (liftSubst sigma) T)))
              (substDerivTmEqComp
                dtu
                (composeOneBinder fits dAσ fits2)
                (composeOneBinderComp fits2 cFits))))
        (λ tau₁ tau₂ fitsEq2 ->
          packClosedEqSubst fitsEq2
            (subst
              (λ J -> Computable J)
              (sym
                (cong₃ (termEq [])
                  (cong (λ rho -> subTm tau₁ (subTm rho t)) (liftSubstCompKeep sigma)
                    ∙ subTmComp tau₁ (liftSubst sigma) t)
                  (cong (λ rho -> subTm tau₂ (subTm rho u)) (liftSubstCompKeep sigma)
                    ∙ subTmComp tau₂ (liftSubst sigma) u)
                  (cong (λ rho -> subTy tau₁ (subTy rho T)) (liftSubstCompKeep sigma)
                    ∙ subTyComp tau₁ (liftSubst sigma) T)))
              (eqSubDerivTmEqComp
                dtu
                (composeOneBinderEq fits dAσ fitsEq2)
                (composeOneBinderCompEq cFits fitsEq2)))))

  substSccTm2 : {gamma : Ctx} {A B T : RawType} {t : RawTerm} {sigma : Subst}
    -> FitsSubst [] gamma sigma
    -> CompFitsSubst gamma sigma
    -> Derivable (isType [] (subTy sigma A))
    -> Derivable (isType (subTy sigma A ∷ []) (subTy (liftSubst sigma) B))
    -> Derivable (hasTy (B ∷ A ∷ gamma) t T)
    -> Computable
         (hasTy (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ [])
           (subTm (liftSubst (liftSubst sigma)) t)
           (subTy (liftSubst (liftSubst sigma)) T))
  substSccTm2 {gamma = gamma} {A = A} {B = B} {T = T} {t = t} {sigma = sigma} fits cFits dAσ dBσ dt =
    let
      lifted1 : FitsSubst (subTy sigma A ∷ []) (A ∷ gamma) (liftSubst sigma)
      lifted1 =
        subst
          (λ rho -> FitsSubst (subTy sigma A ∷ []) (A ∷ gamma) rho)
          (liftSubstCompKeep sigma)
          (liftFitsOne fits dAσ)
    in
    subst
      (λ J -> Computable J)
      (cong₂
        (hasTy (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []))
        (cong (λ rho -> subTm rho t) (liftSubstCompKeep (liftSubst sigma)))
        (cong (λ rho -> subTy rho T) (liftSubstCompKeep (liftSubst sigma))))
      (compTmOpen
        nonemptyNeNil
        (substTmRule dt (liftFits lifted1 dBσ))
        (subst
          (λ T' ->
            Computable (isType (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) T'))
          (sym (cong (λ rho -> subTy rho T) (liftSubstCompKeep (liftSubst sigma))))
          (substSccTy2 fits cFits dAσ dBσ (assocTy dt)))
        (λ tau fits2 ->
          packClosedSubst fits2
            (subst
              (λ J -> Computable J)
              (sym
                (cong₂ (hasTy [])
                  (cong (λ rho -> subTm tau (subTm rho t)) (liftSubstCompKeep (liftSubst sigma))
                    ∙ subTmComp tau (liftSubst (liftSubst sigma)) t)
                  (cong (λ rho -> subTy tau (subTy rho T)) (liftSubstCompKeep (liftSubst sigma))
                    ∙ subTyComp tau (liftSubst (liftSubst sigma)) T)))
              (substDerivTmComp
                dt
                (composeTwoBinders fits dAσ dBσ fits2)
                (composeTwoBindersComp cFits fits2))))
        (λ tau₁ tau₂ fitsEq2 ->
          packClosedEqSubst fitsEq2
            (subst
              (λ J -> Computable J)
              (sym
                (cong₃ (termEq [])
                  (cong (λ rho -> subTm tau₁ (subTm rho t)) (liftSubstCompKeep (liftSubst sigma))
                    ∙ subTmComp tau₁ (liftSubst (liftSubst sigma)) t)
                  (cong (λ rho -> subTm tau₂ (subTm rho t)) (liftSubstCompKeep (liftSubst sigma))
                    ∙ subTmComp tau₂ (liftSubst (liftSubst sigma)) t)
                  (cong (λ rho -> subTy tau₁ (subTy rho T)) (liftSubstCompKeep (liftSubst sigma))
                    ∙ subTyComp tau₁ (liftSubst (liftSubst sigma)) T)))
              (eqSubDerivTmComp
                dt
                (composeTwoBindersEq fits dAσ dBσ fitsEq2)
                (composeTwoBindersCompEq cFits fitsEq2)))))

  substSccTmEq2 : {gamma : Ctx} {A B T : RawType} {t u : RawTerm} {sigma : Subst}
    -> FitsSubst [] gamma sigma
    -> CompFitsSubst gamma sigma
    -> Derivable (isType [] (subTy sigma A))
    -> Derivable (isType (subTy sigma A ∷ []) (subTy (liftSubst sigma) B))
    -> Derivable (termEq (B ∷ A ∷ gamma) t u T)
    -> Computable
         (termEq (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ [])
           (subTm (liftSubst (liftSubst sigma)) t)
           (subTm (liftSubst (liftSubst sigma)) u)
           (subTy (liftSubst (liftSubst sigma)) T))
  substSccTmEq2 {gamma = gamma} {A = A} {B = B} {T = T} {t = t} {u = u} {sigma = sigma}
    fits cFits dAσ dBσ dtu =
    let
      lifted1 : FitsSubst (subTy sigma A ∷ []) (A ∷ gamma) (liftSubst sigma)
      lifted1 =
        subst
          (λ rho -> FitsSubst (subTy sigma A ∷ []) (A ∷ gamma) rho)
          (liftSubstCompKeep sigma)
          (liftFitsOne fits dAσ)
    in
    subst
      (λ J -> Computable J)
      (cong₃
        (termEq (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []))
        (cong (λ rho -> subTm rho t) (liftSubstCompKeep (liftSubst sigma)))
        (cong (λ rho -> subTm rho u) (liftSubstCompKeep (liftSubst sigma)))
        (cong (λ rho -> subTy rho T) (liftSubstCompKeep (liftSubst sigma))))
      (compTmEqOpen
        nonemptyNeNil
        (substTmEqRule dtu (liftFits lifted1 dBσ))
        (subst
          (λ J -> Computable J)
          (sym
            (cong₂
              (hasTy (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []))
              (cong (λ rho -> subTm rho t) (liftSubstCompKeep (liftSubst sigma)))
              (cong (λ rho -> subTy rho T) (liftSubstCompKeep (liftSubst sigma)))))
          (substSccTm2 fits cFits dAσ dBσ (assocTmLeft dtu)))
        (λ tau fits2 ->
          packClosedSubst fits2
            (subst
              (λ J -> Computable J)
              (sym
                (cong₃ (termEq [])
                  (cong (λ rho -> subTm tau (subTm rho t)) (liftSubstCompKeep (liftSubst sigma))
                    ∙ subTmComp tau (liftSubst (liftSubst sigma)) t)
                  (cong (λ rho -> subTm tau (subTm rho u)) (liftSubstCompKeep (liftSubst sigma))
                    ∙ subTmComp tau (liftSubst (liftSubst sigma)) u)
                  (cong (λ rho -> subTy tau (subTy rho T)) (liftSubstCompKeep (liftSubst sigma))
                    ∙ subTyComp tau (liftSubst (liftSubst sigma)) T)))
              (substDerivTmEqComp
                dtu
                (composeTwoBinders fits dAσ dBσ fits2)
                (composeTwoBindersComp cFits fits2))))
        (λ tau₁ tau₂ fitsEq2 ->
          packClosedEqSubst fitsEq2
            (subst
              (λ J -> Computable J)
              (sym
                (cong₃ (termEq [])
                  (cong (λ rho -> subTm tau₁ (subTm rho t)) (liftSubstCompKeep (liftSubst sigma))
                    ∙ subTmComp tau₁ (liftSubst (liftSubst sigma)) t)
                  (cong (λ rho -> subTm tau₂ (subTm rho u)) (liftSubstCompKeep (liftSubst sigma))
                    ∙ subTmComp tau₂ (liftSubst (liftSubst sigma)) u)
                  (cong (λ rho -> subTy tau₁ (subTy rho T)) (liftSubstCompKeep (liftSubst sigma))
                    ∙ subTyComp tau₁ (liftSubst (liftSubst sigma)) T)))
              (eqSubDerivTmEqComp
                dtu
                (composeTwoBindersEq fits dAσ dBσ fitsEq2)
                (composeTwoBindersCompEq cFits fitsEq2)))))

  eqSubOpenTy1 : {gamma : Ctx} {A B : RawType} {sigma tau : Subst}
    -> FitsEqSubst [] gamma sigma tau
    -> CompFitsEqSubst gamma sigma tau
    -> Derivable (isType [] (subTy sigma A))
    -> Computable (isType (A ∷ gamma) B)
    -> Computable (typeEq (subTy sigma A ∷ []) (subTy (liftSubst sigma) B) (subTy (liftSubst tau) B))
  eqSubOpenTy1 {gamma = gamma} {A = A} {B = B} {sigma = sigma} {tau = tau} fitsEq cFitsEq dAσ dB =
    let
      sigmaCFits = compFitsEqLeft cFitsEq
      sigmaFits = compFitsToFits sigmaCFits
      liftedEq :
        FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma)
          (liftSubst sigma)
          (liftSubst tau)
      liftedEq =
        subst
          (λ rho -> FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma) rho (liftSubst tau))
          (liftSubstCompKeep sigma)
          (subst
            (λ rho ->
              FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma)
                (consSubst (var zero) (compSub (keepSubstBy 1) sigma))
                rho)
            (liftSubstCompKeep tau)
            (liftFitsEqOne fitsEq dAσ))
    in
    case dB of λ where
      (compTyOpen neqBody dBody sub subEq) ->
        compTyEqOpen
          nonemptyNeNil
          (eqSubTyRule dBody liftedEq)
          (substOpenTy1 sigmaFits sigmaCFits dAσ dB)
          (λ rho fits2 ->
            let
              composedFitsEq = composeFitsEq fits2 liftedEq
              closedEq =
                subEq
                  (compSub rho (liftSubst sigma))
                  (compSub rho (liftSubst tau))
                  composedFitsEq
              body =
                subst
                  (λ J -> Computable J)
                  (sym
                    (cong₂ (typeEq [])
                      (subTyComp rho (liftSubst sigma) B)
                      (subTyComp rho (liftSubst tau) B)))
                  (ClosedEqSubstComp.closedEqComp closedEq)
            in
            packClosedSubst fits2 body)
          (λ rho eta fitsEq2 ->
            let
              composedFitsEq = composeEqFitsEq fitsEq2 liftedEq
              closedEq =
                subEq
                  (compSub rho (liftSubst sigma))
                  (compSub eta (liftSubst tau))
                  composedFitsEq
              body =
                subst
                  (λ J -> Computable J)
                  (sym
                    (cong₂ (typeEq [])
                      (subTyComp rho (liftSubst sigma) B)
                      (subTyComp eta (liftSubst tau) B)))
                  (ClosedEqSubstComp.closedEqComp closedEq)
            in
            packClosedEqSubst fitsEq2 body)

  eqSubOpenTyEq1 : {gamma : Ctx} {A B C : RawType} {sigma tau : Subst}
    -> FitsEqSubst [] gamma sigma tau
    -> CompFitsEqSubst gamma sigma tau
    -> Derivable (isType [] (subTy sigma A))
    -> Computable (typeEq (A ∷ gamma) B C)
    -> Computable (typeEq (subTy sigma A ∷ []) (subTy (liftSubst sigma) B) (subTy (liftSubst tau) C))
  eqSubOpenTyEq1 {gamma = gamma} {A = A} {B = B} {C = C} {sigma = sigma} {tau = tau} fitsEq cFitsEq dAσ dBC =
    let
      sigmaCFits = compFitsEqLeft cFitsEq
      sigmaFits = compFitsToFits sigmaCFits
      liftedEq :
        FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma)
          (liftSubst sigma)
          (liftSubst tau)
      liftedEq =
        subst
          (λ rho -> FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma) rho (liftSubst tau))
          (liftSubstCompKeep sigma)
          (subst
            (λ rho ->
              FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma)
                (consSubst (var zero) (compSub (keepSubstBy 1) sigma))
                rho)
            (liftSubstCompKeep tau)
            (liftFitsEqOne fitsEq dAσ))
    in
    case dBC of λ where
      (compTyEqOpen neqBody dBody compLeft sub subEq) ->
        compTyEqOpen
          nonemptyNeNil
          (eqSubTyEqRule dBody liftedEq)
          (substOpenTy1 sigmaFits sigmaCFits dAσ compLeft)
          (λ rho fits2 ->
            let
              composedFitsEq = composeFitsEq fits2 liftedEq
              closedEq =
                subEq
                  (compSub rho (liftSubst sigma))
                  (compSub rho (liftSubst tau))
                  composedFitsEq
              body =
                subst
                  (λ J -> Computable J)
                  (sym
                    (cong₂ (typeEq [])
                      (subTyComp rho (liftSubst sigma) B)
                      (subTyComp rho (liftSubst tau) C)))
                  (ClosedEqSubstComp.closedEqComp closedEq)
            in
            packClosedSubst fits2 body)
          (λ rho eta fitsEq2 ->
            let
              composedFitsEq = composeEqFitsEq fitsEq2 liftedEq
              closedEq =
                subEq
                  (compSub rho (liftSubst sigma))
                  (compSub eta (liftSubst tau))
                  composedFitsEq
              body =
                subst
                  (λ J -> Computable J)
                  (sym
                    (cong₂ (typeEq [])
                      (subTyComp rho (liftSubst sigma) B)
                      (subTyComp eta (liftSubst tau) C)))
                  (ClosedEqSubstComp.closedEqComp closedEq)
            in
            packClosedEqSubst fitsEq2 body)

  eqSubOpenTm1 : {gamma : Ctx} {A T : RawType} {t : RawTerm} {sigma tau : Subst}
    -> FitsEqSubst [] gamma sigma tau
    -> CompFitsEqSubst gamma sigma tau
    -> Derivable (isType [] (subTy sigma A))
    -> Computable (hasTy (A ∷ gamma) t T)
    -> Computable
         (termEq (subTy sigma A ∷ [])
           (subTm (liftSubst sigma) t)
           (subTm (liftSubst tau) t)
           (subTy (liftSubst sigma) T))
  eqSubOpenTm1 {gamma = gamma} {A = A} {T = T} {t = t} {sigma = sigma} {tau = tau}
    fitsEq cFitsEq dAσ dt =
    let
      sigmaCFits = compFitsEqLeft cFitsEq
      sigmaFits = compFitsToFits sigmaCFits
      liftedEq :
        FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma)
          (liftSubst sigma)
          (liftSubst tau)
      liftedEq =
        subst
          (λ rho -> FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma) rho (liftSubst tau))
          (liftSubstCompKeep sigma)
          (subst
            (λ rho ->
              FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma)
                (consSubst (var zero) (compSub (keepSubstBy 1) sigma))
                rho)
            (liftSubstCompKeep tau)
            (liftFitsEqOne fitsEq dAσ))
    in
    case dt of λ where
      (compTmOpen neqBody dBody compTy sub subEq) ->
        compTmEqOpen
          nonemptyNeNil
          (eqSubTmRule dBody liftedEq)
          (substOpenTm1 sigmaFits sigmaCFits dAσ dt)
          (λ rho fits2 ->
            let
              composedFitsEq = composeFitsEq fits2 liftedEq
              closedEq =
                subEq
                  (compSub rho (liftSubst sigma))
                  (compSub rho (liftSubst tau))
                  composedFitsEq
              body =
                subst
                  (λ J -> Computable J)
                  (sym
                    (cong₃ (termEq [])
                      (subTmComp rho (liftSubst sigma) t)
                      (subTmComp rho (liftSubst tau) t)
                      (subTyComp rho (liftSubst sigma) T)))
                  (ClosedEqSubstComp.closedEqComp closedEq)
            in
            packClosedSubst fits2 body)
          (λ rho eta fitsEq2 ->
            let
              composedFitsEq = composeEqFitsEq fitsEq2 liftedEq
              closedEq =
                subEq
                  (compSub rho (liftSubst sigma))
                  (compSub eta (liftSubst tau))
                  composedFitsEq
              body =
                subst
                  (λ J -> Computable J)
                  (sym
                    (cong₃ (termEq [])
                      (subTmComp rho (liftSubst sigma) t)
                      (subTmComp eta (liftSubst tau) t)
                      (subTyComp rho (liftSubst sigma) T)))
                  (ClosedEqSubstComp.closedEqComp closedEq)
            in
            packClosedEqSubst fitsEq2 body)

  eqSubOpenTmEq1 : {gamma : Ctx} {A T : RawType} {t u : RawTerm} {sigma tau : Subst}
    -> FitsEqSubst [] gamma sigma tau
    -> CompFitsEqSubst gamma sigma tau
    -> Derivable (isType [] (subTy sigma A))
    -> Computable (termEq (A ∷ gamma) t u T)
    -> Computable
         (termEq (subTy sigma A ∷ [])
           (subTm (liftSubst sigma) t)
           (subTm (liftSubst tau) u)
           (subTy (liftSubst sigma) T))
  eqSubOpenTmEq1 {gamma = gamma} {A = A} {T = T} {t = t} {u = u} {sigma = sigma} {tau = tau}
    fitsEq cFitsEq dAσ dtu =
    let
      sigmaCFits = compFitsEqLeft cFitsEq
      sigmaFits = compFitsToFits sigmaCFits
      liftedEq :
        FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma)
          (liftSubst sigma)
          (liftSubst tau)
      liftedEq =
        subst
          (λ rho -> FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma) rho (liftSubst tau))
          (liftSubstCompKeep sigma)
          (subst
            (λ rho ->
              FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma)
                (consSubst (var zero) (compSub (keepSubstBy 1) sigma))
                rho)
            (liftSubstCompKeep tau)
            (liftFitsEqOne fitsEq dAσ))
    in
    case dtu of λ where
      (compTmEqOpen neqBody dBody compTm sub subEq) ->
        compTmEqOpen
          nonemptyNeNil
          (eqSubTmEqRule dBody liftedEq)
          (substOpenTm1 sigmaFits sigmaCFits dAσ compTm)
          (λ rho fits2 ->
            let
              composedFitsEq = composeFitsEq fits2 liftedEq
              closedEq =
                subEq
                  (compSub rho (liftSubst sigma))
                  (compSub rho (liftSubst tau))
                  composedFitsEq
              body =
                subst
                  (λ J -> Computable J)
                  (sym
                    (cong₃ (termEq [])
                      (subTmComp rho (liftSubst sigma) t)
                      (subTmComp rho (liftSubst tau) u)
                      (subTyComp rho (liftSubst sigma) T)))
                  (ClosedEqSubstComp.closedEqComp closedEq)
            in
            packClosedSubst fits2 body)
          (λ rho eta fitsEq2 ->
            let
              composedFitsEq = composeEqFitsEq fitsEq2 liftedEq
              closedEq =
                subEq
                  (compSub rho (liftSubst sigma))
                  (compSub eta (liftSubst tau))
                  composedFitsEq
              body =
                subst
                  (λ J -> Computable J)
                  (sym
                    (cong₃ (termEq [])
                      (subTmComp rho (liftSubst sigma) t)
                      (subTmComp eta (liftSubst tau) u)
                      (subTyComp rho (liftSubst sigma) T)))
                  (ClosedEqSubstComp.closedEqComp closedEq)
            in
            packClosedEqSubst fitsEq2 body)

  eqSubOpenTm2 : {gamma : Ctx} {A B T : RawType} {t : RawTerm} {sigma tau : Subst}
    -> FitsEqSubst [] gamma sigma tau
    -> CompFitsEqSubst gamma sigma tau
    -> Derivable (isType [] (subTy sigma A))
    -> Derivable (isType (subTy sigma A ∷ []) (subTy (liftSubst sigma) B))
    -> Computable (hasTy (B ∷ A ∷ gamma) t T)
    -> Computable
         (termEq (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ [])
           (subTm (liftSubst (liftSubst sigma)) t)
           (subTm (liftSubst (liftSubst tau)) t)
           (subTy (liftSubst (liftSubst sigma)) T))
  eqSubOpenTm2 {gamma = gamma} {A = A} {B = B} {T = T} {t = t} {sigma = sigma} {tau = tau}
    fitsEq cFitsEq dAσ dBσ dt =
    let
      sigmaCFits = compFitsEqLeft cFitsEq
      sigmaFits = compFitsToFits sigmaCFits
      lifted1Eq :
        FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma)
          (liftSubst sigma)
          (liftSubst tau)
      lifted1Eq =
        subst
          (λ rho -> FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma) rho (liftSubst tau))
          (liftSubstCompKeep sigma)
          (subst
            (λ rho ->
              FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma)
                (consSubst (var zero) (compSub (keepSubstBy 1) sigma))
                rho)
            (liftSubstCompKeep tau)
            (liftFitsEqOne fitsEq dAσ))
      lifted2Eq :
        FitsEqSubst (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) (B ∷ A ∷ gamma)
          (liftSubst (liftSubst sigma))
          (liftSubst (liftSubst tau))
      lifted2Eq =
        subst
          (λ rho ->
            FitsEqSubst (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) (B ∷ A ∷ gamma)
              rho
              (liftSubst (liftSubst tau)))
          (liftSubstCompKeep (liftSubst sigma))
          (subst
            (λ rho ->
              FitsEqSubst (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) (B ∷ A ∷ gamma)
                (consSubst (var zero) (compSub (keepSubstBy 1) (liftSubst sigma)))
                rho)
            (liftSubstCompKeep (liftSubst tau))
            (liftFitsEq lifted1Eq dBσ))
    in
    case dt of λ where
      (compTmOpen neqBody dBody compTy sub subEq) ->
        compTmEqOpen
          nonemptyNeNil
          (eqSubTmRule dBody lifted2Eq)
          (substOpenTm2 sigmaFits sigmaCFits dAσ dBσ dt)
          (λ rho fits2 ->
            let
              composedFitsEq = composeFitsEq fits2 lifted2Eq
              closedEq =
                subEq
                  (compSub rho (liftSubst (liftSubst sigma)))
                  (compSub rho (liftSubst (liftSubst tau)))
                  composedFitsEq
              body =
                subst
                  (λ J -> Computable J)
                  (sym
                    (cong₃ (termEq [])
                      (subTmComp rho (liftSubst (liftSubst sigma)) t)
                      (subTmComp rho (liftSubst (liftSubst tau)) t)
                      (subTyComp rho (liftSubst (liftSubst sigma)) T)))
                  (ClosedEqSubstComp.closedEqComp closedEq)
            in
            packClosedSubst fits2 body)
          (λ rho eta fitsEq2 ->
            let
              composedFitsEq = composeEqFitsEq fitsEq2 lifted2Eq
              closedEq =
                subEq
                  (compSub rho (liftSubst (liftSubst sigma)))
                  (compSub eta (liftSubst (liftSubst tau)))
                  composedFitsEq
              body =
                subst
                  (λ J -> Computable J)
                  (sym
                    (cong₃ (termEq [])
                      (subTmComp rho (liftSubst (liftSubst sigma)) t)
                      (subTmComp eta (liftSubst (liftSubst tau)) t)
                      (subTyComp rho (liftSubst (liftSubst sigma)) T)))
                  (ClosedEqSubstComp.closedEqComp closedEq)
            in
            packClosedEqSubst fitsEq2 body)

  eqSubOpenTmEq2 : {gamma : Ctx} {A B T : RawType} {t u : RawTerm} {sigma tau : Subst}
    -> FitsEqSubst [] gamma sigma tau
    -> CompFitsEqSubst gamma sigma tau
    -> Derivable (isType [] (subTy sigma A))
    -> Derivable (isType (subTy sigma A ∷ []) (subTy (liftSubst sigma) B))
    -> Computable (termEq (B ∷ A ∷ gamma) t u T)
    -> Computable
         (termEq (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ [])
           (subTm (liftSubst (liftSubst sigma)) t)
           (subTm (liftSubst (liftSubst tau)) u)
           (subTy (liftSubst (liftSubst sigma)) T))
  eqSubOpenTmEq2 {gamma = gamma} {A = A} {B = B} {T = T} {t = t} {u = u} {sigma = sigma} {tau = tau}
    fitsEq cFitsEq dAσ dBσ dtu =
    let
      sigmaCFits = compFitsEqLeft cFitsEq
      sigmaFits = compFitsToFits sigmaCFits
      lifted1Eq :
        FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma)
          (liftSubst sigma)
          (liftSubst tau)
      lifted1Eq =
        subst
          (λ rho -> FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma) rho (liftSubst tau))
          (liftSubstCompKeep sigma)
          (subst
            (λ rho ->
              FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma)
                (consSubst (var zero) (compSub (keepSubstBy 1) sigma))
                rho)
            (liftSubstCompKeep tau)
            (liftFitsEqOne fitsEq dAσ))
      lifted2Eq :
        FitsEqSubst (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) (B ∷ A ∷ gamma)
          (liftSubst (liftSubst sigma))
          (liftSubst (liftSubst tau))
      lifted2Eq =
        subst
          (λ rho ->
            FitsEqSubst (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) (B ∷ A ∷ gamma)
              rho
              (liftSubst (liftSubst tau)))
          (liftSubstCompKeep (liftSubst sigma))
          (subst
            (λ rho ->
              FitsEqSubst (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) (B ∷ A ∷ gamma)
                (consSubst (var zero) (compSub (keepSubstBy 1) (liftSubst sigma)))
                rho)
            (liftSubstCompKeep (liftSubst tau))
            (liftFitsEq lifted1Eq dBσ))
    in
    case dtu of λ where
      (compTmEqOpen neqBody dBody compTm sub subEq) ->
        compTmEqOpen
          nonemptyNeNil
          (eqSubTmEqRule dBody lifted2Eq)
          (substOpenTm2 sigmaFits sigmaCFits dAσ dBσ compTm)
          (λ rho fits2 ->
            let
              composedFitsEq = composeFitsEq fits2 lifted2Eq
              closedEq =
                subEq
                  (compSub rho (liftSubst (liftSubst sigma)))
                  (compSub rho (liftSubst (liftSubst tau)))
                  composedFitsEq
              body =
                subst
                  (λ J -> Computable J)
                  (sym
                    (cong₃ (termEq [])
                      (subTmComp rho (liftSubst (liftSubst sigma)) t)
                      (subTmComp rho (liftSubst (liftSubst tau)) u)
                      (subTyComp rho (liftSubst (liftSubst sigma)) T)))
                  (ClosedEqSubstComp.closedEqComp closedEq)
            in
            packClosedSubst fits2 body)
          (λ rho eta fitsEq2 ->
            let
              composedFitsEq = composeEqFitsEq fitsEq2 lifted2Eq
              closedEq =
                subEq
                  (compSub rho (liftSubst (liftSubst sigma)))
                  (compSub eta (liftSubst (liftSubst tau)))
                  composedFitsEq
              body =
                subst
                  (λ J -> Computable J)
                  (sym
                    (cong₃ (termEq [])
                      (subTmComp rho (liftSubst (liftSubst sigma)) t)
                      (subTmComp eta (liftSubst (liftSubst tau)) u)
                      (subTyComp rho (liftSubst (liftSubst sigma)) T)))
                  (ClosedEqSubstComp.closedEqComp closedEq)
            in
            packClosedEqSubst fitsEq2 body)

  eqSubSccTy1 : {gamma : Ctx} {A B : RawType} {sigma tau : Subst}
    -> FitsEqSubst [] gamma sigma tau
    -> CompFitsEqSubst gamma sigma tau
    -> Derivable (isType [] (subTy sigma A))
    -> Derivable (isType (A ∷ gamma) B)
    -> Computable (typeEq (subTy sigma A ∷ []) (subTy (liftSubst sigma) B) (subTy (liftSubst tau) B))
  eqSubSccTy1 {gamma = gamma} {A = A} {B = B} {sigma = sigma} {tau = tau} fitsEq cFitsEq dAσ dB =
    let
      sigmaCFits = compFitsEqLeft cFitsEq
      sigmaFits = compFitsToFits sigmaCFits
      liftedEq :
        FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma)
          (liftSubst sigma)
          (liftSubst tau)
      liftedEq =
        subst
          (λ rho -> FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma) rho (liftSubst tau))
          (liftSubstCompKeep sigma)
          (subst
            (λ rho ->
              FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma)
                (consSubst (var zero) (compSub (keepSubstBy 1) sigma))
                rho)
            (liftSubstCompKeep tau)
            (liftFitsEqOne fitsEq dAσ))
    in
    compTyEqOpen
      nonemptyNeNil
      (eqSubTyRule dB liftedEq)
      (substSccTy1 sigmaFits sigmaCFits dAσ dB)
      (λ rho fits2 ->
        let
          composedFitsEq = composeFitsEq fits2 liftedEq
        in
        packClosedSubst fits2
          (subst
            (λ J -> Computable J)
            (sym
              (cong₂ (typeEq [])
                (subTyComp rho (liftSubst sigma) B)
                (subTyComp rho (liftSubst tau) B)))
            (eqSubDerivTyComp
              dB
              composedFitsEq
              (composeOneBinderEqComp fits2 cFitsEq))))
      (λ rho eta fitsEq2 ->
        let
          composedFitsEq = composeEqFitsEq fitsEq2 liftedEq
        in
        packClosedEqSubst fitsEq2
          (subst
            (λ J -> Computable J)
            (sym
              (cong₂ (typeEq [])
                (subTyComp rho (liftSubst sigma) B)
                (subTyComp eta (liftSubst tau) B)))
            (eqSubDerivTyComp
              dB
              composedFitsEq
              (composeOneBinderEqCompEq cFitsEq fitsEq2))))

  eqSubSccTyEq1 : {gamma : Ctx} {A B C : RawType} {sigma tau : Subst}
    -> FitsEqSubst [] gamma sigma tau
    -> CompFitsEqSubst gamma sigma tau
    -> Derivable (isType [] (subTy sigma A))
    -> Derivable (typeEq (A ∷ gamma) B C)
    -> Computable (typeEq (subTy sigma A ∷ []) (subTy (liftSubst sigma) B) (subTy (liftSubst tau) C))
  eqSubSccTyEq1 {gamma = gamma} {A = A} {B = B} {C = C} {sigma = sigma} {tau = tau} fitsEq cFitsEq dAσ dBC =
    let
      sigmaCFits = compFitsEqLeft cFitsEq
      sigmaFits = compFitsToFits sigmaCFits
      liftedEq :
        FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma)
          (liftSubst sigma)
          (liftSubst tau)
      liftedEq =
        subst
          (λ rho -> FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma) rho (liftSubst tau))
          (liftSubstCompKeep sigma)
          (subst
            (λ rho ->
              FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma)
                (consSubst (var zero) (compSub (keepSubstBy 1) sigma))
                rho)
            (liftSubstCompKeep tau)
            (liftFitsEqOne fitsEq dAσ))
    in
    compTyEqOpen
      nonemptyNeNil
      (eqSubTyEqRule dBC liftedEq)
      (substSccTy1 sigmaFits sigmaCFits dAσ (assocTyLeft dBC))
      (λ rho fits2 ->
        let
          composedFitsEq = composeFitsEq fits2 liftedEq
        in
        packClosedSubst fits2
          (subst
            (λ J -> Computable J)
            (sym
              (cong₂ (typeEq [])
                (subTyComp rho (liftSubst sigma) B)
                (subTyComp rho (liftSubst tau) C)))
            (eqSubDerivTyEqComp
              dBC
              composedFitsEq
              (composeOneBinderEqComp fits2 cFitsEq))))
      (λ rho eta fitsEq2 ->
        let
          composedFitsEq = composeEqFitsEq fitsEq2 liftedEq
        in
        packClosedEqSubst fitsEq2
          (subst
            (λ J -> Computable J)
            (sym
              (cong₂ (typeEq [])
                (subTyComp rho (liftSubst sigma) B)
                (subTyComp eta (liftSubst tau) C)))
            (eqSubDerivTyEqComp
              dBC
              composedFitsEq
              (composeOneBinderEqCompEq cFitsEq fitsEq2))))

  eqSubSccTm1 : {gamma : Ctx} {A T : RawType} {t : RawTerm} {sigma tau : Subst}
    -> FitsEqSubst [] gamma sigma tau
    -> CompFitsEqSubst gamma sigma tau
    -> Derivable (isType [] (subTy sigma A))
    -> Derivable (hasTy (A ∷ gamma) t T)
    -> Computable
         (termEq (subTy sigma A ∷ [])
           (subTm (liftSubst sigma) t)
           (subTm (liftSubst tau) t)
           (subTy (liftSubst sigma) T))
  eqSubSccTm1 {gamma = gamma} {A = A} {T = T} {t = t} {sigma = sigma} {tau = tau}
    fitsEq cFitsEq dAσ dt =
    let
      sigmaCFits = compFitsEqLeft cFitsEq
      sigmaFits = compFitsToFits sigmaCFits
      liftedEq :
        FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma)
          (liftSubst sigma)
          (liftSubst tau)
      liftedEq =
        subst
          (λ rho -> FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma) rho (liftSubst tau))
          (liftSubstCompKeep sigma)
          (subst
            (λ rho ->
              FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma)
                (consSubst (var zero) (compSub (keepSubstBy 1) sigma))
                rho)
            (liftSubstCompKeep tau)
            (liftFitsEqOne fitsEq dAσ))
    in
    compTmEqOpen
      nonemptyNeNil
      (eqSubTmRule dt liftedEq)
      (substSccTm1 sigmaFits sigmaCFits dAσ dt)
      (λ rho fits2 ->
        let
          composedFitsEq = composeFitsEq fits2 liftedEq
        in
        packClosedSubst fits2
          (subst
            (λ J -> Computable J)
            (sym
              (cong₃ (termEq [])
                (subTmComp rho (liftSubst sigma) t)
                (subTmComp rho (liftSubst tau) t)
                (subTyComp rho (liftSubst sigma) T)))
            (eqSubDerivTmComp
              dt
              composedFitsEq
              (composeOneBinderEqComp fits2 cFitsEq))))
      (λ rho eta fitsEq2 ->
        let
          composedFitsEq = composeEqFitsEq fitsEq2 liftedEq
        in
        packClosedEqSubst fitsEq2
          (subst
            (λ J -> Computable J)
            (sym
              (cong₃ (termEq [])
                (subTmComp rho (liftSubst sigma) t)
                (subTmComp eta (liftSubst tau) t)
                (subTyComp rho (liftSubst sigma) T)))
            (eqSubDerivTmComp
              dt
              composedFitsEq
              (composeOneBinderEqCompEq cFitsEq fitsEq2))))

  eqSubSccTmEq1 : {gamma : Ctx} {A T : RawType} {t u : RawTerm} {sigma tau : Subst}
    -> FitsEqSubst [] gamma sigma tau
    -> CompFitsEqSubst gamma sigma tau
    -> Derivable (isType [] (subTy sigma A))
    -> Derivable (termEq (A ∷ gamma) t u T)
    -> Computable
         (termEq (subTy sigma A ∷ [])
           (subTm (liftSubst sigma) t)
           (subTm (liftSubst tau) u)
           (subTy (liftSubst sigma) T))
  eqSubSccTmEq1 {gamma = gamma} {A = A} {T = T} {t = t} {u = u} {sigma = sigma} {tau = tau}
    fitsEq cFitsEq dAσ dtu =
    let
      sigmaCFits = compFitsEqLeft cFitsEq
      sigmaFits = compFitsToFits sigmaCFits
      liftedEq :
        FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma)
          (liftSubst sigma)
          (liftSubst tau)
      liftedEq =
        subst
          (λ rho -> FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma) rho (liftSubst tau))
          (liftSubstCompKeep sigma)
          (subst
            (λ rho ->
              FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma)
                (consSubst (var zero) (compSub (keepSubstBy 1) sigma))
                rho)
            (liftSubstCompKeep tau)
            (liftFitsEqOne fitsEq dAσ))
    in
    compTmEqOpen
      nonemptyNeNil
      (eqSubTmEqRule dtu liftedEq)
      (substSccTm1 sigmaFits sigmaCFits dAσ (assocTmLeft dtu))
      (λ rho fits2 ->
        let
          composedFitsEq = composeFitsEq fits2 liftedEq
        in
        packClosedSubst fits2
          (subst
            (λ J -> Computable J)
            (sym
              (cong₃ (termEq [])
                (subTmComp rho (liftSubst sigma) t)
                (subTmComp rho (liftSubst tau) u)
                (subTyComp rho (liftSubst sigma) T)))
            (eqSubDerivTmEqComp
              dtu
              composedFitsEq
              (composeOneBinderEqComp fits2 cFitsEq))))
      (λ rho eta fitsEq2 ->
        let
          composedFitsEq = composeEqFitsEq fitsEq2 liftedEq
        in
        packClosedEqSubst fitsEq2
          (subst
            (λ J -> Computable J)
            (sym
              (cong₃ (termEq [])
                (subTmComp rho (liftSubst sigma) t)
                (subTmComp eta (liftSubst tau) u)
                (subTyComp rho (liftSubst sigma) T)))
            (eqSubDerivTmEqComp
              dtu
              composedFitsEq
              (composeOneBinderEqCompEq cFitsEq fitsEq2))))

  eqSubSccTm2 : {gamma : Ctx} {A B T : RawType} {t : RawTerm} {sigma tau : Subst}
    -> FitsEqSubst [] gamma sigma tau
    -> CompFitsEqSubst gamma sigma tau
    -> Derivable (isType [] (subTy sigma A))
    -> Derivable (isType (subTy sigma A ∷ []) (subTy (liftSubst sigma) B))
    -> Derivable (hasTy (B ∷ A ∷ gamma) t T)
    -> Computable
         (termEq (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ [])
           (subTm (liftSubst (liftSubst sigma)) t)
           (subTm (liftSubst (liftSubst tau)) t)
           (subTy (liftSubst (liftSubst sigma)) T))
  eqSubSccTm2 {gamma = gamma} {A = A} {B = B} {T = T} {t = t} {sigma = sigma} {tau = tau}
    fitsEq cFitsEq dAσ dBσ dt =
    let
      sigmaCFits = compFitsEqLeft cFitsEq
      sigmaFits = compFitsToFits sigmaCFits
      lifted1Eq :
        FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma)
          (liftSubst sigma)
          (liftSubst tau)
      lifted1Eq =
        subst
          (λ rho -> FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma) rho (liftSubst tau))
          (liftSubstCompKeep sigma)
          (subst
            (λ rho ->
              FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma)
                (consSubst (var zero) (compSub (keepSubstBy 1) sigma))
                rho)
            (liftSubstCompKeep tau)
            (liftFitsEqOne fitsEq dAσ))
      lifted2Eq :
        FitsEqSubst (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) (B ∷ A ∷ gamma)
          (liftSubst (liftSubst sigma))
          (liftSubst (liftSubst tau))
      lifted2Eq =
        subst
          (λ rho ->
            FitsEqSubst (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) (B ∷ A ∷ gamma)
              rho
              (liftSubst (liftSubst tau)))
          (liftSubstCompKeep (liftSubst sigma))
          (subst
            (λ rho ->
              FitsEqSubst (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) (B ∷ A ∷ gamma)
                (consSubst (var zero) (compSub (keepSubstBy 1) (liftSubst sigma)))
                rho)
            (liftSubstCompKeep (liftSubst tau))
            (liftFitsEq lifted1Eq dBσ))
    in
    compTmEqOpen
      nonemptyNeNil
      (eqSubTmRule dt lifted2Eq)
      (substSccTm2 sigmaFits sigmaCFits dAσ dBσ dt)
      (λ rho fits2 ->
        let
          composedFitsEq = composeFitsEq fits2 lifted2Eq
        in
        packClosedSubst fits2
          (subst
            (λ J -> Computable J)
            (sym
              (cong₃ (termEq [])
                (subTmComp rho (liftSubst (liftSubst sigma)) t)
                (subTmComp rho (liftSubst (liftSubst tau)) t)
                (subTyComp rho (liftSubst (liftSubst sigma)) T)))
            (eqSubDerivTmComp
              dt
              composedFitsEq
              (composeTwoBindersEqComp cFitsEq fits2))))
      (λ rho eta fitsEq2 ->
        let
          composedFitsEq = composeEqFitsEq fitsEq2 lifted2Eq
        in
        packClosedEqSubst fitsEq2
          (subst
            (λ J -> Computable J)
            (sym
              (cong₃ (termEq [])
                (subTmComp rho (liftSubst (liftSubst sigma)) t)
                (subTmComp eta (liftSubst (liftSubst tau)) t)
                (subTyComp rho (liftSubst (liftSubst sigma)) T)))
            (eqSubDerivTmComp
              dt
              composedFitsEq
              (composeTwoBindersEqCompEq cFitsEq fitsEq2))))

  eqSubSccTmEq2 : {gamma : Ctx} {A B T : RawType} {t u : RawTerm} {sigma tau : Subst}
    -> FitsEqSubst [] gamma sigma tau
    -> CompFitsEqSubst gamma sigma tau
    -> Derivable (isType [] (subTy sigma A))
    -> Derivable (isType (subTy sigma A ∷ []) (subTy (liftSubst sigma) B))
    -> Derivable (termEq (B ∷ A ∷ gamma) t u T)
    -> Computable
         (termEq (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ [])
           (subTm (liftSubst (liftSubst sigma)) t)
           (subTm (liftSubst (liftSubst tau)) u)
           (subTy (liftSubst (liftSubst sigma)) T))
  eqSubSccTmEq2 {gamma = gamma} {A = A} {B = B} {T = T} {t = t} {u = u} {sigma = sigma} {tau = tau}
    fitsEq cFitsEq dAσ dBσ dtu =
    let
      sigmaCFits = compFitsEqLeft cFitsEq
      sigmaFits = compFitsToFits sigmaCFits
      lifted1Eq :
        FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma)
          (liftSubst sigma)
          (liftSubst tau)
      lifted1Eq =
        subst
          (λ rho -> FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma) rho (liftSubst tau))
          (liftSubstCompKeep sigma)
          (subst
            (λ rho ->
              FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma)
                (consSubst (var zero) (compSub (keepSubstBy 1) sigma))
                rho)
            (liftSubstCompKeep tau)
            (liftFitsEqOne fitsEq dAσ))
      lifted2Eq :
        FitsEqSubst (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) (B ∷ A ∷ gamma)
          (liftSubst (liftSubst sigma))
          (liftSubst (liftSubst tau))
      lifted2Eq =
        subst
          (λ rho ->
            FitsEqSubst (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) (B ∷ A ∷ gamma)
              rho
              (liftSubst (liftSubst tau)))
          (liftSubstCompKeep (liftSubst sigma))
          (subst
            (λ rho ->
              FitsEqSubst (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) (B ∷ A ∷ gamma)
                (consSubst (var zero) (compSub (keepSubstBy 1) (liftSubst sigma)))
                rho)
            (liftSubstCompKeep (liftSubst tau))
            (liftFitsEq lifted1Eq dBσ))
    in
    compTmEqOpen
      nonemptyNeNil
      (eqSubTmEqRule dtu lifted2Eq)
      (substSccTm2 sigmaFits sigmaCFits dAσ dBσ (assocTmLeft dtu))
      (λ rho fits2 ->
        let
          composedFitsEq = composeFitsEq fits2 lifted2Eq
        in
        packClosedSubst fits2
          (subst
            (λ J -> Computable J)
            (sym
              (cong₃ (termEq [])
                (subTmComp rho (liftSubst (liftSubst sigma)) t)
                (subTmComp rho (liftSubst (liftSubst tau)) u)
                (subTyComp rho (liftSubst (liftSubst sigma)) T)))
            (eqSubDerivTmEqComp
              dtu
              composedFitsEq
              (composeTwoBindersEqComp cFitsEq fits2))))
      (λ rho eta fitsEq2 ->
        let
          composedFitsEq = composeEqFitsEq fitsEq2 lifted2Eq
        in
        packClosedEqSubst fitsEq2
          (subst
            (λ J -> Computable J)
            (sym
              (cong₃ (termEq [])
                (subTmComp rho (liftSubst (liftSubst sigma)) t)
                (subTmComp eta (liftSubst (liftSubst tau)) u)
                (subTyComp rho (liftSubst (liftSubst sigma)) T)))
            (eqSubDerivTmEqComp
              dtu
              composedFitsEq
              (composeTwoBindersEqCompEq cFitsEq fitsEq2))))

  substDerivTyComp : {gamma : Ctx} {A : RawType} {sigma : Subst}
    -> Derivable (isType gamma A)
    -> FitsSubst [] gamma sigma
    -> CompFitsSubst gamma sigma
    -> Computable (isType [] (subTy sigma A))
  substDerivTyComp (fTop wf) fits cFits = compFTopClosed
  substDerivTyComp {sigma = sigma} (fSigma {A = A} {B = B} dA dB) fits cFits =
    let
      compA = substDerivTyComp dA fits cFits
      dAσ = compToDerivable compA
      compB =
        subst
          (λ T -> Computable (isType (subTy sigma A ∷ []) T))
          (cong (λ rho -> subTy rho B) (liftSubstCompKeep sigma))
          (compTyOpen
            nonemptyNeNil
            (substTyRule dB (liftFitsOne fits dAσ))
            (λ tau fits2 ->
              packClosedSubst fits2
                (subst
                  (λ T -> Computable (isType [] T))
                  (sym
                    (cong (λ rho -> subTy tau (subTy rho B)) (liftSubstCompKeep sigma)
                      ∙ subTyComp tau (liftSubst sigma) B))
                  (substDerivTyComp
                    dB
                    (composeOneBinder fits dAσ fits2)
                    (composeOneBinderComp fits2 cFits))))
            (λ tau₁ tau₂ fitsEq2 ->
              packClosedEqSubst fitsEq2
                (subst
                  (λ J -> Computable J)
                  (sym
                    (cong₂ (typeEq [])
                      (cong (λ rho -> subTy tau₁ (subTy rho B)) (liftSubstCompKeep sigma)
                        ∙ subTyComp tau₁ (liftSubst sigma) B)
                      (cong (λ rho -> subTy tau₂ (subTy rho B)) (liftSubstCompKeep sigma)
                        ∙ subTyComp tau₂ (liftSubst sigma) B)))
                  (eqSubDerivTyComp
                    dB
                    (composeOneBinderEq fits dAσ fitsEq2)
                    (composeOneBinderCompEq cFits fitsEq2)))))
    in
    compFSigmaClosed compA compB
  substDerivTyComp (fEq dA da db) fits cFits =
    compFEqClosed
      (substDerivTyComp dA fits cFits)
      (substDerivTmComp da fits cFits)
      (substDerivTmComp db fits cFits)
  substDerivTyComp (fQtr dA) fits cFits =
    compFQtrClosed (substDerivTyComp dA fits cFits)
  substDerivTyComp {sigma = sigma} (weakenTy {delta = delta} {A = A} d wf) fits cFits =
    subst
      (λ T -> Computable (isType [] T))
      (sym (subTyWkBy sigma (length delta) A))
      (substDerivTyComp d (dropFits delta fits) (dropCompFits delta cFits))
  substDerivTyComp {sigma = sigma} (substTyRule {sigma = sigma'} {A = A} d fits') fits cFits =
    let
      composedFits = composeFits fits fits'
      composedCFits = composeCompFits fits' fits cFits
    in
    subst
      (λ T -> Computable (isType [] T))
      (sym (subTyComp sigma sigma' A))
      (substDerivTyComp d composedFits composedCFits)

  substDerivTyEqComp : {gamma : Ctx} {A B : RawType} {sigma : Subst}
    -> Derivable (typeEq gamma A B)
    -> FitsSubst [] gamma sigma
    -> CompFitsSubst gamma sigma
    -> Computable (typeEq [] (subTy sigma A) (subTy sigma B))
  substDerivTyEqComp (reflTy d) fits cFits =
    compReflTy (substDerivTyComp d fits cFits)
  substDerivTyEqComp (symTy d) fits cFits =
    compSymTyClosed (substDerivTyEqComp d fits cFits)
  substDerivTyEqComp (transTy d₁ d₂) fits cFits =
    compTransTyClosed (substDerivTyEqComp d₁ fits cFits) (substDerivTyEqComp d₂ fits cFits)
  substDerivTyEqComp {sigma = sigma} (fSigmaEq {A = A} {B = B} {D = D} dAC dBD) fits cFits =
    let
      compAC = substDerivTyEqComp dAC fits cFits
      compA = compTyEqLeft compAC
      compC = compTyEqRight compAC
      dAσ = compToDerivable compA
      compBD =
        subst
          (λ J -> Computable J)
          (cong₂ (typeEq (subTy sigma A ∷ []))
            (cong (λ rho -> subTy rho B) (liftSubstCompKeep sigma))
            (cong (λ rho -> subTy rho D) (liftSubstCompKeep sigma)))
          (compTyEqOpen
            nonemptyNeNil
            (substTyEqRule dBD (liftFitsOne fits dAσ))
            (subst
              (λ T -> Computable (isType (subTy sigma A ∷ []) T))
              (sym (cong (λ rho -> subTy rho B) (liftSubstCompKeep sigma)))
              (subst
                (λ T -> Computable (isType (subTy sigma A ∷ []) T))
                (cong (λ rho -> subTy rho B) (liftSubstCompKeep sigma))
                (compTyOpen
                  nonemptyNeNil
                  (substTyRule (assocTyLeft dBD) (liftFitsOne fits dAσ))
                  (λ tau fits2 ->
                    packClosedSubst fits2
                      (subst
                        (λ T -> Computable (isType [] T))
                        (sym
                          (cong (λ rho -> subTy tau (subTy rho B)) (liftSubstCompKeep sigma)
                            ∙ subTyComp tau (liftSubst sigma) B))
                        (substDerivTyComp
                          (assocTyLeft dBD)
                          (composeOneBinder fits dAσ fits2)
                          (composeOneBinderComp fits2 cFits))))
                  (λ tau₁ tau₂ fitsEq2 ->
                    packClosedEqSubst fitsEq2
                      (subst
                        (λ J -> Computable J)
                        (sym
                          (cong₂ (typeEq [])
                            (cong (λ rho -> subTy tau₁ (subTy rho B)) (liftSubstCompKeep sigma)
                              ∙ subTyComp tau₁ (liftSubst sigma) B)
                            (cong (λ rho -> subTy tau₂ (subTy rho B)) (liftSubstCompKeep sigma)
                              ∙ subTyComp tau₂ (liftSubst sigma) B)))
                        (eqSubDerivTyComp
                          (assocTyLeft dBD)
                          (composeOneBinderEq fits dAσ fitsEq2)
                          (composeOneBinderCompEq cFits fitsEq2)))))))
            (λ tau fits2 ->
              packClosedSubst fits2
                (subst
                  (λ J -> Computable J)
                  (sym
                    (cong₂ (typeEq [])
                      (cong (λ rho -> subTy tau (subTy rho B)) (liftSubstCompKeep sigma)
                        ∙ subTyComp tau (liftSubst sigma) B)
                      (cong (λ rho -> subTy tau (subTy rho D)) (liftSubstCompKeep sigma)
                        ∙ subTyComp tau (liftSubst sigma) D)))
                  (substDerivTyEqComp
                    dBD
                    (composeOneBinder fits dAσ fits2)
                    (composeOneBinderComp fits2 cFits))))
            (λ tau₁ tau₂ fitsEq2 ->
              packClosedEqSubst fitsEq2
                (subst
                  (λ J -> Computable J)
                  (sym
                    (cong₂ (typeEq [])
                      (cong (λ rho -> subTy tau₁ (subTy rho B)) (liftSubstCompKeep sigma)
                        ∙ subTyComp tau₁ (liftSubst sigma) B)
                      (cong (λ rho -> subTy tau₂ (subTy rho D)) (liftSubstCompKeep sigma)
                        ∙ subTyComp tau₂ (liftSubst sigma) D)))
                  (eqSubDerivTyEqComp
                    dBD
                    (composeOneBinderEq fits dAσ fitsEq2)
                    (composeOneBinderCompEq cFits fitsEq2)))))
      compSigmaA = compFSigmaClosed compA (compTyEqLeft compBD)
      compSigmaC = compFSigmaClosed compC (compTransportFamilyTy compAC (compTyEqRight compBD))
    in
    compTyEqClosedSigma
      (fSigmaEq (compToDerivable compAC) (compToDerivable compBD))
      compSigmaA
      compSigmaC
      evalSigma
      evalSigma
      compAC
      compBD
  substDerivTyEqComp (fEqEq dAC dac dbd) fits cFits =
    let
      compAC = substDerivTyEqComp dAC fits cFits
      compac = substDerivTmEqComp dac fits cFits
      compbd = substDerivTmEqComp dbd fits cFits
      compA = compTyEqLeft compAC
      compC = compTyEqRight compAC
      compa = compTmEqLeft compac
      compb = compTmEqLeft compbd
      compcA = compTmEqRightClosed compac
      compdA = compTmEqRightClosed compbd
      compc = compConvTmClosed compcA compAC
      compd = compConvTmClosed compdA compAC
      compEqA = compFEqClosed compA compa compb
      compEqC = compFEqClosed compC compc compd
    in
    compTyEqClosedEq
      (fEqEq (compToDerivable compAC) (compToDerivable compac) (compToDerivable compbd))
      compEqA
      compEqC
      evalEq
      evalEq
      compAC
      compac
      compbd
  substDerivTyEqComp (fQtrEq dAB) fits cFits =
    let
      compAB = substDerivTyEqComp dAB fits cFits
    in
    compTyEqClosedQtr
      (fQtrEq (compToDerivable compAB))
      (compFQtrClosed (compTyEqLeft compAB))
      (compFQtrClosed (compTyEqRight compAB))
      evalQtr
      evalQtr
      compAB
  substDerivTyEqComp {sigma = sigma} (weakenTyEq {delta = delta} {A = A} {B = B} d wf) fits cFits =
    subst
      (λ J -> Computable J)
      (cong₂ (typeEq [])
        (sym (subTyWkBy sigma (length delta) A))
        (sym (subTyWkBy sigma (length delta) B)))
      (substDerivTyEqComp d (dropFits delta fits) (dropCompFits delta cFits))
  substDerivTyEqComp {sigma = sigma} (substTyEqRule {sigma = sigma'} {A = A} {B = B} d fits') fits cFits =
    let
      composedFits = composeFits fits fits'
      composedCFits = composeCompFits fits' fits cFits
    in
    subst
      (λ J -> Computable J)
      (cong₂ (typeEq [])
        (sym (subTyComp sigma sigma' A))
        (sym (subTyComp sigma sigma' B)))
      (substDerivTyEqComp d composedFits composedCFits)
  substDerivTyEqComp {sigma = sigma} (eqSubTyRule {sigma = sigma'} {tau = tau'} {A = A} d fitsEq') fits cFits =
    let
      composedFitsEq = composeFitsEq fits fitsEq'
      composedCFitsEq = composeCompFitsEq fits cFits fitsEq'
    in
    subst
      (λ J -> Computable J)
      (cong₂ (typeEq [])
        (sym (subTyComp sigma sigma' A))
        (sym (subTyComp sigma tau' A)))
      (eqSubDerivTyComp d composedFitsEq composedCFitsEq)
  substDerivTyEqComp {sigma = sigma} (eqSubTyEqRule {sigma = sigma'} {tau = tau'} {A = A} {B = B} d fitsEq') fits cFits =
    let
      composedFitsEq = composeFitsEq fits fitsEq'
      composedCFitsEq = composeCompFitsEq fits cFits fitsEq'
    in
    subst
      (λ J -> Computable J)
      (cong₂ (typeEq [])
        (sym (subTyComp sigma sigma' A))
        (sym (subTyComp sigma tau' B)))
      (eqSubDerivTyEqComp d composedFitsEq composedCFitsEq)

  substDerivTmComp : {gamma : Ctx} {t : RawTerm} {A : RawType} {sigma : Subst}
    -> Derivable (hasTy gamma t A)
    -> FitsSubst [] gamma sigma
    -> CompFitsSubst gamma sigma
    -> Computable (hasTy [] (subTm sigma t) (subTy sigma A))
  substDerivTmCompESigma : {gamma : Ctx} {A B M : RawType} {d m : RawTerm} {sigma : Subst}
    -> Derivable (isType ((tySigma A B) ∷ gamma) M)
    -> Derivable (hasTy gamma d (tySigma A B))
    -> Derivable (hasTy (B ∷ A ∷ gamma) m (sigmaBranchTy M))
    -> FitsSubst [] gamma sigma
    -> CompFitsSubst gamma sigma
    -> Computable (hasTy [] (subTm sigma (tmElSigma d m)) (subTy sigma (subTy (singleSubst d) M)))
  substDerivTmCompESigma {gamma = gamma} {A = A} {B = B} {M = M} {d = d} {m = m} {sigma = sigma} dM dd dm fits cFits =
    let
      compdd = substDerivTmComp dd fits cFits
      compSigma = compTmToCompTy compdd
      dSigmaσ = compToDerivable compSigma
      tyInv = invertSigmaTy compSigma evalSigma
      compAσ = ClosedSigmaTyInv.sigmaTyCompHead tyInv
      compBσ = ClosedSigmaTyInv.sigmaTyCompFam tyInv
      dAσ = compToDerivable compAσ
      dBσ = compToDerivable compBσ
      compM =
        subst
          (λ T -> Computable (isType (subTy sigma (tySigma A B) ∷ []) T))
          (cong (λ rho -> subTy rho M) (liftSubstCompKeep sigma))
          (compTyOpen
            nonemptyNeNil
            (substTyRule dM (liftFitsOne fits dSigmaσ))
            (λ tau fits2 ->
              packClosedSubst fits2
                (subst
                  (λ T -> Computable (isType [] T))
                  (sym
                    (cong (λ rho -> subTy tau (subTy rho M)) (liftSubstCompKeep sigma)
                      ∙ subTyComp tau (liftSubst sigma) M))
                  (substDerivTyComp
                    dM
                    (composeOneBinder fits dSigmaσ fits2)
                    (composeOneBinderComp fits2 cFits))))
            (λ tau₁ tau₂ fitsEq2 ->
              packClosedEqSubst fitsEq2
                (subst
                  (λ J -> Computable J)
                  (sym
                    (cong₂ (typeEq [])
                      (cong (λ rho -> subTy tau₁ (subTy rho M)) (liftSubstCompKeep sigma)
                        ∙ subTyComp tau₁ (liftSubst sigma) M)
                      (cong (λ rho -> subTy tau₂ (subTy rho M)) (liftSubstCompKeep sigma)
                        ∙ subTyComp tau₂ (liftSubst sigma) M)))
                  (eqSubDerivTyComp
                    dM
                    (composeOneBinderEq fits dSigmaσ fitsEq2)
                    (composeOneBinderCompEq cFits fitsEq2)))))

      lifted1 : FitsSubst (subTy sigma A ∷ []) (A ∷ gamma) (liftSubst sigma)
      lifted1 =
        subst
          (λ rho -> FitsSubst (subTy sigma A ∷ []) (A ∷ gamma) rho)
          (liftSubstCompKeep sigma)
          (liftFitsOne fits dAσ)

      compdm =
        subst
          (λ J -> Computable J)
          (cong
            (hasTy (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ [])
              (subTm (liftSubst (liftSubst sigma)) m))
            (sigmaBranchTyLiftComp sigma M))
          (subst
            (λ J -> Computable J)
            (cong₂
              (hasTy (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []))
              (cong (λ rho -> subTm rho m) (liftSubstCompKeep (liftSubst sigma)))
              (cong (λ rho -> subTy rho (sigmaBranchTy M)) (liftSubstCompKeep (liftSubst sigma))))
            (compTmOpen
              nonemptyNeNil
              (substTmRule dm (liftFits lifted1 dBσ))
              (subst
                (λ T ->
                  Computable (isType (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) T))
                (sym (cong (λ rho -> subTy rho (sigmaBranchTy M)) (liftSubstCompKeep (liftSubst sigma))))
                (subst
                  (λ T ->
                    Computable (isType (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) T))
                  (cong (λ rho -> subTy rho (sigmaBranchTy M)) (liftSubstCompKeep (liftSubst sigma)))
                  (compTyOpen
                    nonemptyNeNil
                    (substTyRule (assocTy dm) (liftFits lifted1 dBσ))
                    (λ tau fits2 ->
                      packClosedSubst fits2
                        (subst
                          (λ T -> Computable (isType [] T))
                          (sym
                            (cong (λ rho -> subTy tau (subTy rho (sigmaBranchTy M)))
                              (liftSubstCompKeep (liftSubst sigma))
                              ∙ subTyComp tau (liftSubst (liftSubst sigma)) (sigmaBranchTy M)))
                          (substDerivTyComp
                            (assocTy dm)
                            (composeTwoBinders fits dAσ dBσ fits2)
                            (composeTwoBindersComp cFits fits2))))
                    (λ tau₁ tau₂ fitsEq2 ->
                      packClosedEqSubst fitsEq2
                        (subst
                          (λ J -> Computable J)
                          (sym
                            (cong₂ (typeEq [])
                              (cong (λ rho -> subTy tau₁ (subTy rho (sigmaBranchTy M)))
                                (liftSubstCompKeep (liftSubst sigma))
                                ∙ subTyComp tau₁ (liftSubst (liftSubst sigma)) (sigmaBranchTy M))
                              (cong (λ rho -> subTy tau₂ (subTy rho (sigmaBranchTy M)))
                                (liftSubstCompKeep (liftSubst sigma))
                                ∙ subTyComp tau₂ (liftSubst (liftSubst sigma)) (sigmaBranchTy M))))
                          (eqSubDerivTyComp
                            (assocTy dm)
                            (composeTwoBindersEq fits dAσ dBσ fitsEq2)
                            (composeTwoBindersCompEq cFits fitsEq2)))))))
              (λ tau fits2 ->
                packClosedSubst fits2
                  (subst
                    (λ J -> Computable J)
                    (sym
                      (cong₂ (hasTy [])
                        (cong (λ rho -> subTm tau (subTm rho m)) (liftSubstCompKeep (liftSubst sigma))
                          ∙ subTmComp tau (liftSubst (liftSubst sigma)) m)
                        (cong (λ rho -> subTy tau (subTy rho (sigmaBranchTy M)))
                          (liftSubstCompKeep (liftSubst sigma))
                          ∙ subTyComp tau (liftSubst (liftSubst sigma)) (sigmaBranchTy M))))
                    (substDerivTmComp
                      dm
                      (composeTwoBinders fits dAσ dBσ fits2)
                      (composeTwoBindersComp cFits fits2))))
              (λ tau₁ tau₂ fitsEq2 ->
                packClosedEqSubst fitsEq2
                  (subst
                    (λ J -> Computable J)
                    (sym
                      (cong₃ (termEq [])
                        (cong (λ rho -> subTm tau₁ (subTm rho m)) (liftSubstCompKeep (liftSubst sigma))
                          ∙ subTmComp tau₁ (liftSubst (liftSubst sigma)) m)
                        (cong (λ rho -> subTm tau₂ (subTm rho m)) (liftSubstCompKeep (liftSubst sigma))
                          ∙ subTmComp tau₂ (liftSubst (liftSubst sigma)) m)
                        (cong (λ rho -> subTy tau₁ (subTy rho (sigmaBranchTy M)))
                          (liftSubstCompKeep (liftSubst sigma))
                          ∙ subTyComp tau₁ (liftSubst (liftSubst sigma)) (sigmaBranchTy M))))
                    (eqSubDerivTmComp
                      dm
                      (composeTwoBindersEq fits dAσ dBσ fitsEq2)
                      (composeTwoBindersCompEq cFits fitsEq2))))))

      resultPath :
        hasTy [] (subTm sigma (tmElSigma d m)) (subTy sigma (subTy (singleSubst d) M))
          ≡
        hasTy []
          (tmElSigma (subTm sigma d) (subTm (liftSubst (liftSubst sigma)) m))
          (subTy (singleSubst (subTm sigma d)) (subTy (liftSubst sigma) M))
      resultPath =
        cong₂
          (hasTy [])
          refl
          (subTyComp sigma (singleSubst d) M
            ∙ cong (λ rho -> subTy rho M) (sym (singleSubstCompLift sigma d))
            ∙ sym (subTyComp (singleSubst (subTm sigma d)) (liftSubst sigma) M))
    in
    subst
      (λ J -> Computable J)
      (sym resultPath)
      (compTmEqLeft (compESigmaClosed compM (compReflTm compdd) (compReflTm compdm)))

  substDerivTmCompEQtr
    : {gamma : Ctx} {A L : RawType} {l p : RawTerm} {sigma : Subst}
    -> Derivable (isType ((tyQtr A) ∷ gamma) L)
    -> Derivable (hasTy gamma p (tyQtr A))
    -> Derivable (hasTy (A ∷ gamma) l (qtrBranchTy L))
    -> Derivable
         (termEq (wkTyBy 1 A ∷ A ∷ gamma)
           (wkTmBy 1 l)
           (renTm qtrSecondBranchRen l)
           (qtrCohTy L))
    -> FitsSubst [] gamma sigma
    -> CompFitsSubst gamma sigma
    -> Computable
         (hasTy [] (subTm sigma (tmElQtr l p))
           (subTy sigma (subTy (singleSubst p) L)))
  substDerivTmCompEQtr
    {gamma = gamma} {A = A} {L = L} {l = l} {p = p} {sigma = sigma}
    dL dp dl dcoh fits cFits =
    let
      compdp = substDerivTmComp dp fits cFits
      compQtrσ = compTmToCompTy compdp
      dQtrσ = compToDerivable compQtrσ
      tyInv = invertQtrTy compQtrσ evalQtr
      compAσ = ClosedQtrTyInv.qtrTyCompBase tyInv
      dAσ = compToDerivable compAσ
      dWkAσ =
        subst
          (λ T -> Derivable (isType (subTy sigma A ∷ []) T))
          (sym (wkTyLiftSubst sigma A))
          (weakenTy dAσ (wfCons wfNil dAσ))
      compL = substSccTy1 fits cFits dQtrσ dL

      compl =
        subst
          (λ T ->
            Computable
              (hasTy (subTy sigma A ∷ [])
                (subTm (liftSubst sigma) l)
                T))
          (qtrBranchTyLiftComp sigma L)
          (substSccTm1 fits cFits dAσ dl)

      compcoh =
        subst
          (λ J -> Computable J)
          (cong
            (λ T ->
              termEq (T ∷ subTy sigma A ∷ [])
                (subTm (liftSubst (liftSubst sigma)) (wkTmBy 1 l))
                (subTm (liftSubst (liftSubst sigma)) (renTm qtrSecondBranchRen l))
                (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
            (wkTyLiftSubst sigma A)
            ∙ cong
                (λ t ->
                  termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                    t
                    (subTm (liftSubst (liftSubst sigma)) (renTm qtrSecondBranchRen l))
                    (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
                (wkTmLiftSubst (liftSubst sigma) l)
            ∙ cong
                (λ u ->
                  termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                    (wkTmBy 1 (subTm (liftSubst sigma) l))
                    u
                    (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
                (qtrSecondBranchTmLiftComp sigma l)
            ∙ cong
                (λ T ->
                  termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                    (wkTmBy 1 (subTm (liftSubst sigma) l))
                    (renTm qtrSecondBranchRen (subTm (liftSubst sigma) l))
                    T)
                (qtrCohTyLiftComp sigma L))
          (substSccTmEq2 fits cFits dAσ dWkAσ dcoh)

      resultPath :
        hasTy []
          (subTm sigma (tmElQtr l p))
          (subTy sigma (subTy (singleSubst p) L))
          ≡
        hasTy []
          (tmElQtr (subTm (liftSubst sigma) l) (subTm sigma p))
          (subTy (singleSubst (subTm sigma p)) (subTy (liftSubst sigma) L))
      resultPath =
        cong₂
          (hasTy [])
          refl
          (subTyComp sigma (singleSubst p) L
            ∙ cong (λ rho -> subTy rho L) (sym (singleSubstCompLift sigma p))
            ∙ sym (subTyComp (singleSubst (subTm sigma p)) (liftSubst sigma) L))
    in
    subst
      (λ J -> Computable J)
      (sym resultPath)
      (compTmEqLeft
        (compEQtrClosed
          compL
          (compReflTm compdp)
          (compReflTm compl)
          compcoh
          compcoh))

  substDerivTmComp (varStar {delta = delta} {A = A} wf dA) fits cFits =
    lookupCompFits {delta = delta} {A = A} cFits
  substDerivTmComp (iTop wf) fits cFits = compITopClosed
  substDerivTmComp {sigma = sigma}
    (iSigma {a = a} {b = b} {A = A} {B = B} da db dSigma) fits cFits =
    let
      compa = substDerivTmComp da fits cFits
      compb =
        subst
          (λ T -> Computable (hasTy [] (subTm sigma b) T))
          (subTyComp sigma (singleSubst a) B
            ∙ cong (λ rho -> subTy rho B) (sym (singleSubstCompLift sigma a))
            ∙ sym (subTyComp (singleSubst (subTm sigma a)) (liftSubst sigma) B))
          (substDerivTmComp db fits cFits)
    in
    compISigmaClosed compa compb (substDerivTyComp dSigma fits cFits)
  substDerivTmComp (iEq da) fits cFits =
    compIEqClosed (substDerivTmComp da fits cFits)
  substDerivTmComp (iQtr da) fits cFits =
    compIQtrClosed (substDerivTmComp da fits cFits)
  substDerivTmComp (eSigma dM dd dm) fits cFits =
    substDerivTmCompESigma dM dd dm fits cFits
  substDerivTmComp (eQtr dL dp dl dcoh) fits cFits =
    substDerivTmCompEQtr dL dp dl dcoh fits cFits
  substDerivTmComp (conv d dAB) fits cFits =
    compConvTmClosed (substDerivTmComp d fits cFits) (substDerivTyEqComp dAB fits cFits)
  substDerivTmComp {sigma = sigma} (weakenTm {delta = delta} {t = t} {A = A} d wf) fits cFits =
    subst
      (λ J -> Computable J)
      (cong₂ (hasTy [])
        (sym (subTmWkBy sigma (length delta) t))
        (sym (subTyWkBy sigma (length delta) A)))
      (substDerivTmComp d (dropFits delta fits) (dropCompFits delta cFits))
  substDerivTmComp {sigma = sigma} (substTmRule {sigma = sigma'} {t = t} {A = A} d fits') fits cFits =
    let
      composedFits = composeFits fits fits'
      composedCFits = composeCompFits fits' fits cFits
    in
    subst
      (λ J -> Computable J)
      (cong₂ (hasTy [])
        (sym (subTmComp sigma sigma' t))
        (sym (subTyComp sigma sigma' A)))
      (substDerivTmComp d composedFits composedCFits)
  substDerivTmEqComp : {gamma : Ctx} {t u : RawTerm} {A : RawType} {sigma : Subst}
    -> Derivable (termEq gamma t u A)
    -> FitsSubst [] gamma sigma
    -> CompFitsSubst gamma sigma
    -> Computable (termEq [] (subTm sigma t) (subTm sigma u) (subTy sigma A))
  substDerivTmEqCompESigmaEq
    : {gamma : Ctx} {A B M : RawType} {d d' m m' : RawTerm} {sigma : Subst}
    -> Derivable (isType ((tySigma A B) ∷ gamma) M)
    -> Derivable (termEq gamma d d' (tySigma A B))
    -> Derivable (termEq (B ∷ A ∷ gamma) m m' (sigmaBranchTy M))
    -> FitsSubst [] gamma sigma
    -> CompFitsSubst gamma sigma
    -> Computable
         (termEq []
           (subTm sigma (tmElSigma d m))
           (subTm sigma (tmElSigma d' m'))
           (subTy sigma (subTy (singleSubst d) M)))
  substDerivTmEqCompESigmaEq
    {gamma = gamma} {A = A} {B = B} {M = M} {d = d} {d' = d'} {m = m} {m' = m'} {sigma = sigma}
    dM dd dm fits cFits =
    let
      compdd = substDerivTmEqComp dd fits cFits
      compSigma = compTmToCompTy (compTmEqLeft compdd)
      dSigmaσ = compToDerivable compSigma
      tyInv = invertSigmaTy compSigma evalSigma
      compAσ = ClosedSigmaTyInv.sigmaTyCompHead tyInv
      compBσ = ClosedSigmaTyInv.sigmaTyCompFam tyInv
      dAσ = compToDerivable compAσ
      dBσ = compToDerivable compBσ
      compM = substSccTy1 fits cFits dSigmaσ dM

      compdm =
        subst
          (λ J -> Computable J)
          (cong
            (termEq (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ [])
              (subTm (liftSubst (liftSubst sigma)) m)
              (subTm (liftSubst (liftSubst sigma)) m'))
            (sigmaBranchTyLiftComp sigma M))
          (substSccTmEq2 fits cFits dAσ dBσ dm)

      resultPath :
        termEq []
          (subTm sigma (tmElSigma d m))
          (subTm sigma (tmElSigma d' m'))
          (subTy sigma (subTy (singleSubst d) M))
          ≡
        termEq []
          (tmElSigma (subTm sigma d) (subTm (liftSubst (liftSubst sigma)) m))
          (tmElSigma (subTm sigma d') (subTm (liftSubst (liftSubst sigma)) m'))
          (subTy (singleSubst (subTm sigma d)) (subTy (liftSubst sigma) M))
      resultPath =
        cong₃
          (termEq [])
          refl
          refl
          (subTyComp sigma (singleSubst d) M
            ∙ cong (λ rho -> subTy rho M) (sym (singleSubstCompLift sigma d))
            ∙ sym (subTyComp (singleSubst (subTm sigma d)) (liftSubst sigma) M))
    in
    subst
      (λ J -> Computable J)
      (sym resultPath)
      (compESigmaClosed compM compdd compdm)

  substDerivTmEqCompEQtrEq
    : {gamma : Ctx} {A L : RawType} {l l' p p' : RawTerm} {sigma : Subst}
    -> Derivable (isType ((tyQtr A) ∷ gamma) L)
    -> Derivable (termEq gamma p p' (tyQtr A))
    -> Derivable (termEq (A ∷ gamma) l l' (qtrBranchTy L))
    -> Derivable
         (termEq (wkTyBy 1 A ∷ A ∷ gamma)
           (wkTmBy 1 l)
           (renTm qtrSecondBranchRen l)
           (qtrCohTy L))
    -> Derivable
         (termEq (wkTyBy 1 A ∷ A ∷ gamma)
           (wkTmBy 1 l')
           (renTm qtrSecondBranchRen l')
           (qtrCohTy L))
    -> FitsSubst [] gamma sigma
    -> CompFitsSubst gamma sigma
    -> Computable
         (termEq []
           (subTm sigma (tmElQtr l p))
           (subTm sigma (tmElQtr l' p'))
           (subTy sigma (subTy (singleSubst p) L)))
  substDerivTmEqCompEQtrEq
    {gamma = gamma} {A = A} {L = L} {l = l} {l' = l'} {p = p} {p' = p'} {sigma = sigma}
    dL dp dl dcoh dcoh' fits cFits =
    let
      compdp = substDerivTmEqComp dp fits cFits
      compQtrσ = compTmToCompTy (compTmEqLeft compdp)
      dQtrσ = compToDerivable compQtrσ
      tyInv = invertQtrTy compQtrσ evalQtr
      compAσ = ClosedQtrTyInv.qtrTyCompBase tyInv
      dAσ = compToDerivable compAσ
      dWkAσ =
        subst
          (λ T -> Derivable (isType (subTy sigma A ∷ []) T))
          (sym (wkTyLiftSubst sigma A))
          (weakenTy dAσ (wfCons wfNil dAσ))
      compL = substSccTy1 fits cFits dQtrσ dL

      compl =
        subst
          (λ T ->
            Computable
              (termEq (subTy sigma A ∷ [])
                (subTm (liftSubst sigma) l)
                (subTm (liftSubst sigma) l')
                T))
          (qtrBranchTyLiftComp sigma L)
          (substSccTmEq1 fits cFits dAσ dl)

      compcoh =
        subst
          (λ J -> Computable J)
          (cong
            (λ T ->
              termEq (T ∷ subTy sigma A ∷ [])
                (subTm (liftSubst (liftSubst sigma)) (wkTmBy 1 l))
                (subTm (liftSubst (liftSubst sigma)) (renTm qtrSecondBranchRen l))
                (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
            (wkTyLiftSubst sigma A)
            ∙ cong
                (λ t ->
                  termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                    t
                    (subTm (liftSubst (liftSubst sigma)) (renTm qtrSecondBranchRen l))
                    (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
                (wkTmLiftSubst (liftSubst sigma) l)
            ∙ cong
                (λ u ->
                  termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                    (wkTmBy 1 (subTm (liftSubst sigma) l))
                    u
                    (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
                (qtrSecondBranchTmLiftComp sigma l)
            ∙ cong
                (λ T ->
                  termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                    (wkTmBy 1 (subTm (liftSubst sigma) l))
                    (renTm qtrSecondBranchRen (subTm (liftSubst sigma) l))
                    T)
                (qtrCohTyLiftComp sigma L))
          (substSccTmEq2 fits cFits dAσ dWkAσ dcoh)

      compcoh' =
        subst
          (λ J -> Computable J)
          (cong
            (λ T ->
              termEq (T ∷ subTy sigma A ∷ [])
                (subTm (liftSubst (liftSubst sigma)) (wkTmBy 1 l'))
                (subTm (liftSubst (liftSubst sigma)) (renTm qtrSecondBranchRen l'))
                (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
            (wkTyLiftSubst sigma A)
            ∙ cong
                (λ t ->
                  termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                    t
                    (subTm (liftSubst (liftSubst sigma)) (renTm qtrSecondBranchRen l'))
                    (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
                (wkTmLiftSubst (liftSubst sigma) l')
            ∙ cong
                (λ u ->
                  termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                    (wkTmBy 1 (subTm (liftSubst sigma) l'))
                    u
                    (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
                (qtrSecondBranchTmLiftComp sigma l')
            ∙ cong
                (λ T ->
                  termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                    (wkTmBy 1 (subTm (liftSubst sigma) l'))
                    (renTm qtrSecondBranchRen (subTm (liftSubst sigma) l'))
                    T)
                (qtrCohTyLiftComp sigma L))
          (substSccTmEq2 fits cFits dAσ dWkAσ dcoh')

      resultPath :
        termEq []
          (subTm sigma (tmElQtr l p))
          (subTm sigma (tmElQtr l' p'))
          (subTy sigma (subTy (singleSubst p) L))
          ≡
        termEq []
          (tmElQtr (subTm (liftSubst sigma) l) (subTm sigma p))
          (tmElQtr (subTm (liftSubst sigma) l') (subTm sigma p'))
          (subTy (singleSubst (subTm sigma p)) (subTy (liftSubst sigma) L))
      resultPath =
        cong₃
          (termEq [])
          refl
          refl
          (subTyComp sigma (singleSubst p) L
            ∙ cong (λ rho -> subTy rho L) (sym (singleSubstCompLift sigma p))
            ∙ sym (subTyComp (singleSubst (subTm sigma p)) (liftSubst sigma) L))
    in
    subst
      (λ J -> Computable J)
      (sym resultPath)
      (compEQtrClosed compL compdp compl compcoh compcoh')

  substDerivTmEqCompCQtr
    : {gamma : Ctx} {A L : RawType} {a l : RawTerm} {sigma : Subst}
    -> Derivable (isType ((tyQtr A) ∷ gamma) L)
    -> Derivable (hasTy gamma a A)
    -> Derivable (hasTy (A ∷ gamma) l (qtrBranchTy L))
    -> Derivable
         (termEq (wkTyBy 1 A ∷ A ∷ gamma)
           (wkTmBy 1 l)
           (renTm qtrSecondBranchRen l)
           (qtrCohTy L))
    -> FitsSubst [] gamma sigma
    -> CompFitsSubst gamma sigma
    -> Computable
         (termEq []
           (subTm sigma (tmElQtr l (tmClass a)))
           (subTm sigma (subTm (qtrCompSub a) l))
           (subTy sigma (subTy (singleSubst (tmClass a)) L)))
  substDerivTmEqCompCQtr
    {gamma = gamma} {A = A} {L = L} {a = a} {l = l} {sigma = sigma}
    dL da dl dcoh fits cFits =
    let
      compa = substDerivTmComp da fits cFits
      compAσ = compTmToCompTy compa
      dAσ = compToDerivable compAσ
      dQtrσ = compToDerivable (compFQtrClosed compAσ)
      dWkAσ =
        subst
          (λ T -> Derivable (isType (subTy sigma A ∷ []) T))
          (sym (wkTyLiftSubst sigma A))
          (weakenTy dAσ (wfCons wfNil dAσ))
      compL = substSccTy1 fits cFits dQtrσ dL

      compl =
        subst
          (λ T ->
            Computable
              (hasTy (subTy sigma A ∷ [])
                (subTm (liftSubst sigma) l)
                T))
          (qtrBranchTyLiftComp sigma L)
          (substSccTm1 fits cFits dAσ dl)

      compcoh =
        subst
          (λ J -> Computable J)
          (cong
            (λ T ->
              termEq (T ∷ subTy sigma A ∷ [])
                (subTm (liftSubst (liftSubst sigma)) (wkTmBy 1 l))
                (subTm (liftSubst (liftSubst sigma)) (renTm qtrSecondBranchRen l))
                (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
            (wkTyLiftSubst sigma A)
            ∙ cong
                (λ t ->
                  termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                    t
                    (subTm (liftSubst (liftSubst sigma)) (renTm qtrSecondBranchRen l))
                    (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
                (wkTmLiftSubst (liftSubst sigma) l)
            ∙ cong
                (λ u ->
                  termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                    (wkTmBy 1 (subTm (liftSubst sigma) l))
                    u
                    (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
                (qtrSecondBranchTmLiftComp sigma l)
            ∙ cong
                (λ T ->
                  termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                    (wkTmBy 1 (subTm (liftSubst sigma) l))
                    (renTm qtrSecondBranchRen (subTm (liftSubst sigma) l))
                    T)
                (qtrCohTyLiftComp sigma L))
          (substSccTmEq2 fits cFits dAσ dWkAσ dcoh)

      resultPath :
        termEq []
          (subTm sigma (tmElQtr l (tmClass a)))
          (subTm sigma (subTm (qtrCompSub a) l))
          (subTy sigma (subTy (singleSubst (tmClass a)) L))
          ≡
        termEq []
          (tmElQtr (subTm (liftSubst sigma) l) (tmClass (subTm sigma a)))
          (subTm (qtrCompSub (subTm sigma a)) (subTm (liftSubst sigma) l))
          (subTy (singleSubst (tmClass (subTm sigma a))) (subTy (liftSubst sigma) L))
      resultPath =
        cong₃
          (termEq [])
          refl
          (subTmComp sigma (qtrCompSub a) l
            ∙ cong (λ rho -> subTm rho l) (qtrCompSubLiftComp sigma a)
            ∙ sym (subTmComp (qtrCompSub (subTm sigma a)) (liftSubst sigma) l))
          (subTyComp sigma (singleSubst (tmClass a)) L
            ∙ cong (λ rho -> subTy rho L) (sym (singleSubstCompLift sigma (tmClass a)))
            ∙ sym (subTyComp (singleSubst (tmClass (subTm sigma a))) (liftSubst sigma) L))
    in
    subst
      (λ J -> Computable J)
      (sym resultPath)
      (compCQtrClosed compL compa compl compcoh)

  substDerivTmEqComp (reflTm d) fits cFits =
    compReflTmClosed (substDerivTmComp d fits cFits)
  substDerivTmEqComp (symTm d) fits cFits =
    compSymTmClosed (substDerivTmEqComp d fits cFits)
  substDerivTmEqComp (transTm d₁ d₂) fits cFits =
    compTransTmClosed (substDerivTmEqComp d₁ fits cFits) (substDerivTmEqComp d₂ fits cFits)
  substDerivTmEqComp (convEq d dAB) fits cFits =
    compConvTmEqClosed (substDerivTmEqComp d fits cFits) (substDerivTyEqComp dAB fits cFits)
  substDerivTmEqComp (cTop d) fits cFits =
    compCTopClosed (substDerivTmComp d fits cFits)
  substDerivTmEqComp {sigma = sigma}
    (iSigmaEq {a = a} {b = b} {d = d} {A = A} {B = B} dac dbd dA dB) fits cFits =
    let
      compac = substDerivTmEqComp dac fits cFits
      compbdRaw = substDerivTmEqComp dbd fits cFits
      compA = substDerivTyComp dA fits cFits
      dAσ = compToDerivable compA
      compB = substSccTy1 fits cFits dAσ dB
      compa = compTmEqLeft compac
      compcA = compTmEqRightClosed compac
      compbd =
        subst
          (λ T -> Computable (termEq [] (subTm sigma b) (subTm sigma d) T))
          (subTyComp sigma (singleSubst a) B
            ∙ cong (λ rho -> subTy rho B) (sym (singleSubstCompLift sigma a))
            ∙ sym (subTyComp (singleSubst (subTm sigma a)) (liftSubst sigma) B))
          compbdRaw
      compb = compTmEqLeft compbd
      compdA = compTmEqRightClosed compbd
      compd =
        compConvTmClosed compdA (compSingleEqSubstTyClosed compB compac)
      compPairLeft = compISigmaClosed compa compb (compFSigmaClosed compA compB)
      compPairRight = compISigmaClosed compcA compd (compFSigmaClosed compA compB)
    in
    compTmEqClosedSigma
      (iSigmaEq (compToDerivable compac) (compToDerivable compbd) dAσ (compToDerivable compB))
      compPairLeft
      compPairRight
      evalSigma
      evalPair
      evalPair
      compac
      compbd
  substDerivTmEqComp (eSigmaEq dM dd dm) fits cFits =
    substDerivTmEqCompESigmaEq dM dd dm fits cFits
  substDerivTmEqComp (eQtrEq dL dp dl dcoh dcoh') fits cFits =
    substDerivTmEqCompEQtrEq dL dp dl dcoh dcoh' fits cFits
  substDerivTmEqComp {gamma = gamma} {sigma = sigma}
    (cSigma {A = A} {B = B} {M = M} {b = b} {c = c} {m = m} dM db dc dm) fits cFits =
    let
      compb = substDerivTmComp db fits cFits
      sigmaTy = ctxSuffixTy {delta = []} {gamma = gamma} {A = tySigma A B} (derivToCtxWF dM)
      compSigma = substDerivTyComp sigmaTy fits cFits
      dSigmaσ = compToDerivable compSigma
      tyInv = invertSigmaTy compSigma evalSigma
      compAσ = ClosedSigmaTyInv.sigmaTyCompHead tyInv
      compBσ = ClosedSigmaTyInv.sigmaTyCompFam tyInv
      dAσ = compToDerivable compAσ
      dBσ = compToDerivable compBσ
      compM = substSccTy1 fits cFits dSigmaσ dM

      compdm =
        subst
          (λ J -> Computable J)
          (cong
            (hasTy (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ [])
              (subTm (liftSubst (liftSubst sigma)) m))
            (sigmaBranchTyLiftComp sigma M))
          (substSccTm2 fits cFits dAσ dBσ dm)

      compcRaw = substDerivTmComp dc fits cFits
      compc =
        subst
          (λ T -> Computable (hasTy [] (subTm sigma c) T))
          (subTyComp sigma (singleSubst b) B
            ∙ cong (λ rho -> subTy rho B) (sym (singleSubstCompLift sigma b))
            ∙ sym (subTyComp (singleSubst (subTm sigma b)) (liftSubst sigma) B))
          compcRaw

      resultPath :
        termEq []
          (subTm sigma (tmElSigma (tmPair b c) m))
          (subTm sigma (subTm (sigmaCompSub b c) m))
          (subTy sigma (subTy (singleSubst (tmPair b c)) M))
          ≡
        termEq []
          (tmElSigma (tmPair (subTm sigma b) (subTm sigma c))
            (subTm (liftSubst (liftSubst sigma)) m))
          (subTm (sigmaCompSub (subTm sigma b) (subTm sigma c))
            (subTm (liftSubst (liftSubst sigma)) m))
          (subTy (singleSubst (tmPair (subTm sigma b) (subTm sigma c)))
            (subTy (liftSubst sigma) M))
      resultPath =
        cong₃
          (termEq [])
          refl
          (subTmComp sigma (sigmaCompSub b c) m
            ∙ cong (λ rho -> subTm rho m) (sigmaCompSubLiftComp sigma b c)
            ∙ sym (subTmComp (sigmaCompSub (subTm sigma b) (subTm sigma c))
                (liftSubst (liftSubst sigma)) m))
          (subTyComp sigma (singleSubst (tmPair b c)) M
            ∙ cong (λ rho -> subTy rho M) (sym (singleSubstCompLift sigma (tmPair b c)))
            ∙ sym (subTyComp (singleSubst (tmPair (subTm sigma b) (subTm sigma c)))
                (liftSubst sigma) M))
    in
    subst
      (λ J -> Computable J)
      (sym resultPath)
      (compCSigmaClosed compM compb compc compdm)
  substDerivTmEqComp (iEqEq d) fits cFits =
    compReflTm (compIEqClosed (compTmEqLeft (substDerivTmEqComp d fits cFits)))
  substDerivTmEqComp (eEqStar dp dA da db) fits cFits =
    compEEqClosed (substDerivTmComp dp fits cFits)
  substDerivTmEqComp (cEq dp dA da db) fits cFits =
    compCEqClosed (substDerivTmComp dp fits cFits)
  substDerivTmEqComp (iQtrEq da db) fits cFits =
    compIQtrEqClosed (substDerivTmComp da fits cFits) (substDerivTmComp db fits cFits)
  substDerivTmEqComp (cQtr dL da dl dcoh) fits cFits =
    substDerivTmEqCompCQtr dL da dl dcoh fits cFits
  substDerivTmEqComp {sigma = sigma} (weakenTmEq {delta = delta} {t = t} {u = u} {A = A} d wf) fits cFits =
    subst
      (λ J -> Computable J)
      (cong₃ (termEq [])
        (sym (subTmWkBy sigma (length delta) t))
        (sym (subTmWkBy sigma (length delta) u))
        (sym (subTyWkBy sigma (length delta) A)))
      (substDerivTmEqComp d (dropFits delta fits) (dropCompFits delta cFits))
  substDerivTmEqComp {sigma = sigma} (substTmEqRule {sigma = sigma'} {t = t} {u = u} {A = A} d fits') fits cFits =
    let
      composedFits = composeFits fits fits'
      composedCFits = composeCompFits fits' fits cFits
    in
    subst
      (λ J -> Computable J)
      (cong₃ (termEq [])
        (sym (subTmComp sigma sigma' t))
        (sym (subTmComp sigma sigma' u))
        (sym (subTyComp sigma sigma' A)))
      (substDerivTmEqComp d composedFits composedCFits)
  substDerivTmEqComp {sigma = sigma}
    (eqSubTmRule {sigma = sigma'} {tau = tau'} {t = t} {A = A} d fitsEq') fits cFits =
    let
      composedFitsEq = composeFitsEq fits fitsEq'
      composedCFitsEq = composeCompFitsEq fits cFits fitsEq'
    in
    subst
      (λ J -> Computable J)
      (cong₃ (termEq [])
        (sym (subTmComp sigma sigma' t))
        (sym (subTmComp sigma tau' t))
        (sym (subTyComp sigma sigma' A)))
      (eqSubDerivTmComp d composedFitsEq composedCFitsEq)
  substDerivTmEqComp {sigma = sigma}
    (eqSubTmEqRule {sigma = sigma'} {tau = tau'} {t = t} {u = u} {A = A} d fitsEq') fits cFits =
    let
      composedFitsEq = composeFitsEq fits fitsEq'
      composedCFitsEq = composeCompFitsEq fits cFits fitsEq'
    in
    subst
      (λ J -> Computable J)
      (cong₃ (termEq [])
        (sym (subTmComp sigma sigma' t))
        (sym (subTmComp sigma tau' u))
        (sym (subTyComp sigma sigma' A)))
      (eqSubDerivTmEqComp d composedFitsEq composedCFitsEq)
  eqSubDerivTyComp : {gamma : Ctx} {A : RawType} {sigma tau : Subst}
    -> Derivable (isType gamma A)
    -> FitsEqSubst [] gamma sigma tau
    -> CompFitsEqSubst gamma sigma tau
    -> Computable (typeEq [] (subTy sigma A) (subTy tau A))
  eqSubDerivTyComp (fTop wf) fitsEq cFitsEq = compReflTy compFTopClosed
  eqSubDerivTyComp {sigma = sigma} {tau = tau}
    (fSigma {A = A} {B = B} dA dB) fitsEq cFitsEq =
    let
      compAA' = eqSubDerivTyComp dA fitsEq cFitsEq
      compA = compTyEqLeft compAA'
      compA' = compTyEqRight compAA'
      dAσ = compToDerivable compA
      compBD = eqSubSccTy1 fitsEq cFitsEq dAσ dB
      compSigmaA = compFSigmaClosed compA (compTyEqLeft compBD)
      compSigmaA' = compFSigmaClosed compA' (compTransportFamilyTy compAA' (compTyEqRight compBD))
    in
    compTyEqClosedSigma
      (fSigmaEq (compToDerivable compAA') (compToDerivable compBD))
      compSigmaA
      compSigmaA'
      evalSigma
      evalSigma
      compAA'
      compBD
  eqSubDerivTyComp (fEq dA da db) fitsEq cFitsEq =
    let
      compAA' = eqSubDerivTyComp dA fitsEq cFitsEq
      compac = eqSubDerivTmComp da fitsEq cFitsEq
      compbd = eqSubDerivTmComp db fitsEq cFitsEq
      compA = compTyEqLeft compAA'
      compA' = compTyEqRight compAA'
      compa = compTmEqLeft compac
      compb = compTmEqLeft compbd
      compcA = compTmEqRightClosed compac
      compdA = compTmEqRightClosed compbd
      compc = compConvTmClosed compcA compAA'
      compd = compConvTmClosed compdA compAA'
      compEqA = compFEqClosed compA compa compb
      compEqA' = compFEqClosed compA' compc compd
    in
    compTyEqClosedEq
      (fEqEq (compToDerivable compAA') (compToDerivable compac) (compToDerivable compbd))
      compEqA
      compEqA'
      evalEq
      evalEq
      compAA'
      compac
      compbd
  eqSubDerivTyComp (fQtr dA) fitsEq cFitsEq =
    let
      compAA' = eqSubDerivTyComp dA fitsEq cFitsEq
    in
    compTyEqClosedQtr
      (fQtrEq (compToDerivable compAA'))
      (compFQtrClosed (compTyEqLeft compAA'))
      (compFQtrClosed (compTyEqRight compAA'))
      evalQtr
      evalQtr
      compAA'
  eqSubDerivTyComp {sigma = sigma} {tau = tau}
    (weakenTy {delta = delta} {A = A} d wf) fitsEq cFitsEq =
    subst
      (λ J -> Computable J)
      (cong₂ (typeEq [])
        (sym (subTyWkBy sigma (length delta) A))
        (sym (subTyWkBy tau (length delta) A)))
      (eqSubDerivTyComp d (dropFitsEq delta fitsEq) (dropCompFitsEq delta cFitsEq))
  eqSubDerivTyComp {sigma = sigma} {tau = tau}
    (substTyRule {sigma = sigma'} {A = A} d fits') fitsEq cFitsEq =
    let
      composedFitsEq = composeEqFits fitsEq fits'
      composedCFitsEq = composeCompEqFits fitsEq cFitsEq fits'
    in
    subst
      (λ J -> Computable J)
      (cong₂ (typeEq [])
        (sym (subTyComp sigma sigma' A))
        (sym (subTyComp tau sigma' A)))
      (eqSubDerivTyComp d composedFitsEq composedCFitsEq)

  eqSubDerivTyEqComp : {gamma : Ctx} {A B : RawType} {sigma tau : Subst}
    -> Derivable (typeEq gamma A B)
    -> FitsEqSubst [] gamma sigma tau
    -> CompFitsEqSubst gamma sigma tau
    -> Computable (typeEq [] (subTy sigma A) (subTy tau B))
  eqSubDerivTyEqComp (reflTy d) fitsEq cFitsEq =
    eqSubDerivTyComp d fitsEq cFitsEq
  eqSubDerivTyEqComp (symTy d) fitsEq cFitsEq =
    let
      sigmaCFits = compFitsEqLeft cFitsEq
      sigmaFits = compFitsToFits sigmaCFits
    in
    compTransTyClosed
      (compSymTyClosed (substDerivTyEqComp d sigmaFits sigmaCFits))
      (eqSubDerivTyComp (assocTyLeft d) fitsEq cFitsEq)
  eqSubDerivTyEqComp (transTy d₁ d₂) fitsEq cFitsEq =
    let
      sigmaCFits = compFitsEqLeft cFitsEq
      sigmaFits = compFitsToFits sigmaCFits
    in
    compTransTyClosed
      (substDerivTyEqComp d₁ sigmaFits sigmaCFits)
      (eqSubDerivTyEqComp d₂ fitsEq cFitsEq)
  eqSubDerivTyEqComp {sigma = sigma} {tau = tau}
    (fSigmaEq {A = A} {B = B} {D = D} dAC dBD) fitsEq cFitsEq =
    let
      compAC = eqSubDerivTyEqComp dAC fitsEq cFitsEq
      compA = compTyEqLeft compAC
      compC = compTyEqRight compAC
      dAσ = compToDerivable compA
      compBD = eqSubSccTyEq1 fitsEq cFitsEq dAσ dBD
      compSigmaA = compFSigmaClosed compA (compTyEqLeft compBD)
      compSigmaC = compFSigmaClosed compC (compTransportFamilyTy compAC (compTyEqRight compBD))
    in
    compTyEqClosedSigma
      (fSigmaEq (compToDerivable compAC) (compToDerivable compBD))
      compSigmaA
      compSigmaC
      evalSigma
      evalSigma
      compAC
      compBD
  eqSubDerivTyEqComp {sigma = sigma} {tau = tau}
    (weakenTyEq {delta = delta} {A = A} {B = B} d wf) fitsEq cFitsEq =
    subst
      (λ J -> Computable J)
      (cong₂ (typeEq [])
        (sym (subTyWkBy sigma (length delta) A))
        (sym (subTyWkBy tau (length delta) B)))
      (eqSubDerivTyEqComp d (dropFitsEq delta fitsEq) (dropCompFitsEq delta cFitsEq))
  eqSubDerivTyEqComp {sigma = sigma} {tau = tau}
    (substTyEqRule {sigma = sigma'} {A = A} {B = B} d fits') fitsEq cFitsEq =
    let
      composedFitsEq = composeEqFits fitsEq fits'
      composedCFitsEq = composeCompEqFits fitsEq cFitsEq fits'
    in
    subst
      (λ J -> Computable J)
      (cong₂ (typeEq [])
        (sym (subTyComp sigma sigma' A))
        (sym (subTyComp tau sigma' B)))
      (eqSubDerivTyEqComp d composedFitsEq composedCFitsEq)
  eqSubDerivTyEqComp {sigma = sigma} {tau = tau}
    (eqSubTyRule {sigma = sigma'} {tau = tau'} {A = A} d fitsEq') fitsEq cFitsEq =
    let
      composedFitsEq = composeEqFitsEq fitsEq fitsEq'
      composedCFitsEq = composeCompEqFitsEq fitsEq cFitsEq fitsEq'
    in
    subst
      (λ J -> Computable J)
      (cong₂ (typeEq [])
        (sym (subTyComp sigma sigma' A))
        (sym (subTyComp tau tau' A)))
      (eqSubDerivTyComp d composedFitsEq composedCFitsEq)
  eqSubDerivTyEqComp {sigma = sigma} {tau = tau}
    (eqSubTyEqRule {sigma = sigma'} {tau = tau'} {A = A} {B = B} d fitsEq') fitsEq cFitsEq =
    let
      composedFitsEq = composeEqFitsEq fitsEq fitsEq'
      composedCFitsEq = composeCompEqFitsEq fitsEq cFitsEq fitsEq'
    in
    subst
      (λ J -> Computable J)
      (cong₂ (typeEq [])
        (sym (subTyComp sigma sigma' A))
        (sym (subTyComp tau tau' B)))
      (eqSubDerivTyEqComp d composedFitsEq composedCFitsEq)
  eqSubDerivTyEqComp (fEqEq dAC dac dbd) fitsEq cFitsEq =
    let
      compAC = eqSubDerivTyEqComp dAC fitsEq cFitsEq
      compac = eqSubDerivTmEqComp dac fitsEq cFitsEq
      compbd = eqSubDerivTmEqComp dbd fitsEq cFitsEq
      compA = compTyEqLeft compAC
      compC = compTyEqRight compAC
      compa = compTmEqLeft compac
      compb = compTmEqLeft compbd
      compcA = compTmEqRightClosed compac
      compdA = compTmEqRightClosed compbd
      compc = compConvTmClosed compcA compAC
      compd = compConvTmClosed compdA compAC
      compEqA = compFEqClosed compA compa compb
      compEqC = compFEqClosed compC compc compd
    in
    compTyEqClosedEq
      (fEqEq (compToDerivable compAC) (compToDerivable compac) (compToDerivable compbd))
      compEqA
      compEqC
      evalEq
      evalEq
      compAC
      compac
      compbd
  eqSubDerivTyEqComp (fQtrEq dAB) fitsEq cFitsEq =
    let
      compAB = eqSubDerivTyEqComp dAB fitsEq cFitsEq
    in
    compTyEqClosedQtr
      (fQtrEq (compToDerivable compAB))
      (compFQtrClosed (compTyEqLeft compAB))
      (compFQtrClosed (compTyEqRight compAB))
      evalQtr
      evalQtr
      compAB

  eqSubDerivTmCompEQtr
    : {gamma : Ctx} {A L : RawType} {l p : RawTerm} {sigma tau : Subst}
    -> Derivable (isType ((tyQtr A) ∷ gamma) L)
    -> Derivable (hasTy gamma p (tyQtr A))
    -> Derivable (hasTy (A ∷ gamma) l (qtrBranchTy L))
    -> Derivable
         (termEq (wkTyBy 1 A ∷ A ∷ gamma)
           (wkTmBy 1 l)
           (renTm qtrSecondBranchRen l)
           (qtrCohTy L))
    -> FitsEqSubst [] gamma sigma tau
    -> CompFitsEqSubst gamma sigma tau
    -> Computable
         (termEq []
           (subTm sigma (tmElQtr l p))
           (subTm tau (tmElQtr l p))
           (subTy sigma (subTy (singleSubst p) L)))
  eqSubDerivTmCompEQtr
    {gamma = gamma} {A = A} {L = L} {l = l} {p = p} {sigma = sigma} {tau = tau}
    dL dp dl dcoh fitsEq cFitsEq =
    let
      sigmaCFits = compFitsEqLeft cFitsEq
      sigmaFits = compFitsToFits sigmaCFits
      compp = eqSubDerivTmComp dp fitsEq cFitsEq
      compQtrσ = compTmToCompTy (compTmEqLeft compp)
      dQtrσ = compToDerivable compQtrσ
      tyInv = invertQtrTy compQtrσ evalQtr
      compAσ = ClosedQtrTyInv.qtrTyCompBase tyInv
      dAσ = compToDerivable compAσ
      dWkBaseσ = weakenTy dAσ (wfCons wfNil dAσ)
      dWkAσ =
        subst
          (λ T -> Derivable (isType (subTy sigma A ∷ []) T))
          (sym (wkTyLiftSubst sigma A))
          dWkBaseσ
      wkCtxWF : CtxWF (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
      wkCtxWF = wfCons (wfCons wfNil dAσ) dWkBaseσ
      compL = substSccTy1 sigmaFits sigmaCFits dQtrσ dL

      branchEq =
        subst
          (λ T ->
            Computable
              (termEq (subTy sigma A ∷ [])
                (subTm (liftSubst sigma) l)
                (subTm (liftSubst tau) l)
                T))
          (qtrBranchTyLiftComp sigma L)
          (eqSubSccTm1 fitsEq cFitsEq dAσ dl)

      branchEqWk =
        subst
          (λ J -> Computable J)
          (cong
            (λ T ->
              termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                (wkTmBy 1 (subTm (liftSubst sigma) l))
                (wkTmBy 1 (subTm (liftSubst tau) l))
                T)
            (qtrBranchTyWk (subTy (liftSubst sigma) L)))
          (weakenOneOpenTmEq branchEq wkCtxWF)

      cohσ =
        subst
          (λ J -> Computable J)
          (cong
            (λ T ->
              termEq (T ∷ subTy sigma A ∷ [])
                (subTm (liftSubst (liftSubst sigma)) (wkTmBy 1 l))
                (subTm (liftSubst (liftSubst sigma)) (renTm qtrSecondBranchRen l))
                (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
            (wkTyLiftSubst sigma A)
            ∙ cong
                (λ t ->
                  termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                    t
                    (subTm (liftSubst (liftSubst sigma)) (renTm qtrSecondBranchRen l))
                    (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
                (wkTmLiftSubst (liftSubst sigma) l)
            ∙ cong
                (λ u ->
                  termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                    (wkTmBy 1 (subTm (liftSubst sigma) l))
                    u
                    (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
                (qtrSecondBranchTmLiftComp sigma l)
            ∙ cong
                (λ T ->
                  termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                    (wkTmBy 1 (subTm (liftSubst sigma) l))
                    (renTm qtrSecondBranchRen (subTm (liftSubst sigma) l))
                    T)
                (qtrCohTyLiftComp sigma L))
          (substSccTmEq2 sigmaFits sigmaCFits dAσ dWkAσ dcoh)

      cohστ =
        subst
          (λ J -> Computable J)
          (cong
            (λ T ->
              termEq (T ∷ subTy sigma A ∷ [])
                (subTm (liftSubst (liftSubst sigma)) (wkTmBy 1 l))
                (subTm (liftSubst (liftSubst tau)) (renTm qtrSecondBranchRen l))
                (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
            (wkTyLiftSubst sigma A)
            ∙ cong
                (λ t ->
                  termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                    t
                    (subTm (liftSubst (liftSubst tau)) (renTm qtrSecondBranchRen l))
                    (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
                (wkTmLiftSubst (liftSubst sigma) l)
            ∙ cong
                (λ u ->
                  termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                    (wkTmBy 1 (subTm (liftSubst sigma) l))
                    u
                    (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
                (qtrSecondBranchTmLiftComp tau l)
            ∙ cong
                (λ T ->
                  termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                    (wkTmBy 1 (subTm (liftSubst sigma) l))
                    (renTm qtrSecondBranchRen (subTm (liftSubst tau) l))
                    T)
                (qtrCohTyLiftComp sigma L))
          (eqSubSccTmEq2 fitsEq cFitsEq dAσ dWkAσ dcoh)

      cohτ = compTransTm (compSymTm branchEqWk) cohστ

      resultPath :
        termEq []
          (subTm sigma (tmElQtr l p))
          (subTm tau (tmElQtr l p))
          (subTy sigma (subTy (singleSubst p) L))
          ≡
        termEq []
          (tmElQtr (subTm (liftSubst sigma) l) (subTm sigma p))
          (tmElQtr (subTm (liftSubst tau) l) (subTm tau p))
          (subTy (singleSubst (subTm sigma p)) (subTy (liftSubst sigma) L))
      resultPath =
        cong₃
          (termEq [])
          refl
          refl
          (subTyComp sigma (singleSubst p) L
            ∙ cong (λ rho -> subTy rho L) (sym (singleSubstCompLift sigma p))
            ∙ sym (subTyComp (singleSubst (subTm sigma p)) (liftSubst sigma) L))
    in
    subst
      (λ J -> Computable J)
      (sym resultPath)
      (compEQtrClosed compL compp branchEq cohσ cohτ)

  eqSubDerivTmEqCompEQtrEq
    : {gamma : Ctx} {A L : RawType} {l l' p p' : RawTerm} {sigma tau : Subst}
    -> Derivable (isType ((tyQtr A) ∷ gamma) L)
    -> Derivable (termEq gamma p p' (tyQtr A))
    -> Derivable (termEq (A ∷ gamma) l l' (qtrBranchTy L))
    -> Derivable
         (termEq (wkTyBy 1 A ∷ A ∷ gamma)
           (wkTmBy 1 l)
           (renTm qtrSecondBranchRen l)
           (qtrCohTy L))
    -> Derivable
         (termEq (wkTyBy 1 A ∷ A ∷ gamma)
           (wkTmBy 1 l')
           (renTm qtrSecondBranchRen l')
           (qtrCohTy L))
    -> FitsEqSubst [] gamma sigma tau
    -> CompFitsEqSubst gamma sigma tau
    -> Computable
         (termEq []
           (subTm sigma (tmElQtr l p))
           (subTm tau (tmElQtr l' p'))
           (subTy sigma (subTy (singleSubst p) L)))
  eqSubDerivTmEqCompEQtrEq
    {gamma = gamma} {A = A} {L = L} {l = l} {l' = l'} {p = p} {p' = p'} {sigma = sigma} {tau = tau}
    dL dp dl dcoh dcoh' fitsEq cFitsEq =
    let
      sigmaCFits = compFitsEqLeft cFitsEq
      sigmaFits = compFitsToFits sigmaCFits
      compp = eqSubDerivTmEqComp dp fitsEq cFitsEq
      compQtrσ = compTmToCompTy (compTmEqLeft compp)
      dQtrσ = compToDerivable compQtrσ
      tyInv = invertQtrTy compQtrσ evalQtr
      compAσ = ClosedQtrTyInv.qtrTyCompBase tyInv
      dAσ = compToDerivable compAσ
      dWkBaseσ = weakenTy dAσ (wfCons wfNil dAσ)
      dWkAσ =
        subst
          (λ T -> Derivable (isType (subTy sigma A ∷ []) T))
          (sym (wkTyLiftSubst sigma A))
          dWkBaseσ
      wkCtxWF : CtxWF (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
      wkCtxWF = wfCons (wfCons wfNil dAσ) dWkBaseσ
      compL = substSccTy1 sigmaFits sigmaCFits dQtrσ dL

      branchEq =
        subst
          (λ T ->
            Computable
              (termEq (subTy sigma A ∷ [])
                (subTm (liftSubst sigma) l)
                (subTm (liftSubst tau) l')
                T))
          (qtrBranchTyLiftComp sigma L)
          (eqSubSccTmEq1 fitsEq cFitsEq dAσ dl)

      branchEqRight =
        subst
          (λ T ->
            Computable
              (termEq (subTy sigma A ∷ [])
                (subTm (liftSubst sigma) l')
                (subTm (liftSubst tau) l')
                T))
          (qtrBranchTyLiftComp sigma L)
          (eqSubSccTm1 fitsEq cFitsEq dAσ (assocTmRight dl))

      branchEqRightWk =
        subst
          (λ J -> Computable J)
          (cong
            (λ T ->
              termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                (wkTmBy 1 (subTm (liftSubst sigma) l'))
                (wkTmBy 1 (subTm (liftSubst tau) l'))
                T)
            (qtrBranchTyWk (subTy (liftSubst sigma) L)))
          (weakenOneOpenTmEq branchEqRight wkCtxWF)

      cohσ =
        subst
          (λ J -> Computable J)
          (cong
            (λ T ->
              termEq (T ∷ subTy sigma A ∷ [])
                (subTm (liftSubst (liftSubst sigma)) (wkTmBy 1 l))
                (subTm (liftSubst (liftSubst sigma)) (renTm qtrSecondBranchRen l))
                (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
            (wkTyLiftSubst sigma A)
            ∙ cong
                (λ t ->
                  termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                    t
                    (subTm (liftSubst (liftSubst sigma)) (renTm qtrSecondBranchRen l))
                    (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
                (wkTmLiftSubst (liftSubst sigma) l)
            ∙ cong
                (λ u ->
                  termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                    (wkTmBy 1 (subTm (liftSubst sigma) l))
                    u
                    (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
                (qtrSecondBranchTmLiftComp sigma l)
            ∙ cong
                (λ T ->
                  termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                    (wkTmBy 1 (subTm (liftSubst sigma) l))
                    (renTm qtrSecondBranchRen (subTm (liftSubst sigma) l))
                    T)
                (qtrCohTyLiftComp sigma L))
          (substSccTmEq2 sigmaFits sigmaCFits dAσ dWkAσ dcoh)

      coh'στ =
        subst
          (λ J -> Computable J)
          (cong
            (λ T ->
              termEq (T ∷ subTy sigma A ∷ [])
                (subTm (liftSubst (liftSubst sigma)) (wkTmBy 1 l'))
                (subTm (liftSubst (liftSubst tau)) (renTm qtrSecondBranchRen l'))
                (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
            (wkTyLiftSubst sigma A)
            ∙ cong
                (λ t ->
                  termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                    t
                    (subTm (liftSubst (liftSubst tau)) (renTm qtrSecondBranchRen l'))
                    (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
                (wkTmLiftSubst (liftSubst sigma) l')
            ∙ cong
                (λ u ->
                  termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                    (wkTmBy 1 (subTm (liftSubst sigma) l'))
                    u
                    (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
                (qtrSecondBranchTmLiftComp tau l')
            ∙ cong
                (λ T ->
                  termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                    (wkTmBy 1 (subTm (liftSubst sigma) l'))
                    (renTm qtrSecondBranchRen (subTm (liftSubst tau) l'))
                    T)
                (qtrCohTyLiftComp sigma L))
          (eqSubSccTmEq2 fitsEq cFitsEq dAσ dWkAσ dcoh')

      cohτ = compTransTm (compSymTm branchEqRightWk) coh'στ

      resultPath :
        termEq []
          (subTm sigma (tmElQtr l p))
          (subTm tau (tmElQtr l' p'))
          (subTy sigma (subTy (singleSubst p) L))
          ≡
        termEq []
          (tmElQtr (subTm (liftSubst sigma) l) (subTm sigma p))
          (tmElQtr (subTm (liftSubst tau) l') (subTm tau p'))
          (subTy (singleSubst (subTm sigma p)) (subTy (liftSubst sigma) L))
      resultPath =
        cong₃
          (termEq [])
          refl
          refl
          (subTyComp sigma (singleSubst p) L
            ∙ cong (λ rho -> subTy rho L) (sym (singleSubstCompLift sigma p))
            ∙ sym (subTyComp (singleSubst (subTm sigma p)) (liftSubst sigma) L))
    in
    subst
      (λ J -> Computable J)
      (sym resultPath)
      (compEQtrClosed compL compp branchEq cohσ cohτ)

  eqSubDerivTmEqCompCQtr
    : {gamma : Ctx} {A L : RawType} {a l : RawTerm} {sigma tau : Subst}
    -> Derivable (isType ((tyQtr A) ∷ gamma) L)
    -> Derivable (hasTy gamma a A)
    -> Derivable (hasTy (A ∷ gamma) l (qtrBranchTy L))
    -> Derivable
         (termEq (wkTyBy 1 A ∷ A ∷ gamma)
           (wkTmBy 1 l)
           (renTm qtrSecondBranchRen l)
           (qtrCohTy L))
    -> FitsEqSubst [] gamma sigma tau
    -> CompFitsEqSubst gamma sigma tau
    -> Computable
         (termEq []
           (subTm sigma (tmElQtr l (tmClass a)))
           (subTm tau (subTm (qtrCompSub a) l))
           (subTy sigma (subTy (singleSubst (tmClass a)) L)))
  eqSubDerivTmEqCompCQtr
    {gamma = gamma} {A = A} {L = L} {a = a} {l = l} {sigma = sigma} {tau = tau}
    dL da dl dcoh fitsEq cFitsEq =
    let
      sigmaCFits = compFitsEqLeft cFitsEq
      sigmaFits = compFitsToFits sigmaCFits
      compa = eqSubDerivTmComp da fitsEq cFitsEq
      compaσ = compTmEqLeft compa
      compAσ = compTmToCompTy compaσ
      dAσ = compToDerivable compAσ
      dQtrσ = compToDerivable (compFQtrClosed compAσ)
      dWkBaseσ = weakenTy dAσ (wfCons wfNil dAσ)
      dWkAσ =
        subst
          (λ T -> Derivable (isType (subTy sigma A ∷ []) T))
          (sym (wkTyLiftSubst sigma A))
          dWkBaseσ
      compL = substSccTy1 sigmaFits sigmaCFits dQtrσ dL

      complσ =
        subst
          (λ T ->
            Computable
              (hasTy (subTy sigma A ∷ [])
                (subTm (liftSubst sigma) l)
                T))
          (qtrBranchTyLiftComp sigma L)
          (substSccTm1 sigmaFits sigmaCFits dAσ dl)

      compcohσ =
        subst
          (λ J -> Computable J)
          (cong
            (λ T ->
              termEq (T ∷ subTy sigma A ∷ [])
                (subTm (liftSubst (liftSubst sigma)) (wkTmBy 1 l))
                (subTm (liftSubst (liftSubst sigma)) (renTm qtrSecondBranchRen l))
                (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
            (wkTyLiftSubst sigma A)
            ∙ cong
                (λ t ->
                  termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                    t
                    (subTm (liftSubst (liftSubst sigma)) (renTm qtrSecondBranchRen l))
                    (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
                (wkTmLiftSubst (liftSubst sigma) l)
            ∙ cong
                (λ u ->
                  termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                    (wkTmBy 1 (subTm (liftSubst sigma) l))
                    u
                    (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
                (qtrSecondBranchTmLiftComp sigma l)
            ∙ cong
                (λ T ->
                  termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                    (wkTmBy 1 (subTm (liftSubst sigma) l))
                    (renTm qtrSecondBranchRen (subTm (liftSubst sigma) l))
                    T)
                (qtrCohTyLiftComp sigma L))
          (substSccTmEq2 sigmaFits sigmaCFits dAσ dWkAσ dcoh)

      leftCan = compCQtrClosed compL compaσ complσ compcohσ

      complEq =
        subst
          (λ T ->
            Computable
              (termEq (subTy sigma A ∷ [])
                (subTm (liftSubst sigma) l)
                (subTm (liftSubst tau) l)
                T))
          (qtrBranchTyLiftComp sigma L)
          (eqSubSccTm1 fitsEq cFitsEq dAσ dl)

      branchFitsEq :
        FitsEqSubst [] (subTy sigma A ∷ [])
          (qtrCompSub (subTm sigma a))
          (qtrCompSub (subTm tau a))
      branchFitsEq =
        compFitsEqToFitsEq (qtrCompCompFitsEqHelper compa)

      compBodyEq = branchSubEq branchFitsEq complEq

      resultPath :
        termEq []
          (subTm sigma (tmElQtr l (tmClass a)))
          (subTm tau (subTm (qtrCompSub a) l))
          (subTy sigma (subTy (singleSubst (tmClass a)) L))
          ≡
        termEq []
          (tmElQtr (subTm (liftSubst sigma) l) (tmClass (subTm sigma a)))
          (subTm (qtrCompSub (subTm tau a)) (subTm (liftSubst tau) l))
          (subTy (singleSubst (tmClass (subTm sigma a))) (subTy (liftSubst sigma) L))
      resultPath =
        cong₃
          (termEq [])
          refl
          (subTmComp tau (qtrCompSub a) l
            ∙ cong (λ rho -> subTm rho l) (qtrCompSubLiftComp tau a)
            ∙ sym (subTmComp (qtrCompSub (subTm tau a)) (liftSubst tau) l))
          (subTyComp sigma (singleSubst (tmClass a)) L
            ∙ cong (λ rho -> subTy rho L) (sym (singleSubstCompLift sigma (tmClass a)))
            ∙ sym (subTyComp (singleSubst (tmClass (subTm sigma a))) (liftSubst sigma) L))
    in
    subst
      (λ J -> Computable J)
      (sym resultPath)
      (compTransTmClosed leftCan compBodyEq)
    where
    branchSubEq :
      FitsEqSubst [] (subTy sigma A ∷ [])
        (qtrCompSub (subTm sigma a))
        (qtrCompSub (subTm tau a))
      ->
      Computable
        (termEq (subTy sigma A ∷ [])
          (subTm (liftSubst sigma) l)
          (subTm (liftSubst tau) l)
          (qtrBranchTy (subTy (liftSubst sigma) L)))
      ->
      Computable
        (termEq []
          (subTm (qtrCompSub (subTm sigma a)) (subTm (liftSubst sigma) l))
          (subTm (qtrCompSub (subTm tau a)) (subTm (liftSubst tau) l))
          (subTy (singleSubst (tmClass (subTm sigma a))) (subTy (liftSubst sigma) L)))
    branchSubEq branchFitsEq (compTmEqOpen _ _ _ _ subEqdl) =
      subst
        (λ J -> Computable J)
        (cong
          (termEq []
            (subTm (qtrCompSub (subTm sigma a)) (subTm (liftSubst sigma) l))
            (subTm (qtrCompSub (subTm tau a)) (subTm (liftSubst tau) l)))
          (qtrBranchTyComp (subTm sigma a) (subTy (liftSubst sigma) L)))
        (ClosedEqSubstComp.closedEqComp
          (subEqdl
            (qtrCompSub (subTm sigma a))
            (qtrCompSub (subTm tau a))
            branchFitsEq))

  eqSubDerivTmComp : {gamma : Ctx} {t : RawTerm} {A : RawType} {sigma tau : Subst}
    -> Derivable (hasTy gamma t A)
    -> FitsEqSubst [] gamma sigma tau
    -> CompFitsEqSubst gamma sigma tau
    -> Computable (termEq [] (subTm sigma t) (subTm tau t) (subTy sigma A))
  eqSubDerivTmComp (varStar {delta = delta} {A = A} wf dA) fitsEq cFitsEq =
    lookupCompFitsEq {delta = delta} {A = A} cFitsEq
  eqSubDerivTmComp (iTop wf) fitsEq cFitsEq =
    compReflTm compITopClosed
  eqSubDerivTmComp {sigma = sigma} {tau = tau}
    (iSigma {a = a} {b = b} {A = A} {B = B} da db dSigma) fitsEq cFitsEq =
    let
      sigmaCFits = compFitsEqLeft cFitsEq
      sigmaFits = compFitsToFits sigmaCFits
      compac = eqSubDerivTmComp da fitsEq cFitsEq
      compSigma = substDerivTyComp dSigma sigmaFits sigmaCFits
      tyInv = invertSigmaTy compSigma evalSigma
      compAσ = ClosedSigmaTyInv.sigmaTyCompHead tyInv
      compBσ = ClosedSigmaTyInv.sigmaTyCompFam tyInv
      compbdRaw = eqSubDerivTmComp db fitsEq cFitsEq
      compbd =
        subst
          (λ T -> Computable (termEq [] (subTm sigma b) (subTm tau b) T))
          (subTyComp sigma (singleSubst a) B
            ∙ cong (λ rho -> subTy rho B) (sym (singleSubstCompLift sigma a))
            ∙ sym (subTyComp (singleSubst (subTm sigma a)) (liftSubst sigma) B))
          compbdRaw
      compa = compTmEqLeft compac
      compcA = compTmEqRightClosed compac
      compb = compTmEqLeft compbd
      compdA = compTmEqRightClosed compbd
      compd =
        compConvTmClosed compdA (compSingleEqSubstTyClosed compBσ compac)
      compPairLeft = compISigmaClosed compa compb compSigma
      compPairRight = compISigmaClosed compcA compd compSigma
    in
    compTmEqClosedSigma
      (iSigmaEq (compToDerivable compac) (compToDerivable compbd)
        (compToDerivable compAσ) (compToDerivable compBσ))
      compPairLeft
      compPairRight
      evalSigma
      evalPair
      evalPair
      compac
      compbd
  eqSubDerivTmComp (iEq da) fitsEq cFitsEq =
    compReflTm (compIEqClosed (compTmEqLeft (eqSubDerivTmComp da fitsEq cFitsEq)))
  eqSubDerivTmComp (iQtr da) fitsEq cFitsEq =
    let
      compab = eqSubDerivTmComp da fitsEq cFitsEq
    in
    compIQtrEqClosed (compTmEqLeft compab) (compTmEqRightClosed compab)
  eqSubDerivTmComp {gamma = gamma} {sigma = sigma} {tau = tau}
    (eSigma {A = A} {B = B} {M = M} {d = d} {m = m} dM dd dm) fitsEq cFitsEq =
    let
      sigmaCFits = compFitsEqLeft cFitsEq
      sigmaFits = compFitsToFits sigmaCFits
      compdd = eqSubDerivTmComp dd fitsEq cFitsEq
      compSigma = compTmToCompTy (compTmEqLeft compdd)
      dSigmaσ = compToDerivable compSigma
      compM = substSccTy1 sigmaFits sigmaCFits dSigmaσ dM

      tyInv = invertSigmaTy compSigma evalSigma
      compAσ = ClosedSigmaTyInv.sigmaTyCompHead tyInv
      compBσ = ClosedSigmaTyInv.sigmaTyCompFam tyInv
      dAσ = compToDerivable compAσ
      dBσ = compToDerivable compBσ

      compdm =
        subst
          (λ J -> Computable J)
          (cong
            (termEq (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ [])
              (subTm (liftSubst (liftSubst sigma)) m)
              (subTm (liftSubst (liftSubst tau)) m))
            (sigmaBranchTyLiftComp sigma M))
          (eqSubSccTm2 fitsEq cFitsEq dAσ dBσ dm)

      resultPath :
        termEq []
          (subTm sigma (tmElSigma d m))
          (subTm tau (tmElSigma d m))
          (subTy sigma (subTy (singleSubst d) M))
          ≡
        termEq []
          (tmElSigma (subTm sigma d) (subTm (liftSubst (liftSubst sigma)) m))
          (tmElSigma (subTm tau d) (subTm (liftSubst (liftSubst tau)) m))
          (subTy (singleSubst (subTm sigma d)) (subTy (liftSubst sigma) M))
      resultPath =
        cong₃
          (termEq [])
          refl
          refl
          (subTyComp sigma (singleSubst d) M
            ∙ cong (λ rho -> subTy rho M) (sym (singleSubstCompLift sigma d))
            ∙ sym (subTyComp (singleSubst (subTm sigma d)) (liftSubst sigma) M))
    in
    subst
      (λ J -> Computable J)
      (sym resultPath)
      (compESigmaClosed compM compdd compdm)
  eqSubDerivTmComp (eQtr dL dp dl dcoh) fitsEq cFitsEq =
    eqSubDerivTmCompEQtr dL dp dl dcoh fitsEq cFitsEq
  eqSubDerivTmComp (conv d dAB) fitsEq cFitsEq =
    let
      sigmaCFits = compFitsEqLeft cFitsEq
      sigmaFits = compFitsToFits sigmaCFits
    in
    compConvTmEqClosed (eqSubDerivTmComp d fitsEq cFitsEq) (substDerivTyEqComp dAB sigmaFits sigmaCFits)
  eqSubDerivTmComp {sigma = sigma} {tau = tau}
    (weakenTm {delta = delta} {t = t} {A = A} d wf) fitsEq cFitsEq =
    subst
      (λ J -> Computable J)
      (cong₃ (termEq [])
        (sym (subTmWkBy sigma (length delta) t))
        (sym (subTmWkBy tau (length delta) t))
        (sym (subTyWkBy sigma (length delta) A)))
      (eqSubDerivTmComp d (dropFitsEq delta fitsEq) (dropCompFitsEq delta cFitsEq))
  eqSubDerivTmComp {sigma = sigma} {tau = tau}
    (substTmRule {sigma = sigma'} {t = t} {A = A} d fits') fitsEq cFitsEq =
    let
      composedFitsEq = composeEqFits fitsEq fits'
      composedCFitsEq = composeCompEqFits fitsEq cFitsEq fits'
    in
    subst
      (λ J -> Computable J)
      (cong₃ (termEq [])
        (sym (subTmComp sigma sigma' t))
        (sym (subTmComp tau sigma' t))
        (sym (subTyComp sigma sigma' A)))
      (eqSubDerivTmComp d composedFitsEq composedCFitsEq)
  eqSubDerivTmEqComp : {gamma : Ctx} {t u : RawTerm} {A : RawType} {sigma tau : Subst}
    -> Derivable (termEq gamma t u A)
    -> FitsEqSubst [] gamma sigma tau
    -> CompFitsEqSubst gamma sigma tau
    -> Computable (termEq [] (subTm sigma t) (subTm tau u) (subTy sigma A))
  eqSubDerivTmEqComp (reflTm d) fitsEq cFitsEq =
    eqSubDerivTmComp d fitsEq cFitsEq
  eqSubDerivTmEqComp (symTm d) fitsEq cFitsEq =
    let
      sigmaCFits = compFitsEqLeft cFitsEq
      sigmaFits = compFitsToFits sigmaCFits
    in
    compTransTmClosed
      (compSymTmClosed (substDerivTmEqComp d sigmaFits sigmaCFits))
      (eqSubDerivTmComp (assocTmLeft d) fitsEq cFitsEq)
  eqSubDerivTmEqComp (transTm d₁ d₂) fitsEq cFitsEq =
    let
      sigmaCFits = compFitsEqLeft cFitsEq
      sigmaFits = compFitsToFits sigmaCFits
    in
    compTransTmClosed
      (substDerivTmEqComp d₁ sigmaFits sigmaCFits)
      (eqSubDerivTmEqComp d₂ fitsEq cFitsEq)
  eqSubDerivTmEqComp (convEq d dAB) fitsEq cFitsEq =
    let
      sigmaCFits = compFitsEqLeft cFitsEq
      sigmaFits = compFitsToFits sigmaCFits
    in
    compConvTmEqClosed (eqSubDerivTmEqComp d fitsEq cFitsEq) (substDerivTyEqComp dAB sigmaFits sigmaCFits)
  eqSubDerivTmEqComp (cTop d) fitsEq cFitsEq =
    compCTopClosed (compTmEqLeft (eqSubDerivTmComp d fitsEq cFitsEq))
  eqSubDerivTmEqComp {sigma = sigma} {tau = tau}
    (iSigmaEq {a = a} {b = b} {d = d} {A = A} {B = B} dac dbd dA dB) fitsEq cFitsEq =
    let
      sigmaCFits = compFitsEqLeft cFitsEq
      sigmaFits = compFitsToFits sigmaCFits
      compac = eqSubDerivTmEqComp dac fitsEq cFitsEq
      compA = substDerivTyComp dA sigmaFits sigmaCFits
      dAσ = compToDerivable compA
      compB = substSccTy1 sigmaFits sigmaCFits dAσ dB
      compbdRaw = eqSubDerivTmEqComp dbd fitsEq cFitsEq
      compbd =
        subst
          (λ T -> Computable (termEq [] (subTm sigma b) (subTm tau d) T))
          (subTyComp sigma (singleSubst a) B
            ∙ cong (λ rho -> subTy rho B) (sym (singleSubstCompLift sigma a))
            ∙ sym (subTyComp (singleSubst (subTm sigma a)) (liftSubst sigma) B))
          compbdRaw
      compa = compTmEqLeft compac
      compcA = compTmEqRightClosed compac
      compb = compTmEqLeft compbd
      compdA = compTmEqRightClosed compbd
      compd =
        compConvTmClosed compdA (compSingleEqSubstTyClosed compB compac)
      compPairLeft = compISigmaClosed compa compb (compFSigmaClosed compA compB)
      compPairRight = compISigmaClosed compcA compd (compFSigmaClosed compA compB)
    in
    compTmEqClosedSigma
      (iSigmaEq (compToDerivable compac) (compToDerivable compbd) dAσ (compToDerivable compB))
      compPairLeft
      compPairRight
      evalSigma
      evalPair
      evalPair
      compac
      compbd
  eqSubDerivTmEqComp {gamma = gamma} {sigma = sigma} {tau = tau}
    (eSigmaEq {A = A} {B = B} {M = M} {d = d} {d' = d'} {m = m} {m' = m'} dM dd dm) fitsEq cFitsEq =
    let
      sigmaCFits = compFitsEqLeft cFitsEq
      sigmaFits = compFitsToFits sigmaCFits
      compdd = eqSubDerivTmEqComp dd fitsEq cFitsEq
      compSigma = compTmToCompTy (compTmEqLeft compdd)
      dSigmaσ = compToDerivable compSigma
      compM = substSccTy1 sigmaFits sigmaCFits dSigmaσ dM

      tyInv = invertSigmaTy compSigma evalSigma
      compAσ = ClosedSigmaTyInv.sigmaTyCompHead tyInv
      compBσ = ClosedSigmaTyInv.sigmaTyCompFam tyInv
      dAσ = compToDerivable compAσ
      dBσ = compToDerivable compBσ

      compdm =
        subst
          (λ J -> Computable J)
          (cong
            (termEq (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ [])
              (subTm (liftSubst (liftSubst sigma)) m)
              (subTm (liftSubst (liftSubst tau)) m'))
            (sigmaBranchTyLiftComp sigma M))
          (eqSubSccTmEq2 fitsEq cFitsEq dAσ dBσ dm)

      resultPath :
        termEq []
          (subTm sigma (tmElSigma d m))
          (subTm tau (tmElSigma d' m'))
          (subTy sigma (subTy (singleSubst d) M))
          ≡
        termEq []
          (tmElSigma (subTm sigma d) (subTm (liftSubst (liftSubst sigma)) m))
          (tmElSigma (subTm tau d') (subTm (liftSubst (liftSubst tau)) m'))
          (subTy (singleSubst (subTm sigma d)) (subTy (liftSubst sigma) M))
      resultPath =
        cong₃
          (termEq [])
          refl
          refl
          (subTyComp sigma (singleSubst d) M
            ∙ cong (λ rho -> subTy rho M) (sym (singleSubstCompLift sigma d))
            ∙ sym (subTyComp (singleSubst (subTm sigma d)) (liftSubst sigma) M))
    in
    subst
      (λ J -> Computable J)
      (sym resultPath)
      (compESigmaClosed compM compdd compdm)
  eqSubDerivTmEqComp {gamma = gamma} {sigma = sigma} {tau = tau}
    (cSigma {A = A} {B = B} {M = M} {b = b} {c = c} {m = m} dM db dc dm) fitsEq cFitsEq =
    let
      sigmaCFits = compFitsEqLeft cFitsEq
      sigmaFits = compFitsToFits sigmaCFits
      compb = eqSubDerivTmComp db fitsEq cFitsEq
      compSigma = substDerivTyComp (ctxSuffixTy {delta = []} {gamma = gamma} {A = tySigma A B} (derivToCtxWF dM)) sigmaFits sigmaCFits
      dSigmaσ = compToDerivable compSigma
      tyInv = invertSigmaTy compSigma evalSigma
      compAσ = ClosedSigmaTyInv.sigmaTyCompHead tyInv
      compBσ = ClosedSigmaTyInv.sigmaTyCompFam tyInv
      dAσ = compToDerivable compAσ
      dBσ = compToDerivable compBσ
      compM = substSccTy1 sigmaFits sigmaCFits dSigmaσ dM

      compcRaw = eqSubDerivTmComp dc fitsEq cFitsEq
      compc =
        subst
          (λ T -> Computable (termEq [] (subTm sigma c) (subTm tau c) T))
          (subTyComp sigma (singleSubst b) B
            ∙ cong (λ rho -> subTy rho B) (sym (singleSubstCompLift sigma b))
            ∙ sym (subTyComp (singleSubst (subTm sigma b)) (liftSubst sigma) B))
          compcRaw

      branchFitsEq : FitsEqSubst [] (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ [])
        (sigmaCompSub (subTm sigma b) (subTm sigma c))
        (sigmaCompSub (subTm tau b) (subTm tau c))
      branchFitsEq =
        compFitsEqToFitsEq
          (sigmaCompCompFitsEqHelper compb compc)

      compdmOpen =
        eqSubSccTm2 fitsEq cFitsEq dAσ dBσ dm

      compdmEq =
        branchSubEq branchFitsEq compdmOpen

      leftCanPath :
        termEq []
          (subTm sigma (tmElSigma (tmPair b c) m))
          (subTm sigma (subTm (sigmaCompSub b c) m))
          (subTy sigma (subTy (singleSubst (tmPair b c)) M))
          ≡
        termEq []
          (tmElSigma (tmPair (subTm sigma b) (subTm sigma c))
            (subTm (liftSubst (liftSubst sigma)) m))
          (subTm (sigmaCompSub (subTm sigma b) (subTm sigma c))
            (subTm (liftSubst (liftSubst sigma)) m))
          (subTy (singleSubst (tmPair (subTm sigma b) (subTm sigma c)))
            (subTy (liftSubst sigma) M))
      leftCanPath =
        cong₃
          (termEq [])
          refl
          (subTmComp sigma (sigmaCompSub b c) m
            ∙ cong (λ rho -> subTm rho m) (sigmaCompSubLiftComp sigma b c)
            ∙ sym (subTmComp (sigmaCompSub (subTm sigma b) (subTm sigma c))
                (liftSubst (liftSubst sigma)) m))
          (subTyComp sigma (singleSubst (tmPair b c)) M
            ∙ cong (λ rho -> subTy rho M) (sym (singleSubstCompLift sigma (tmPair b c)))
            ∙ sym (subTyComp (singleSubst (tmPair (subTm sigma b) (subTm sigma c)))
                (liftSubst sigma) M))

      leftCan =
        subst
          (λ J -> Computable J)
          leftCanPath
          (substDerivTmEqComp (cSigma dM db dc dm) sigmaFits sigmaCFits)

      resultPath :
        termEq []
          (subTm sigma (tmElSigma (tmPair b c) m))
          (subTm tau (subTm (sigmaCompSub b c) m))
          (subTy sigma (subTy (singleSubst (tmPair b c)) M))
          ≡
        termEq []
          (tmElSigma (tmPair (subTm sigma b) (subTm sigma c))
            (subTm (liftSubst (liftSubst sigma)) m))
          (subTm (sigmaCompSub (subTm tau b) (subTm tau c))
            (subTm (liftSubst (liftSubst tau)) m))
          (subTy (singleSubst (tmPair (subTm sigma b) (subTm sigma c)))
            (subTy (liftSubst sigma) M))
      resultPath =
        cong₃
          (termEq [])
          refl
          (subTmComp tau (sigmaCompSub b c) m
            ∙ cong (λ rho -> subTm rho m) (sigmaCompSubLiftComp tau b c)
            ∙ sym (subTmComp (sigmaCompSub (subTm tau b) (subTm tau c))
                (liftSubst (liftSubst tau)) m))
          (subTyComp sigma (singleSubst (tmPair b c)) M
            ∙ cong (λ rho -> subTy rho M) (sym (singleSubstCompLift sigma (tmPair b c)))
            ∙ sym (subTyComp (singleSubst (tmPair (subTm sigma b) (subTm sigma c)))
                (liftSubst sigma) M))
    in
    subst
      (λ J -> Computable J)
      (sym resultPath)
      (compTransTmClosed leftCan compdmEq)
    where
    branchSubEq :
      FitsEqSubst [] (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ [])
        (sigmaCompSub (subTm sigma b) (subTm sigma c))
        (sigmaCompSub (subTm tau b) (subTm tau c))
      ->
      Computable
        (termEq (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ [])
          (subTm (liftSubst (liftSubst sigma)) m)
          (subTm (liftSubst (liftSubst tau)) m)
          (subTy (liftSubst (liftSubst sigma)) (sigmaBranchTy M)))
      -> Computable
           (termEq []
             (subTm (sigmaCompSub (subTm sigma b) (subTm sigma c))
               (subTm (liftSubst (liftSubst sigma)) m))
             (subTm (sigmaCompSub (subTm tau b) (subTm tau c))
               (subTm (liftSubst (liftSubst tau)) m))
             (subTy (singleSubst (tmPair (subTm sigma b) (subTm sigma c)))
               (subTy (liftSubst sigma) M)))
    branchSubEq branchFitsEq (compTmEqOpen _ _ _ _ subEqdm) =
      subst
        (λ J -> Computable J)
        (cong
          (termEq []
            (subTm (sigmaCompSub (subTm sigma b) (subTm sigma c))
              (subTm (liftSubst (liftSubst sigma)) m))
            (subTm (sigmaCompSub (subTm tau b) (subTm tau c))
              (subTm (liftSubst (liftSubst tau)) m)))
          (cong
            (λ T -> subTy (sigmaCompSub (subTm sigma b) (subTm sigma c)) T)
            (sigmaBranchTyLiftComp sigma M)
            ∙ sigmaBranchTyComp (subTm sigma b) (subTm sigma c) (subTy (liftSubst sigma) M)))
        (ClosedEqSubstComp.closedEqComp
          (subEqdm
            (sigmaCompSub (subTm sigma b) (subTm sigma c))
            (sigmaCompSub (subTm tau b) (subTm tau c))
            branchFitsEq))
  eqSubDerivTmEqComp (iEqEq d) fitsEq cFitsEq =
    compReflTm (compIEqClosed (compTmEqLeft (eqSubDerivTmEqComp d fitsEq cFitsEq)))
  eqSubDerivTmEqComp (eEqStar dp dA da db) fitsEq cFitsEq =
    let
      compp = eqSubDerivTmComp dp fitsEq cFitsEq
      compab = compEEqClosed (compTmEqLeft compp)
      compbb' = eqSubDerivTmComp db fitsEq cFitsEq
    in
    compTransTmClosed compab compbb'
  eqSubDerivTmEqComp (cEq dp dA da db) fitsEq cFitsEq =
    compCEqClosed (compTmEqLeft (eqSubDerivTmComp dp fitsEq cFitsEq))
  eqSubDerivTmEqComp (iQtrEq da db) fitsEq cFitsEq =
    let
      compab = eqSubDerivTmComp da fitsEq cFitsEq
      compcd = eqSubDerivTmComp db fitsEq cFitsEq
    in
    compIQtrEqClosed (compTmEqLeft compab) (compTmEqRightClosed compcd)
  eqSubDerivTmEqComp (eQtrEq dL dp dl dcoh dcoh') fitsEq cFitsEq =
    eqSubDerivTmEqCompEQtrEq dL dp dl dcoh dcoh' fitsEq cFitsEq
  eqSubDerivTmEqComp (cQtr dL da dl dcoh) fitsEq cFitsEq =
    eqSubDerivTmEqCompCQtr dL da dl dcoh fitsEq cFitsEq
  eqSubDerivTmEqComp {sigma = sigma} {tau = tau}
    (weakenTmEq {delta = delta} {t = t} {u = u} {A = A} d wf) fitsEq cFitsEq =
    subst
      (λ J -> Computable J)
      (cong₃ (termEq [])
        (sym (subTmWkBy sigma (length delta) t))
        (sym (subTmWkBy tau (length delta) u))
        (sym (subTyWkBy sigma (length delta) A)))
      (eqSubDerivTmEqComp d (dropFitsEq delta fitsEq) (dropCompFitsEq delta cFitsEq))
  eqSubDerivTmEqComp {sigma = sigma} {tau = tau}
    (substTmEqRule {sigma = sigma'} {t = t} {u = u} {A = A} d fits') fitsEq cFitsEq =
    let
      composedFitsEq = composeEqFits fitsEq fits'
      composedCFitsEq = composeCompEqFits fitsEq cFitsEq fits'
    in
    subst
      (λ J -> Computable J)
      (cong₃ (termEq [])
        (sym (subTmComp sigma sigma' t))
        (sym (subTmComp tau sigma' u))
        (sym (subTyComp sigma sigma' A)))
      (eqSubDerivTmEqComp d composedFitsEq composedCFitsEq)
  eqSubDerivTmEqComp {sigma = sigma} {tau = tau}
    (eqSubTmRule {sigma = sigma'} {tau = tau'} {t = t} {A = A} d fitsEq') fitsEq cFitsEq =
    let
      composedFitsEq = composeEqFitsEq fitsEq fitsEq'
      composedCFitsEq = composeCompEqFitsEq fitsEq cFitsEq fitsEq'
    in
    subst
      (λ J -> Computable J)
      (cong₃ (termEq [])
        (sym (subTmComp sigma sigma' t))
        (sym (subTmComp tau tau' t))
        (sym (subTyComp sigma sigma' A)))
      (eqSubDerivTmComp d composedFitsEq composedCFitsEq)
  eqSubDerivTmEqComp {sigma = sigma} {tau = tau}
    (eqSubTmEqRule {sigma = sigma'} {tau = tau'} {t = t} {u = u} {A = A} d fitsEq') fitsEq cFitsEq =
    let
      composedFitsEq = composeEqFitsEq fitsEq fitsEq'
      composedCFitsEq = composeCompEqFitsEq fitsEq cFitsEq fitsEq'
    in
    subst
      (λ J -> Computable J)
      (cong₃ (termEq [])
        (sym (subTmComp sigma sigma' t))
        (sym (subTmComp tau tau' u))
        (sym (subTyComp sigma sigma' A)))
      (eqSubDerivTmEqComp d composedFitsEq composedCFitsEq)
  openCompTy : {A : RawType} {B : RawType} {gamma : Ctx}
    -> Derivable (isType (B ∷ gamma) A)
    -> Computable (isType (B ∷ gamma) A)
  openCompTy d =
    compTyOpen
      nonemptyNeNil
      d
      (λ sigma fits -> packClosedSubst fits (substDerivTyComp d fits (fitsToCompFits fits)))
      (λ sigma tau fitsEq -> packClosedEqSubst fitsEq (eqSubDerivTyComp d fitsEq (fitsEqToCompFitsEq fitsEq)))

  openCompTyEq : {A B C : RawType} {gamma : Ctx}
    -> Derivable (typeEq (C ∷ gamma) A B)
    -> Computable (typeEq (C ∷ gamma) A B)
  openCompTyEq d =
    compTyEqOpen
      nonemptyNeNil
      d
      (openCompTy (assocTyLeft d))
      (λ sigma fits -> packClosedSubst fits (substDerivTyEqComp d fits (fitsToCompFits fits)))
      (λ sigma tau fitsEq -> packClosedEqSubst fitsEq (eqSubDerivTyEqComp d fitsEq (fitsEqToCompFitsEq fitsEq)))

  openCompTm : {t : RawTerm} {A B : RawType} {gamma : Ctx}
    -> Derivable (hasTy (B ∷ gamma) t A)
    -> Computable (hasTy (B ∷ gamma) t A)
  openCompTm d =
    compTmOpen
      nonemptyNeNil
      d
      (openCompTy (assocTy d))
      (λ sigma fits -> packClosedSubst fits (substDerivTmComp d fits (fitsToCompFits fits)))
      (λ sigma tau fitsEq -> packClosedEqSubst fitsEq (eqSubDerivTmComp d fitsEq (fitsEqToCompFitsEq fitsEq)))

  openCompTmEq : {t u : RawTerm} {A B : RawType} {gamma : Ctx}
    -> Derivable (termEq (B ∷ gamma) t u A)
    -> Computable (termEq (B ∷ gamma) t u A)
  openCompTmEq d =
    compTmEqOpen
      nonemptyNeNil
      d
      (openCompTm (assocTmLeft d))
      (λ sigma fits -> packClosedSubst fits (substDerivTmEqComp d fits (fitsToCompFits fits)))
      (λ sigma tau fitsEq -> packClosedEqSubst fitsEq (eqSubDerivTmEqComp d fitsEq (fitsEqToCompFitsEq fitsEq)))

  substTyClosed : {delta : Ctx} {A : RawType} {sigma : Subst}
    -> Derivable (isType delta A)
    -> FitsSubst [] delta sigma
    -> Computable (isType [] (subTy sigma A))
  substTyClosed d fits = substDerivTyComp d fits (fitsToCompFits fits)

  substTyEqClosed : {delta : Ctx} {A B : RawType} {sigma : Subst}
    -> Derivable (typeEq delta A B)
    -> FitsSubst [] delta sigma
    -> Computable (typeEq [] (subTy sigma A) (subTy sigma B))
  substTyEqClosed d fits = substDerivTyEqComp d fits (fitsToCompFits fits)

  substTmClosed : {delta : Ctx} {t : RawTerm} {A : RawType} {sigma : Subst}
    -> Derivable (hasTy delta t A)
    -> FitsSubst [] delta sigma
    -> Computable (hasTy [] (subTm sigma t) (subTy sigma A))
  substTmClosed d fits = substDerivTmComp d fits (fitsToCompFits fits)

  substTmEqClosed : {delta : Ctx} {t u : RawTerm} {A : RawType} {sigma : Subst}
    -> Derivable (termEq delta t u A)
    -> FitsSubst [] delta sigma
    -> Computable (termEq [] (subTm sigma t) (subTm sigma u) (subTy sigma A))
  substTmEqClosed d fits = substDerivTmEqComp d fits (fitsToCompFits fits)

  eqSubTyClosed : {delta : Ctx} {A : RawType} {sigma tau : Subst}
    -> Derivable (isType delta A)
    -> FitsEqSubst [] delta sigma tau
    -> Computable (typeEq [] (subTy sigma A) (subTy tau A))
  eqSubTyClosed d fitsEq = eqSubDerivTyComp d fitsEq (fitsEqToCompFitsEq fitsEq)

  eqSubTyEqClosed : {delta : Ctx} {A B : RawType} {sigma tau : Subst}
    -> Derivable (typeEq delta A B)
    -> FitsEqSubst [] delta sigma tau
    -> Computable (typeEq [] (subTy sigma A) (subTy tau B))
  eqSubTyEqClosed d fitsEq = eqSubDerivTyEqComp d fitsEq (fitsEqToCompFitsEq fitsEq)

  eqSubTmClosed : {delta : Ctx} {t : RawTerm} {A : RawType} {sigma tau : Subst}
    -> Derivable (hasTy delta t A)
    -> FitsEqSubst [] delta sigma tau
    -> Computable (termEq [] (subTm sigma t) (subTm tau t) (subTy sigma A))
  eqSubTmClosed d fitsEq = eqSubDerivTmComp d fitsEq (fitsEqToCompFitsEq fitsEq)

  eqSubTmEqClosed : {delta : Ctx} {t u : RawTerm} {A : RawType} {sigma tau : Subst}
    -> Derivable (termEq delta t u A)
    -> FitsEqSubst [] delta sigma tau
    -> Computable (termEq [] (subTm sigma t) (subTm tau u) (subTy sigma A))
  eqSubTmEqClosed d fitsEq = eqSubDerivTmEqComp d fitsEq (fitsEqToCompFitsEq fitsEq)

  hypComputableTy : {A B : RawType} {gamma : Ctx}
    -> Derivable (isType (B ∷ gamma) A)
    -> HypComputable (isType (B ∷ gamma) A)
  hypComputableTy d =
    hypTyOpen
      nonemptyNeNil
      d
      (λ sigma fits _ -> substTyClosed d fits)
      (λ sigma tau fitsEq _ -> eqSubTyClosed d fitsEq)

  hypComputableTyEq : {A B C : RawType} {gamma : Ctx}
    -> Derivable (typeEq (C ∷ gamma) A B)
    -> HypComputable (typeEq (C ∷ gamma) A B)
  hypComputableTyEq d =
    hypTyEqOpen
      nonemptyNeNil
      d
      (hypComputableTy (assocTyLeft d))
      (λ sigma fits _ -> substTyEqClosed d fits)
      (λ sigma tau fitsEq _ -> eqSubTyEqClosed d fitsEq)

  hypComputableTm : {t : RawTerm} {A B : RawType} {gamma : Ctx}
    -> Derivable (hasTy (B ∷ gamma) t A)
    -> HypComputable (hasTy (B ∷ gamma) t A)
  hypComputableTm d =
    hypTmOpen
      nonemptyNeNil
      d
      (hypComputableTy (assocTy d))
      (λ sigma fits _ -> substTmClosed d fits)
      (λ sigma tau fitsEq _ -> eqSubTmClosed d fitsEq)

  hypComputableTmEq : {t u : RawTerm} {A B : RawType} {gamma : Ctx}
    -> Derivable (termEq (B ∷ gamma) t u A)
    -> HypComputable (termEq (B ∷ gamma) t u A)
  hypComputableTmEq d =
    hypTmEqOpen
      nonemptyNeNil
      d
      (hypComputableTm (assocTmLeft d))
      (λ sigma fits _ -> substTmEqClosed d fits)
      (λ sigma tau fitsEq _ -> eqSubTmEqClosed d fitsEq)

  compTransportFamilyTy : {A C D : RawType}
    -> Computable (typeEq [] A C)
    -> Computable (isType (A ∷ []) D)
    -> Computable (isType (C ∷ []) D)
  compTransportFamilyTy {A = A} {C = C} {D = D} compAC (compTyOpen neq dD sub subEq) =
    compTyOpen
      nonemptyNeNil
      (transportFamilyTy dAC dC dD)
      (λ sigma fits ->
        packClosedSubst fits
          (subst
            (λ T -> Computable (isType [] T))
            (sym (subTyComp sigma idSubst D) ∙ cong (subTy sigma) (subTyId D))
            (ClosedSubstComp.closedComp
              (sub (compSub sigma idSubst) (composeFits fits transportFits)))))
      (λ sigma tau fitsEq ->
        packClosedEqSubst fitsEq
          (subst
            (λ J -> Computable J)
            (cong₂ (typeEq [])
              (sym (subTyComp sigma idSubst D) ∙ cong (subTy sigma) (subTyId D))
              (sym (subTyComp tau idSubst D) ∙ cong (subTy tau) (subTyId D)))
            (ClosedEqSubstComp.closedEqComp
              (subEq
                (compSub sigma idSubst)
                (compSub tau idSubst)
                (composeEqFits fitsEq transportFits)))))
    where
    dAC : Derivable (typeEq [] A C)
    dAC = compToDerivable compAC

    dC : Derivable (isType [] C)
    dC = compToDerivable (compTyEqRightClosed compAC)

    transportFits : FitsSubst (C ∷ []) (A ∷ []) idSubst
    transportFits = headTypeTransportFits dAC dC

  compTransportFamilyTyEq : {A C D F : RawType}
    -> Computable (typeEq [] A C)
    -> Computable (typeEq (A ∷ []) D F)
    -> Computable (typeEq (C ∷ []) D F)
  compTransportFamilyTyEq {A = A} {C = C} {D = D} {F = F} compAC (compTyEqOpen neq dDF compD sub subEq) =
    compTyEqOpen
      nonemptyNeNil
      (transportFamilyTyEq dAC dC dDF)
      (compTransportFamilyTy compAC compD)
      (λ sigma fits ->
        packClosedSubst fits
          (subst
            (λ J -> Computable J)
            (cong₂ (typeEq [])
              (sym (subTyComp sigma idSubst D) ∙ cong (subTy sigma) (subTyId D))
              (sym (subTyComp sigma idSubst F) ∙ cong (subTy sigma) (subTyId F)))
            (ClosedSubstComp.closedComp
              (sub (compSub sigma idSubst) (composeFits fits transportFits)))))
      (λ sigma tau fitsEq ->
        packClosedEqSubst fitsEq
          (subst
            (λ J -> Computable J)
            (cong₂ (typeEq [])
              (sym (subTyComp sigma idSubst D) ∙ cong (subTy sigma) (subTyId D))
              (sym (subTyComp tau idSubst F) ∙ cong (subTy tau) (subTyId F)))
            (ClosedEqSubstComp.closedEqComp
              (subEq
                (compSub sigma idSubst)
                (compSub tau idSubst)
                (composeEqFits fitsEq transportFits)))))
    where
    dAC : Derivable (typeEq [] A C)
    dAC = compToDerivable compAC

    dC : Derivable (isType [] C)
    dC = compToDerivable (compTyEqRightClosed compAC)

    transportFits : FitsSubst (C ∷ []) (A ∷ []) idSubst
    transportFits = headTypeTransportFits dAC dC

  compSymTyOpenHelper : {gamma : Ctx} {A B : RawType}
    -> ({A B : RawType} -> Computable (typeEq [] A B) -> Computable (typeEq [] B A))
    -> ({A B C : RawType} -> Computable (typeEq [] A B) -> Computable (typeEq [] B C) -> Computable (typeEq [] A C))
    -> ((gamma ≡ []) -> ⊥)
    -> Derivable (typeEq gamma A B)
    -> Computable (isType gamma A)
    -> ((sigma : Subst) -> FitsSubst [] gamma sigma
         -> ClosedSubstComp (typeEq gamma A B) sigma)
    -> ((sigma tau : Subst) -> FitsEqSubst [] gamma sigma tau
         -> ClosedEqSubstComp (typeEq gamma A B) sigma tau)
    -> Computable (typeEq gamma B A)
  compSymTyOpenHelper symCl transCl neq d compA sub subEq =
    compTyEqOpen
      neq
      (symTy d)
      (compTyOpen
        neq
        (assocTyRight d)
        (λ sigma fits ->
          packClosedSubst fits
            (compTyEqRightClosed (ClosedSubstComp.closedComp (sub sigma fits))))
        (λ sigma tau fitsEq ->
          let
            closedσ = ClosedSubstComp.closedComp (sub sigma (fitsEqSubstLeft fitsEq))
            closedστ = ClosedEqSubstComp.closedEqComp (subEq sigma tau fitsEq)
          in
          packClosedEqSubst fitsEq
            (transCl
              (symCl closedσ)
              closedστ)))
      (λ sigma fits ->
        packClosedSubst fits
          (symCl (ClosedSubstComp.closedComp (sub sigma fits))))
      (λ sigma tau fitsEq ->
        let
          closedσ = ClosedSubstComp.closedComp (sub sigma (fitsEqSubstLeft fitsEq))
          closedστ = ClosedEqSubstComp.closedEqComp (subEq sigma tau fitsEq)
          closedτ = ClosedSubstComp.closedComp (sub tau (fitsEqSubstRight (derivToCtxWF d) fitsEq))
        in
        packClosedEqSubst fitsEq
          (transCl
            (transCl (symCl closedσ) closedστ)
            (symCl closedτ)))

  compTransTyOpenHelper : {gamma : Ctx} {A B C : RawType}
    -> ({A B C : RawType} -> Computable (typeEq [] A B) -> Computable (typeEq [] B C) -> Computable (typeEq [] A C))
    -> ((gamma ≡ []) -> ⊥)
    -> Derivable (typeEq gamma A B)
    -> Computable (isType gamma A)
    -> ((sigma : Subst) -> FitsSubst [] gamma sigma
         -> ClosedSubstComp (typeEq gamma A B) sigma)
    -> ((sigma tau : Subst) -> FitsEqSubst [] gamma sigma tau
         -> ClosedEqSubstComp (typeEq gamma A B) sigma tau)
    -> Derivable (typeEq gamma B C)
    -> ((sigma : Subst) -> FitsSubst [] gamma sigma
         -> ClosedSubstComp (typeEq gamma B C) sigma)
    -> ((sigma tau : Subst) -> FitsEqSubst [] gamma sigma tau
         -> ClosedEqSubstComp (typeEq gamma B C) sigma tau)
    -> Computable (typeEq gamma A C)
  compTransTyOpenHelper transCl neq dAB compA subAB subEqAB dBC subBC subEqBC =
    compTyEqOpen
      neq
      (transTy dAB dBC)
      compA
      (λ sigma fits ->
        packClosedSubst fits
          (transCl
            (ClosedSubstComp.closedComp (subAB sigma fits))
            (ClosedSubstComp.closedComp (subBC sigma fits))))
      (λ sigma tau fitsEq ->
        let
          closedστ = ClosedEqSubstComp.closedEqComp (subEqAB sigma tau fitsEq)
          closedτ = ClosedSubstComp.closedComp (subBC tau (fitsEqSubstRight (derivToCtxWF dBC) fitsEq))
        in
        packClosedEqSubst fitsEq
          (transCl closedστ closedτ))

  compSymTransportFamilyTyEq : {A C D F : RawType}
    -> ((sigma : Subst) -> FitsSubst [] (C ∷ []) sigma
         -> Computable (isType [] (subTy sigma F)))
    -> ((sigma tau : Subst) -> FitsEqSubst [] (C ∷ []) sigma tau
         -> Computable (typeEq [] (subTy sigma F) (subTy tau F)))
    -> ((sigma : Subst) -> FitsSubst [] (C ∷ []) sigma
         -> Computable (typeEq [] (subTy sigma F) (subTy sigma D)))
    -> ((sigma tau : Subst) -> FitsEqSubst [] (C ∷ []) sigma tau
         -> Computable (typeEq [] (subTy sigma F) (subTy tau D)))
    -> Computable (typeEq [] A C)
    -> Computable (typeEq (A ∷ []) D F)
    -> Computable (typeEq (C ∷ []) F D)
  compSymTransportFamilyTyEq
    {A = A} {C = C} {D = D} {F = F}
    tySub tySubEq symSub symSubEq compAC (compTyEqOpen neq dDF compD sub subEq) =
    compTyEqOpen
      nonemptyNeNil
      (symTy transportedEq)
      (compTyOpen
        nonemptyNeNil
        (assocTyRight transportedEq)
        (λ sigma fits -> packClosedSubst fits (tySub sigma fits))
        (λ sigma tau fitsEq -> packClosedEqSubst fitsEq (tySubEq sigma tau fitsEq)))
      (λ sigma fits -> packClosedSubst fits (symSub sigma fits))
      (λ sigma tau fitsEq -> packClosedEqSubst fitsEq (symSubEq sigma tau fitsEq))
    where
    dAC : Derivable (typeEq [] A C)
    dAC = compToDerivable compAC

    dC : Derivable (isType [] C)
    dC = compToDerivable (compTyEqRightClosed compAC)

    transportedEq : Derivable (typeEq (C ∷ []) D F)
    transportedEq = transportFamilyTyEq dAC dC dDF

    transportFits : FitsSubst (C ∷ []) (A ∷ []) idSubst
    transportFits = headTypeTransportFits dAC dC

  compSymTy : {gamma : Ctx} {A B : RawType}
    -> Computable (typeEq gamma A B)
    -> Computable (typeEq gamma B A)
  compSymTy comp@(compTyEqClosedTop _ _ _ _ _) = compSymTyClosed comp
  compSymTy comp@(compTyEqClosedSigma _ _ _ _ _ _ _) = compSymTyClosed comp
  compSymTy comp@(compTyEqClosedEq _ _ _ _ _ _ _ _) = compSymTyClosed comp
  compSymTy comp@(compTyEqClosedQtr _ _ _ _ _ _) = compSymTyClosed comp
  compSymTy {gamma = []} (compTyEqOpen neq _ _ _ _) = Empty.rec (neq refl)
  compSymTy {gamma = C ∷ gamma} (compTyEqOpen neq d compA sub subEq) =
    compSymTyOpenHelper compSymTyClosed compTransTyClosed neq d compA sub subEq

  compTransTy : {gamma : Ctx} {A B C : RawType}
    -> Computable (typeEq gamma A B)
    -> Computable (typeEq gamma B C)
    -> Computable (typeEq gamma A C)
  compTransTy compAB@(compTyEqClosedTop _ _ _ _ _) compBC = compTransTyClosed compAB compBC
  compTransTy compAB@(compTyEqClosedSigma _ _ _ _ _ _ _) compBC = compTransTyClosed compAB compBC
  compTransTy compAB@(compTyEqClosedEq _ _ _ _ _ _ _ _) compBC = compTransTyClosed compAB compBC
  compTransTy compAB@(compTyEqClosedQtr _ _ _ _ _ _) compBC = compTransTyClosed compAB compBC
  compTransTy {gamma = []} (compTyEqOpen neq _ _ _ _) _ = Empty.rec (neq refl)
  compTransTy {gamma = D ∷ gamma}
    (compTyEqOpen neq dAB compA subAB subEqAB)
    (compTyEqOpen _ dBC _ subBC subEqBC) =
    compTransTyOpenHelper compTransTyClosed neq dAB compA subAB subEqAB dBC subBC subEqBC

  compConvTm : {gamma : Ctx} {t : RawTerm} {A B : RawType}
    -> Computable (hasTy gamma t A)
    -> Computable (typeEq gamma A B)
    -> Computable (hasTy gamma t B)
  compConvTm comp@(compTmClosedTop _ _ _ _ _) compAB = compConvTmClosed comp compAB
  compConvTm comp@(compTmClosedSigma _ _ _ _ _ _ _) compAB = compConvTmClosed comp compAB
  compConvTm comp@(compTmClosedEq _ _ _ _ _ _) compAB = compConvTmClosed comp compAB
  compConvTm comp@(compTmClosedQtr _ _ _ _ _ _) compAB = compConvTmClosed comp compAB
  compConvTm {gamma = []} (compTmOpen neq _ _ _ _) _ = Empty.rec (neq refl)
  compConvTm {gamma = C ∷ gamma} (compTmOpen _ d _ _ _) compAB =
    openCompTm (conv d (compToDerivable compAB))

  compConvTmEq : {gamma : Ctx} {t u : RawTerm} {A B : RawType}
    -> Computable (termEq gamma t u A)
    -> Computable (typeEq gamma A B)
    -> Computable (termEq gamma t u B)
  compConvTmEq comp@(compTmEqClosedTop _ _ _ _ _ _) compAB = compConvTmEqClosed comp compAB
  compConvTmEq comp@(compTmEqClosedSigma _ _ _ _ _ _ _ _) compAB = compConvTmEqClosed comp compAB
  compConvTmEq comp@(compTmEqClosedEq _ _ _ _ _ _ _) compAB = compConvTmEqClosed comp compAB
  compConvTmEq comp@(compTmEqClosedQtr _ _ _ _ _ _ _ _) compAB = compConvTmEqClosed comp compAB
  compConvTmEq {gamma = []} (compTmEqOpen neq _ _ _ _) _ = Empty.rec (neq refl)
  compConvTmEq {gamma = C ∷ gamma} (compTmEqOpen _ d _ _ _) compAB =
    openCompTmEq (convEq d (compToDerivable compAB))

  compTransTm : {gamma : Ctx} {t u v : RawTerm} {A : RawType}
    -> Computable (termEq gamma t u A)
    -> Computable (termEq gamma u v A)
    -> Computable (termEq gamma t v A)
  compTransTm comp₁@(compTmEqClosedTop _ _ _ _ _ _) comp₂ = compTransTmClosed comp₁ comp₂
  compTransTm comp₁@(compTmEqClosedSigma _ _ _ _ _ _ _ _) comp₂ = compTransTmClosed comp₁ comp₂
  compTransTm comp₁@(compTmEqClosedEq _ _ _ _ _ _ _) comp₂ = compTransTmClosed comp₁ comp₂
  compTransTm comp₁@(compTmEqClosedQtr _ _ _ _ _ _ _ _) comp₂ = compTransTmClosed comp₁ comp₂
  compTransTm {gamma = []} (compTmEqOpen neq _ _ _ _) _ = Empty.rec (neq refl)
  compTransTm {gamma = C ∷ gamma}
    (compTmEqOpen neq d₁ compt₁ sub₁ subEq₁)
    (compTmEqOpen _ d₂ _ sub₂ subEq₂)
    with compTmToCompTy compt₁
  ... | compTyOpen _ _ _ subEqA =
    compTmEqOpen
      neq
      (transTm d₁ d₂)
      compt₁
      (λ sigma fits ->
        packClosedSubst fits
          (compTransTmClosed
            (ClosedSubstComp.closedComp (sub₁ sigma fits))
            (ClosedSubstComp.closedComp (sub₂ sigma fits))))
      (λ sigma tau fitsEq ->
        let
          closedστ = ClosedEqSubstComp.closedEqComp (subEq₁ sigma tau fitsEq)
          closedτ = ClosedSubstComp.closedComp (sub₂ tau (fitsEqSubstRight (derivToCtxWF d₂) fitsEq))
          closedτσ =
            compConvTmEqClosed
              closedτ
              (compSymTyClosed (ClosedEqSubstComp.closedEqComp (subEqA sigma tau fitsEq)))
        in
        packClosedEqSubst fitsEq
          (compTransTmClosed closedστ closedτσ))

  compSymTm : {gamma : Ctx} {t u : RawTerm} {A : RawType}
    -> Computable (termEq gamma t u A)
    -> Computable (termEq gamma u t A)
  compSymTm comp@(compTmEqClosedTop _ _ _ _ _ _) = compSymTmClosed comp
  compSymTm comp@(compTmEqClosedSigma _ _ _ _ _ _ _ _) = compSymTmClosed comp
  compSymTm comp@(compTmEqClosedEq _ _ _ _ _ _ _) = compSymTmClosed comp
  compSymTm comp@(compTmEqClosedQtr _ _ _ _ _ _ _ _) = compSymTmClosed comp
  compSymTm {gamma = []} (compTmEqOpen neq _ _ _ _) = Empty.rec (neq refl)
  compSymTm {gamma = B ∷ gamma} (compTmEqOpen neq d compt sub subEq) with compTmToCompTy compt
  ... | compAeq@(compTyOpen _ _ _ subEqA) =
    compTmEqOpen
      neq
      (symTm d)
      (compTmOpen
        neq
        (assocTmRight d)
        compAeq
        (λ sigma fits ->
          packClosedSubst fits
            (compTmEqRightClosed (ClosedSubstComp.closedComp (sub sigma fits))))
        (λ sigma tau fitsEq ->
          let
            closedσ = ClosedSubstComp.closedComp (sub sigma (fitsEqSubstLeft fitsEq))
            closedστ = ClosedEqSubstComp.closedEqComp (subEq sigma tau fitsEq)
          in
          packClosedEqSubst fitsEq
            (compTransTmClosed
              (compSymTmClosed closedσ)
              closedστ)))
      (λ sigma fits ->
        packClosedSubst fits
          (compSymTmClosed (ClosedSubstComp.closedComp (sub sigma fits))))
      (λ sigma tau fitsEq ->
        let
          closedσ = ClosedSubstComp.closedComp (sub sigma (fitsEqSubstLeft fitsEq))
          closedστ = ClosedEqSubstComp.closedEqComp (subEq sigma tau fitsEq)
          closedτ = ClosedSubstComp.closedComp (sub tau (fitsEqSubstRight (derivToCtxWF d) fitsEq))
          closedτσ =
            compConvTmEqClosed
              (compSymTmClosed closedτ)
              (compSymTyClosed (ClosedEqSubstComp.closedEqComp (subEqA sigma tau fitsEq)))
        in
        packClosedEqSubst fitsEq
          (compTransTmClosed
            (compTransTmClosed (compSymTmClosed closedσ) closedστ)
            closedτσ))

  weakenOneOpenTy : {A B C : RawType}
    -> Computable (isType (A ∷ []) B)
    -> CtxWF (C ∷ A ∷ [])
    -> Computable (isType (C ∷ A ∷ []) (wkTyBy 1 B))
  weakenOneOpenTy {A = A} {B = B} {C = C} (compTyOpen neq d sub subEq) wf =
    compTyOpen
      nonemptyNeNil
      (weakenTy {gamma = A ∷ []} {delta = C ∷ []} d wf)
      (λ sigma fits ->
        packClosedSubst fits
          (subst
            (λ T -> Computable (isType [] T))
            (sym (subTyWkBy sigma 1 B))
            (ClosedSubstComp.closedComp
              (sub (dropSubstBy 1 sigma) (dropFits (C ∷ []) fits)))))
      (λ sigma tau fitsEq ->
        packClosedEqSubst fitsEq
          (subst
            (λ J -> Computable J)
            (cong₂ (typeEq [])
              (sym (subTyWkBy sigma 1 B))
              (sym (subTyWkBy tau 1 B)))
            (ClosedEqSubstComp.closedEqComp
              (subEq
                (dropSubstBy 1 sigma)
                (dropSubstBy 1 tau)
                (dropFitsEq (C ∷ []) fitsEq)))))

  weakenOneOpenTm : {A B C : RawType} {t : RawTerm}
    -> Computable (hasTy (A ∷ []) t B)
    -> CtxWF (C ∷ A ∷ [])
    -> Computable (hasTy (C ∷ A ∷ []) (wkTmBy 1 t) (wkTyBy 1 B))
  weakenOneOpenTm {A = A} {B = B} {C = C} {t = t}
    (compTmOpen neq d compB sub subEq) wf =
    compTmOpen
      nonemptyNeNil
      (weakenTm {gamma = A ∷ []} {delta = C ∷ []} d wf)
      (weakenOneOpenTy compB wf)
      (λ sigma fits ->
        packClosedSubst fits
          (subst
            (λ J -> Computable J)
            (cong₂ (hasTy [])
              (sym (subTmWkBy sigma 1 t))
              (sym (subTyWkBy sigma 1 B)))
            (ClosedSubstComp.closedComp
              (sub (dropSubstBy 1 sigma) (dropFits (C ∷ []) fits)))))
      (λ sigma tau fitsEq ->
        packClosedEqSubst fitsEq
          (subst
            (λ J -> Computable J)
            (cong₃ (termEq [])
              (sym (subTmWkBy sigma 1 t))
              (sym (subTmWkBy tau 1 t))
              (sym (subTyWkBy sigma 1 B)))
            (ClosedEqSubstComp.closedEqComp
              (subEq
                (dropSubstBy 1 sigma)
                (dropSubstBy 1 tau)
                (dropFitsEq (C ∷ []) fitsEq)))))

  weakenOneOpenTmEq : {A B C : RawType} {t u : RawTerm}
    -> Computable (termEq (A ∷ []) t u B)
    -> CtxWF (C ∷ A ∷ [])
    -> Computable (termEq (C ∷ A ∷ []) (wkTmBy 1 t) (wkTmBy 1 u) (wkTyBy 1 B))
  weakenOneOpenTmEq {A = A} {B = B} {C = C} {t = t} {u = u}
    (compTmEqOpen neq d compt sub subEq) wf =
    compTmEqOpen
      nonemptyNeNil
      (weakenTmEq {gamma = A ∷ []} {delta = C ∷ []} d wf)
      (weakenOneOpenTm compt wf)
      (λ sigma fits ->
        packClosedSubst fits
          (subst
            (λ J -> Computable J)
            (cong₃ (termEq [])
              (sym (subTmWkBy sigma 1 t))
              (sym (subTmWkBy sigma 1 u))
              (sym (subTyWkBy sigma 1 B)))
            (ClosedSubstComp.closedComp
              (sub (dropSubstBy 1 sigma) (dropFits (C ∷ []) fits)))))
      (λ sigma tau fitsEq ->
        packClosedEqSubst fitsEq
          (subst
            (λ J -> Computable J)
            (cong₃ (termEq [])
              (sym (subTmWkBy sigma 1 t))
              (sym (subTmWkBy tau 1 u))
              (sym (subTyWkBy sigma 1 B)))
            (ClosedEqSubstComp.closedEqComp
              (subEq
                (dropSubstBy 1 sigma)
                (dropSubstBy 1 tau)
                (dropFitsEq (C ∷ []) fitsEq)))))

  compSubst : {gamma : Ctx} {J : JForm} {sigma : Subst}
    -> Computable J
    -> FitsSubst gamma (ctxOf J) sigma
    -> Computable (subJInto gamma sigma J)
  compSubst {gamma = []} {J = isType delta A} comp fits =
    substTyClosed (compToDerivable comp) fits
  compSubst {gamma = []} {J = typeEq delta A B} comp fits =
    substTyEqClosed (compToDerivable comp) fits
  compSubst {gamma = []} {J = hasTy delta t A} comp fits =
    substTmClosed (compToDerivable comp) fits
  compSubst {gamma = []} {J = termEq delta t u A} comp fits =
    substTmEqClosed (compToDerivable comp) fits
  compSubst {gamma = B ∷ gamma} {J = isType delta A} comp fits =
    openCompTy (substTyRule (compToDerivable comp) fits)
  compSubst {gamma = B ∷ gamma} {J = typeEq delta A C} comp fits =
    openCompTyEq (substTyEqRule (compToDerivable comp) fits)
  compSubst {gamma = B ∷ gamma} {J = hasTy delta t A} comp fits =
    openCompTm (substTmRule (compToDerivable comp) fits)
  compSubst {gamma = B ∷ gamma} {J = termEq delta t u A} comp fits =
    openCompTmEq (substTmEqRule (compToDerivable comp) fits)

  compEqSubst : {gamma : Ctx} {J : JForm} {sigma tau : Subst}
    -> Computable J
    -> FitsEqSubst gamma (ctxOf J) sigma tau
    -> Computable (eqSubJInto gamma sigma tau J)
  compEqSubst {gamma = []} {J = isType delta A} comp fitsEq =
    eqSubTyClosed (compToDerivable comp) fitsEq
  compEqSubst {gamma = []} {J = typeEq delta A B} comp fitsEq =
    eqSubTyEqClosed (compToDerivable comp) fitsEq
  compEqSubst {gamma = []} {J = hasTy delta t A} comp fitsEq =
    eqSubTmClosed (compToDerivable comp) fitsEq
  compEqSubst {gamma = []} {J = termEq delta t u A} comp fitsEq =
    eqSubTmEqClosed (compToDerivable comp) fitsEq
  compEqSubst {gamma = B ∷ gamma} {J = isType delta A} comp fitsEq =
    openCompTyEq (eqSubTyRule (compToDerivable comp) fitsEq)
  compEqSubst {gamma = B ∷ gamma} {J = typeEq delta A C} comp fitsEq =
    openCompTyEq (eqSubTyEqRule (compToDerivable comp) fitsEq)
  compEqSubst {gamma = B ∷ gamma} {J = hasTy delta t A} comp fitsEq =
    openCompTmEq (eqSubTmRule (compToDerivable comp) fitsEq)
  compEqSubst {gamma = B ∷ gamma} {J = termEq delta t u A} comp fitsEq =
    openCompTmEq (eqSubTmEqRule (compToDerivable comp) fitsEq)

  compConvTmClosedAcc : {t : RawTerm} {A B : RawType}
    -> Computable (hasTy [] t A)
    -> Computable (typeEq [] A B)
    -> Acc _<_ (closedTaskMeasure A)
    -> Computable (hasTy [] t B)
  compConvTmClosedAcc comp (compTyEqClosedTop dAB compA compB evA evB) (acc rs) =
    let
      inv = invertTopTm comp evA
      open ClosedTopTmInv inv
      tyInv = invertTopTy (compTmToCompTy comp) evA
      open ClosedTopTyInv tyInv
      topEqB = transTy (symTy topTyCorr) dAB
    in
    compTmClosedTop
      (conv (compToDerivable comp) dAB)
      compB
      evB
      topTmEvalStar
      (convEq topTmCorrStar topEqB)
  compConvTmClosedAcc
    comp
    (compTyEqClosedSigma {C = C} {D = D} dAB compA compB evA evB compCE dDF)
    (acc rs) =
    let
      inv = invertSigmaTm comp evA
      open ClosedSigmaTmInv inv
      tyInv = invertSigmaTy (compTmToCompTy comp) evA
      open ClosedSigmaTyInv tyInv
      sigmaEqB = transTy (symTy sigmaTyCorr) dAB
      acFst =
        rs _ (rewriteClosedUpper {H = tySigma C D} (evalSigmaPath evA)
          (smallerClosedTask<ClosedTask {A = C} {B = tySigma C D}
            (tyDepth-fst<Sigma C D)))
      acSnd =
        rs _ (rewriteClosedUpper {H = tySigma C D} (evalSigmaPath evA)
          (smallerClosedTask<ClosedTask
            {A = subTy (singleSubst sigmaTmFst) D} {B = tySigma C D}
            (subTySigmaFamilyDepth< (singleSubst sigmaTmFst) C D)))
      compaE = compConvTmClosedAcc sigmaTmCompFst compCE acFst
      compDFa = compSingleSubstTyEqClosed (hypComputableTyEq dDF) sigmaTmCompFst
      compbF = compConvTmClosedAcc sigmaTmCompSnd compDFa acSnd
    in
    compTmClosedSigma
      (conv sigmaTmDeriv sigmaEqB)
      compB
      evB
      sigmaTmEvalPair
      (convEq sigmaTmCorrPair sigmaEqB)
      compaE
      compbF
  compConvTmClosedAcc
    comp
    (compTyEqClosedEq {C = C} {a = a} {b = b} dAB compA compB evA evB compCD compac compbd)
    (acc rs) =
    let
      inv = invertEqTm comp evA
      open ClosedEqTmInv inv
      tyInv = invertEqTy (compTmToCompTy comp) evA
      open ClosedEqTyInv tyInv
      eqEqB = transTy (symTy eqTyCorr) dAB
      acBaseClosed =
        rs _ (rewriteClosedUpper {H = tyEq C a b} (evalEqPath evA)
          (smallerClosedTask<ClosedTask {A = C} {B = tyEq C a b}
            (tyDepth-base<Eq C a b)))
      acBaseOpen =
        rs _ (rewriteClosedUpper {H = tyEq C a b} (evalEqPath evA)
          (smallerOpenTask<ClosedTask {A = C} {B = tyEq C a b}
            (tyDepth-base<Eq C a b)))
      compcdC =
        compTransTmClosedAcc
          (compTransTmClosedAcc (compSymTmClosedAcc compac acBaseClosed) eqTmCompInner acBaseClosed)
          compbd
          acBaseClosed
      compcdD = compConvTmEqClosedAcc compcdC compCD acBaseOpen
    in
    compTmClosedEq
      (conv eqTmDeriv eqEqB)
      compB
      evB
      eqTmEvalRhs
      (convEq eqTmCorrRhs eqEqB)
      compcdD
  compConvTmClosedAcc
    comp
    (compTyEqClosedQtr {C = C} dAB compA compB evA evB compCD)
    (acc rs) =
    let
      inv = invertQtrTm comp evA
      open ClosedQtrTmInv inv
      tyInv = invertQtrTy (compTmToCompTy comp) evA
      open ClosedQtrTyInv tyInv
      qtrEqB = transTy (symTy qtrTyCorr) dAB
      acBase =
        rs _ (rewriteClosedUpper {H = tyQtr C} (evalQtrPath evA)
          (smallerClosedTask<ClosedTask {A = C} {B = tyQtr C}
            (tyDepth-base<Qtr C)))
      compaD = compConvTmClosedAcc qtrTmCompRepr compCD acBase
    in
    compTmClosedQtr
      (conv qtrTmDeriv qtrEqB)
      compB
      evB
      qtrTmEvalClass
      (convEq qtrTmCorrClass qtrEqB)
      compaD

  compConvTmEqClosedAcc : {t u : RawTerm} {A B : RawType}
    -> Computable (termEq [] t u A)
    -> Computable (typeEq [] A B)
    -> Acc _<_ (openTaskMeasure A)
    -> Computable (termEq [] t u B)
  compConvTmEqClosedAcc
    {t = t} {u = u} {A = A} {B = B}
    comp
    compAB@(compTyEqClosedTop dAB compA compB evA evB)
    (acc rs) =
    let
      comp' =
        subst
          (λ X -> Computable (termEq [] t u X))
          (evalTopPath evA)
          comp
      inv = invertTopTmEq0 comp'
      open ClosedTopTmEqInv inv
      compAB' = subst (λ X -> Computable (typeEq [] X B)) (evalTopPath evA) compAB
      acSame = rs _ (rewriteOpenUpper {A = A} {H = tyTop} (evalTopPath evA) (closedTask<openTask tyTop))
    in
    compTmEqClosedTop
      (convEq topTmEqDeriv (compToDerivable compAB'))
      (compConvTmClosedAcc topTmEqCompLeft compAB' acSame)
      (compConvTmClosedAcc topTmEqCompRight compAB' acSame)
      evB
      topTmEqEvalLeftStar
      topTmEqEvalRightStar
  compConvTmEqClosedAcc
    {t = t} {u = u} {A = A} {B = B}
    comp
    compAB@(compTyEqClosedSigma {C = C} {D = D} dAB compA compB evA evB compCE dDF)
    (acc rs) =
    let
      comp' =
        subst
          (λ X -> Computable (termEq [] t u X))
          (evalSigmaPath evA)
          comp
      inv = invertSigmaTmEq0 comp'
      open ClosedSigmaTmEqInv inv
      compA' =
        subst
          (λ X -> Computable (isType [] X))
          (evalSigmaPath evA)
          compA
      tyInv = invertSigmaTy compA' evalSigma
      open ClosedSigmaTyInv tyInv
      compAB' = subst (λ X -> Computable (typeEq [] X B)) (evalSigmaPath evA) compAB
      compLeftA : Computable (hasTy [] t (tySigma C D))
      compLeftA = sigmaTmEqCompLeft
      compRightA : Computable (hasTy [] u (tySigma C D))
      compRightA = sigmaTmEqCompRight
      acSame =
        rs _ (rewriteOpenUpper {A = A} {H = tySigma C D} (evalSigmaPath evA)
          (closedTask<openTask (tySigma C D)))
      acFst =
        rs _ (rewriteOpenUpper {A = A} {H = tySigma C D} (evalSigmaPath evA)
          (smallerOpenTask<OpenTask {A = C} {B = tySigma C D}
            (tyDepth-fst<Sigma C D)))
      acSnd =
        rs _ (rewriteOpenUpper {A = A} {H = tySigma C D} (evalSigmaPath evA)
          (smallerOpenTask<OpenTask
            {A = subTy (singleSubst sigmaTmEqLeftFst) D} {B = tySigma C D}
            (subTySigmaFamilyDepth< (singleSubst sigmaTmEqLeftFst) C D)))
      compLeftB = compConvTmClosedAcc compLeftA compAB' acSame
      compRightB = compConvTmClosedAcc compRightA compAB' acSame
      compFstE = compConvTmEqClosedAcc sigmaTmEqCompFst compCE acFst
      compDFa = compSingleSubstTyEqClosed (hypComputableTyEq dDF) (compTmEqLeft sigmaTmEqCompFst)
      compSndF = compConvTmEqClosedAcc sigmaTmEqCompSnd compDFa acSnd
    in
    compTmEqClosedSigma
      (convEq sigmaTmEqDeriv (compToDerivable compAB'))
      compLeftB
      compRightB
      evB
      sigmaTmEqEvalLeftPair
      sigmaTmEqEvalRightPair
      compFstE
      compSndF
  compConvTmEqClosedAcc
    {t = t} {u = u} {A = A} {B = B}
    comp
    compAB@(compTyEqClosedEq {C = C} {a = a} {b = b} dAB compA compB evA evB compCD compac compbd)
    (acc rs) =
    let
      comp' =
        subst
          (λ X -> Computable (termEq [] t u X))
          (evalEqPath evA)
          comp
      inv = invertEqTmEq0 comp'
      open ClosedEqTmEqInv inv
      compA' =
        subst
          (λ X -> Computable (isType [] X))
          (evalEqPath evA)
          compA
      tyInv = invertEqTy compA' evalEq
      open ClosedEqTyInv tyInv
      compAB' = subst (λ X -> Computable (typeEq [] X B)) (evalEqPath evA) compAB
      compLeftA : Computable (hasTy [] t (tyEq C a b))
      compLeftA = eqTmEqCompLeft
      compRightA : Computable (hasTy [] u (tyEq C a b))
      compRightA = eqTmEqCompRight
      acSame =
        rs _ (rewriteOpenUpper {A = A} {H = tyEq C a b} (evalEqPath evA)
          (closedTask<openTask (tyEq C a b)))
      acBaseClosed =
        rs _ (rewriteOpenUpper {A = A} {H = tyEq C a b} (evalEqPath evA)
          (smallerClosedTask<OpenTask {A = C} {B = tyEq C a b}
            (tyDepth-base<Eq C a b)))
      acBaseOpen =
        rs _ (rewriteOpenUpper {A = A} {H = tyEq C a b} (evalEqPath evA)
          (smallerOpenTask<OpenTask {A = C} {B = tyEq C a b}
            (tyDepth-base<Eq C a b)))
      compLeftB = compConvTmClosedAcc compLeftA compAB' acSame
      compRightB = compConvTmClosedAcc compRightA compAB' acSame
      compcdC =
        compTransTmClosedAcc
          (compTransTmClosedAcc (compSymTmClosedAcc compac acBaseClosed) eqTmEqCompInner acBaseClosed)
          compbd
          acBaseClosed
      compcdD = compConvTmEqClosedAcc compcdC compCD acBaseOpen
    in
    compTmEqClosedEq
      (convEq eqTmEqDeriv (compToDerivable compAB'))
      compLeftB
      compRightB
      evB
      eqTmEqEvalLeftR
      eqTmEqEvalRightR
      compcdD
  compConvTmEqClosedAcc
    {t = t} {u = u} {A = A} {B = B}
    comp
    compAB@(compTyEqClosedQtr {C = C} dAB compA compB evA evB compCD)
    (acc rs) =
    let
      comp' =
        subst
          (λ X -> Computable (termEq [] t u X))
          (evalQtrPath evA)
          comp
      inv = invertQtrTmEq0 comp'
      open ClosedQtrTmEqInv inv
      compA' =
        subst
          (λ X -> Computable (isType [] X))
          (evalQtrPath evA)
          compA
      tyInv = invertQtrTy compA' evalQtr
      open ClosedQtrTyInv tyInv
      compAB' = subst (λ X -> Computable (typeEq [] X B)) (evalQtrPath evA) compAB
      compLeftA : Computable (hasTy [] t (tyQtr C))
      compLeftA = qtrTmEqCompLeft
      compRightA : Computable (hasTy [] u (tyQtr C))
      compRightA = qtrTmEqCompRight
      acSame =
        rs _ (rewriteOpenUpper {A = A} {H = tyQtr C} (evalQtrPath evA)
          (closedTask<openTask (tyQtr C)))
      acBase =
        rs _ (rewriteOpenUpper {A = A} {H = tyQtr C} (evalQtrPath evA)
          (smallerClosedTask<OpenTask {A = C} {B = tyQtr C}
            (tyDepth-base<Qtr C)))
      compLeftB = compConvTmClosedAcc compLeftA compAB' acSame
      compRightB = compConvTmClosedAcc compRightA compAB' acSame
      compaD = compConvTmClosedAcc qtrTmEqCompLeftRepr compCD acBase
      compbD = compConvTmClosedAcc qtrTmEqCompRightRepr compCD acBase
    in
    compTmEqClosedQtr
      (convEq qtrTmEqDeriv (compToDerivable compAB'))
      compLeftB
      compRightB
      evB
      qtrTmEqEvalLeftClass
      qtrTmEqEvalRightClass
      compaD
      compbD

  compSymTmClosedAcc : {t u : RawTerm} {A : RawType}
    -> Computable (termEq [] t u A)
    -> Acc _<_ (closedTaskMeasure A)
    -> Computable (termEq [] u t A)
  compSymTmClosedAcc (compTmEqClosedTop d compt compu evA evt evu) (acc rs) =
    compTmEqClosedTop (symTm d) compu compt evA evu evt
  compSymTmClosedAcc
    comp@(compTmEqClosedSigma {a = a} {A = B} {B = C} d compt compu evA evt evu compac compbd)
    (acc rs) =
    let
      tyInv = invertSigmaTy (compTmToCompTy compt) evA
      compB = hypComputableTy (ClosedSigmaTyInv.sigmaTyFamDeriv tyInv)
      acFst =
        rs _ (rewriteClosedUpper {H = tySigma B C} (evalSigmaPath evA)
          (smallerClosedTask<ClosedTask {A = B} {B = tySigma B C}
            (tyDepth-fst<Sigma B C)))
      acSndClosed =
        rs _ (rewriteClosedUpper {H = tySigma B C} (evalSigmaPath evA)
          (smallerClosedTask<ClosedTask
            {A = subTy (singleSubst a) C} {B = tySigma B C}
            (subTySigmaFamilyDepth< (singleSubst a) B C)))
      acSndOpen =
        rs _ (rewriteClosedUpper {H = tySigma B C} (evalSigmaPath evA)
          (smallerOpenTask<ClosedTask
            {A = subTy (singleSubst a) C} {B = tySigma B C}
            (subTySigmaFamilyDepth< (singleSubst a) B C)))
      compca = compSymTmClosedAcc compac acFst
      compdb = compSymTmClosedAcc compbd acSndClosed
      compBac = compSingleEqSubstTyClosed compB compac
      compdb' = compConvTmEqClosedAcc compdb compBac acSndOpen
    in
    compTmEqClosedSigma
      (symTm d)
      compu
      compt
      evA
      evu
      evt
      compca
      compdb'
  compSymTmClosedAcc (compTmEqClosedEq d compt compu evA evt evu compab) (acc rs) =
    compTmEqClosedEq
      (symTm d)
      compu
      compt
      evA
      evu
      evt
      compab
  compSymTmClosedAcc (compTmEqClosedQtr d compt compu evA evt evu compa compb) (acc rs) =
    compTmEqClosedQtr
      (symTm d)
      compu
      compt
      evA
      evu
      evt
      compb
      compa

  compTransTmClosedAcc : {t u v : RawTerm} {A : RawType}
    -> Computable (termEq [] t u A)
    -> Computable (termEq [] u v A)
    -> Acc _<_ (closedTaskMeasure A)
    -> Computable (termEq [] t v A)
  compTransTmClosedAcc (compTmEqClosedTop d₁ compt _ evA evt evu) comp₂ (acc rs) =
    let
      inv₂ = invertTopTmEq comp₂ evA
      open ClosedTopTmEqInv inv₂
    in
    compTmEqClosedTop
      (transTm d₁ (compToDerivable comp₂))
      compt
      (compTmEqRightClosed comp₂)
      evA
      evt
      topTmEqEvalRightStar
  compTransTmClosedAcc
    comp₁@(compTmEqClosedSigma {a = a} {b = b} {c = c} {d = d} {A = C} {B = D}
      d₁ compt _ evA evt evu compac compbd)
    comp₂
    (acc rs) =
    let
      inv₂ = invertSigmaTmEq comp₂ evA
      open ClosedSigmaTmEqInv inv₂
      tyInv = invertSigmaTy (compTmToCompTy compt) evA
      compB = hypComputableTy (ClosedSigmaTyInv.sigmaTyFamDeriv tyInv)
      pairEq = evalDetTm evu sigmaTmEqEvalLeftPair
      c≡left = tmPairInj₁ pairEq
      d≡left = tmPairInj₂ pairEq
      compce =
        subst
          (λ x -> Computable (termEq [] x sigmaTmEqRightFst C))
          (sym c≡left)
          sigmaTmEqCompFst
      compdfC =
        subst
          (λ x -> Computable (termEq [] x sigmaTmEqRightSnd (subTy (singleSubst c) D)))
          (sym d≡left)
          (subst
            (λ T -> Computable (termEq [] sigmaTmEqLeftSnd sigmaTmEqRightSnd T))
            (cong (λ x -> subTy (singleSubst x) D) (sym c≡left))
            sigmaTmEqCompSnd)
      acFst =
        rs _ (rewriteClosedUpper {H = tySigma C D} (evalSigmaPath evA)
          (smallerClosedTask<ClosedTask {A = C} {B = tySigma C D}
            (tyDepth-fst<Sigma C D)))
      acSndCOpen =
        rs _ (rewriteClosedUpper {H = tySigma C D} (evalSigmaPath evA)
          (smallerOpenTask<ClosedTask
            {A = subTy (singleSubst c) D} {B = tySigma C D}
            (subTySigmaFamilyDepth< (singleSubst c) C D)))
      acSndAClosed =
        rs _ (rewriteClosedUpper {H = tySigma C D} (evalSigmaPath evA)
          (smallerClosedTask<ClosedTask
            {A = subTy (singleSubst a) D} {B = tySigma C D}
            (subTySigmaFamilyDepth< (singleSubst a) C D)))
      compae = compTransTmClosedAcc compac compce acFst
      compDca = compSingleEqSubstTyClosed compB (compSymTmClosedAcc compac acFst)
      compdfA = compConvTmEqClosedAcc compdfC compDca acSndCOpen
      compbf = compTransTmClosedAcc compbd compdfA acSndAClosed
    in
    compTmEqClosedSigma
      (transTm d₁ (compToDerivable comp₂))
      compt
      (compTmEqRightClosed comp₂)
      evA
      evt
      sigmaTmEqEvalRightPair
      compae
      compbf
  compTransTmClosedAcc comp₁@(compTmEqClosedEq d₁ compt _ evA evt evu compab) comp₂ (acc rs) =
    let
      inv₂ = invertEqTmEq comp₂ evA
      open ClosedEqTmEqInv inv₂
    in
    compTmEqClosedEq
      (transTm d₁ (compToDerivable comp₂))
      compt
      (compTmEqRightClosed comp₂)
      evA
      evt
      eqTmEqEvalRightR
      compab
  compTransTmClosedAcc comp₁@(compTmEqClosedQtr d₁ compt _ evA evt evu compa compb) comp₂ (acc rs) =
    let
      inv₂ = invertQtrTmEq comp₂ evA
      open ClosedQtrTmEqInv inv₂
    in
    compTmEqClosedQtr
      (transTm d₁ (compToDerivable comp₂))
      compt
      (compTmEqRightClosed comp₂)
      evA
      evt
      qtrTmEqEvalRightClass
      compa
      qtrTmEqCompRightRepr

  compConvTmClosed {A = A} comp compAB =
    compConvTmClosedAcc comp compAB (<-wellfounded (closedTaskMeasure A))

  compConvTmEqClosed {A = A} comp compAB =
    compConvTmEqClosedAcc comp compAB (<-wellfounded (openTaskMeasure A))

  compSymTmClosed {A = A} comp =
    compSymTmClosedAcc comp (<-wellfounded (closedTaskMeasure A))

  compTransTmClosed {A = A} comp₁ comp₂ =
    compTransTmClosedAcc comp₁ comp₂ (<-wellfounded (closedTaskMeasure A))

  compSymTyClosedAcc : {A B : RawType}
    -> Computable (typeEq [] A B)
    -> Acc _<_ (closedTaskMeasure A)
    -> Computable (typeEq [] B A)
  compSymTyClosedAcc (compTyEqClosedTop d compA compB evA evB) (acc rs) =
    compTyEqClosedTop (symTy d) compB compA evB evA
  compSymTyClosedAcc
    {A = AΣ}
    (compTyEqClosedSigma {C = C} {D = D} {E = E} {F = F} d compA compB evA evB compCE compDF)
    (acc rs) with compDF
  ... | compTyEqOpen {B = F} neq dDF compD subDF subEqDF =
    let
      acHead =
        rs _ (rewriteClosedUpper {H = tySigma C D} (evalSigmaPath evA)
          (smallerClosedTask<ClosedTask {A = C} {B = tySigma C D}
            (tyDepth-fst<Sigma C D)))
      dCE : Derivable (typeEq [] C E)
      dCE = compToDerivable compCE
      dRight : Derivable (isType [] E)
      dRight = compToDerivable (compTyEqRightClosed compCE)
      transportedEq : Derivable (typeEq (E ∷ []) D F)
      transportedEq = transportFamilyTyEq dCE dRight dDF
      transportFits : FitsSubst (E ∷ []) (C ∷ []) idSubst
      transportFits = headTypeTransportFits dCE dRight
      familyAcc : (sigma : Subst) -> Acc _<_ (closedTaskMeasure (subTy sigma D))
      familyAcc sigma =
        rs (closedTaskMeasure (subTy sigma D))
          (rewriteClosedUpper {A = AΣ} {H = tySigma C D} (evalSigmaPath evA)
            (smallerClosedTask<ClosedTask {A = subTy sigma D} {B = tySigma C D}
              (subTySigmaFamilyDepth< sigma C D)))
      familySym :
        (sigma : Subst) ->
        FitsSubst [] (E ∷ []) sigma ->
        Computable (typeEq [] (subTy sigma F) (subTy sigma D))
      familySym sigma fits =
        let
          closedσ =
            subst
              (λ J -> Computable J)
              (cong₂ (typeEq [])
                (sym (subTyComp sigma idSubst D) ∙ cong (subTy sigma) (subTyId D))
                (sym (subTyComp sigma idSubst F) ∙ cong (subTy sigma) (subTyId F)))
              (ClosedSubstComp.closedComp
                (subDF (compSub sigma idSubst) (composeFits fits transportFits)))
        in
        compSymTyClosedAcc closedσ (familyAcc sigma)
      familySymEq :
        (sigma tau : Subst) ->
        FitsEqSubst [] (E ∷ []) sigma tau ->
        Computable (typeEq [] (subTy sigma F) (subTy tau D))
      familySymEq sigma tau fitsEq =
        let
          closedσ =
            subst
              (λ J -> Computable J)
              (cong₂ (typeEq [])
                (sym (subTyComp sigma idSubst D) ∙ cong (subTy sigma) (subTyId D))
                (sym (subTyComp sigma idSubst F) ∙ cong (subTy sigma) (subTyId F)))
              (ClosedSubstComp.closedComp
                (subDF (compSub sigma idSubst) (composeFits (fitsEqSubstLeft fitsEq) transportFits)))
          closedστ =
            subst
              (λ J -> Computable J)
              (cong₂ (typeEq [])
                (sym (subTyComp sigma idSubst D) ∙ cong (subTy sigma) (subTyId D))
                (sym (subTyComp tau idSubst F) ∙ cong (subTy tau) (subTyId F)))
              (ClosedEqSubstComp.closedEqComp
                (subEqDF
                  (compSub sigma idSubst)
                  (compSub tau idSubst)
                  (composeEqFits fitsEq transportFits)))
          closedτ =
            subst
              (λ J -> Computable J)
              (cong₂ (typeEq [])
                (sym (subTyComp tau idSubst D) ∙ cong (subTy tau) (subTyId D))
                (sym (subTyComp tau idSubst F) ∙ cong (subTy tau) (subTyId F)))
              (ClosedSubstComp.closedComp
                (subDF
                  (compSub tau idSubst)
                  (composeFits
                    (fitsEqSubstRight (derivToCtxWF transportedEq) fitsEq)
                    transportFits)))
        in
        compTransTyClosed
          (compTransTyClosed
            (compSymTyClosedAcc closedσ (familyAcc sigma))
            closedστ)
          (compSymTyClosedAcc closedτ (familyAcc tau))
      familyTy :
        (sigma : Subst) ->
        FitsSubst [] (E ∷ []) sigma ->
        Computable (isType [] (subTy sigma F))
      familyTy sigma fits =
        compTyEqLeft (familySym sigma fits)
      familyTyEq :
        (sigma tau : Subst) ->
        FitsEqSubst [] (E ∷ []) sigma tau ->
        Computable (typeEq [] (subTy sigma F) (subTy tau F))
      familyTyEq sigma tau fitsEq =
        let
          closedτ =
            subst
              (λ J -> Computable J)
              (cong₂ (typeEq [])
                (sym (subTyComp tau idSubst D) ∙ cong (subTy tau) (subTyId D))
                (sym (subTyComp tau idSubst F) ∙ cong (subTy tau) (subTyId F)))
              (ClosedSubstComp.closedComp
                (subDF
                  (compSub tau idSubst)
                  (composeFits
                    (fitsEqSubstRight (derivToCtxWF transportedEq) fitsEq)
                    transportFits)))
        in
        compTransTyClosed
          (familySymEq sigma tau fitsEq)
          closedτ
    in
      compTyEqClosedSigma
        (symTy d)
        compB
        compA
        evB
        evA
        (compSymTyClosedAcc compCE acHead)
        (compSymTransportFamilyTyEq
          familyTy
          familyTyEq
          familySym
          familySymEq
          compCE
          compDF)
  compSymTyClosedAcc
    (compTyEqClosedEq {C = C} {a = a} {b = b} d compA compB evA evB compCD compac compbd)
    (acc rs) =
    let
      acBase =
        rs _ (rewriteClosedUpper {H = tyEq C a b} (evalEqPath evA)
          (smallerClosedTask<ClosedTask {A = C} {B = tyEq C a b}
            (tyDepth-base<Eq C a b)))
    in
    compTyEqClosedEq
      (symTy d)
      compB
      compA
      evB
      evA
      (compSymTyClosedAcc compCD acBase)
      (compConvTmEqClosed (compSymTmClosed compac) compCD)
      (compConvTmEqClosed (compSymTmClosed compbd) compCD)
  compSymTyClosedAcc
    (compTyEqClosedQtr {C = C} d compA compB evA evB compCD)
    (acc rs) =
    let
      acBase =
        rs _ (rewriteClosedUpper {H = tyQtr C} (evalQtrPath evA)
          (smallerClosedTask<ClosedTask {A = C} {B = tyQtr C}
            (tyDepth-base<Qtr C)))
    in
    compTyEqClosedQtr
      (symTy d)
      compB
      compA
      evB
      evA
      (compSymTyClosedAcc compCD acBase)
  compSymTyClosedAcc (compTyEqOpen neq _ _ _ _) _ = Empty.rec (neq refl)

  compTransTyClosedAcc : {A B C : RawType}
    -> Computable (typeEq [] A B)
    -> Computable (typeEq [] B C)
    -> Acc _<_ (closedTaskMeasure A)
    -> Computable (typeEq [] A C)
  compTransTyClosedAcc
    (compTyEqClosedTop dAB compA compB evA evB)
    (compTyEqClosedTop dBC _ compC evB' evC)
    (acc rs) =
    compTyEqClosedTop
      (transTy dAB dBC)
      compA
      compC
      evA
      evC
  compTransTyClosedAcc
    (compTyEqClosedTop _ _ _ _ evB)
    (compTyEqClosedSigma _ _ _ evB' _ _ _)
    _ =
    Empty.rec (topNeSigma (sym (evalTopPath evB) ∙ evalSigmaPath evB'))
  compTransTyClosedAcc
    (compTyEqClosedTop _ _ _ _ evB)
    (compTyEqClosedEq _ _ _ evB' _ _ _ _)
    _ =
    Empty.rec (topNeEq (sym (evalTopPath evB) ∙ evalEqPath evB'))
  compTransTyClosedAcc
    (compTyEqClosedTop _ _ _ _ evB)
    (compTyEqClosedQtr _ _ _ evB' _ _)
    _ =
    Empty.rec (topNeQtr (sym (evalTopPath evB) ∙ evalQtrPath evB'))
  compTransTyClosedAcc
    (compTyEqClosedTop _ _ _ _ _)
    (compTyEqOpen neq _ _ _ _)
    _ =
    Empty.rec (neq refl)
  compTransTyClosedAcc
    comp₁@(compTyEqClosedSigma {C = C} {D = D} dAB compA compB evA evB compCE compDF)
    comp₂
    (acc rs)
    with compDF
  ... | compTyEqOpen neq dDF compD subDF subEqDF =
    let
      inv₂ = invertSigmaTyEq comp₂ evB
      open ClosedSigmaTyEqInv inv₂
      acHead =
        rs _ (rewriteClosedUpper {H = tySigma C D} (evalSigmaPath evA)
          (smallerClosedTask<ClosedTask {A = C} {B = tySigma C D}
            (tyDepth-fst<Sigma C D)))
      compCG = compTransTyClosedAcc compCE sigmaTyEqCompHead acHead
      compGC = compSymTyClosedAcc compCE acHead
      compFH = compTransportFamilyTyEq compGC sigmaTyEqCompFam
    in
    case compFH of λ where
      (compTyEqOpen _ dFH _ subFH subEqFH) ->
        let
          compDH =
            compTransTyOpenHelper
              compTransTyClosed
              neq
              dDF
              compD
              subDF
              subEqDF
              dFH
              subFH
              subEqFH
        in
        compTyEqClosedSigma
          (transTy dAB (compToDerivable comp₂))
          compA
          sigmaTyEqCompRight
          evA
          sigmaTyEqEvalRight
          compCG
          compDH
  compTransTyClosedAcc
    (compTyEqClosedEq {C = C} {a = a} {b = b} dAB compA compB evA evB compCD compac compbd)
    comp₂
    (acc rs) =
    let
      inv₂ = invertEqTyEq comp₂ evB
      open ClosedEqTyEqInv inv₂
      acBase =
        rs _ (rewriteClosedUpper {H = tyEq C a b} (evalEqPath evA)
          (smallerClosedTask<ClosedTask {A = C} {B = tyEq C a b}
            (tyDepth-base<Eq C a b)))
      compDG = compTransTyClosedAcc compCD eqTyEqCompBase acBase
      compeRight = compConvTmEqClosed eqTyEqCompLeftTerm (compSymTyClosedAcc compCD acBase)
      compfRight = compConvTmEqClosed eqTyEqCompRightTerm (compSymTyClosedAcc compCD acBase)
      compae = compTransTmClosed compac compeRight
      compbf = compTransTmClosed compbd compfRight
    in
    compTyEqClosedEq
      (transTy dAB (compToDerivable comp₂))
      compA
      eqTyEqCompRight
      evA
      eqTyEqEvalRight
      compDG
      compae
      compbf
  compTransTyClosedAcc
    (compTyEqClosedQtr {C = C} dAB compA compB evA evB compCD)
    comp₂
    (acc rs) =
    let
      inv₂ = invertQtrTyEq comp₂ evB
      open ClosedQtrTyEqInv inv₂
      acBase =
        rs _ (rewriteClosedUpper {H = tyQtr C} (evalQtrPath evA)
          (smallerClosedTask<ClosedTask {A = C} {B = tyQtr C}
            (tyDepth-base<Qtr C)))
    in
    compTyEqClosedQtr
      (transTy dAB (compToDerivable comp₂))
      compA
      qtrTyEqCompRight
      evA
      qtrTyEqEvalRight
      (compTransTyClosedAcc compCD qtrTyEqCompBase acBase)
  compTransTyClosedAcc (compTyEqOpen neq _ _ _ _) _ _ = Empty.rec (neq refl)

  compSymTyClosed : {A B : RawType}
    -> Computable (typeEq [] A B)
    -> Computable (typeEq [] B A)
  compSymTyClosed {A = A} comp =
    compSymTyClosedAcc comp (<-wellfounded (closedTaskMeasure A))

  compTransTyClosed : {A B C : RawType}
    -> Computable (typeEq [] A B)
    -> Computable (typeEq [] B C)
    -> Computable (typeEq [] A C)
  compTransTyClosed {A = A} comp₁ comp₂ =
    compTransTyClosedAcc comp₁ comp₂ (<-wellfounded (closedTaskMeasure A))

  compTyEqRight : {gamma : Ctx} {A B : RawType}
    -> Computable (typeEq gamma A B)
    -> Computable (isType gamma B)
  compTyEqRight comp@(compTyEqClosedTop _ _ _ _ _) = compTyEqRightClosed comp
  compTyEqRight comp@(compTyEqClosedSigma _ _ _ _ _ _ _) = compTyEqRightClosed comp
  compTyEqRight comp@(compTyEqClosedEq _ _ _ _ _ _ _ _) = compTyEqRightClosed comp
  compTyEqRight comp@(compTyEqClosedQtr _ _ _ _ _ _) = compTyEqRightClosed comp
  compTyEqRight (compTyEqOpen neq d compA sub subEq) =
    compTyOpen
      neq
      (assocTyRight d)
      (λ sigma fits ->
        packClosedSubst fits
          (compTyEqRightClosed (ClosedSubstComp.closedComp (sub sigma fits))))
      (λ sigma tau fitsEq ->
        let
          closedσ = ClosedSubstComp.closedComp (sub sigma (fitsEqSubstLeft fitsEq))
          closedστ = ClosedEqSubstComp.closedEqComp (subEq sigma tau fitsEq)
        in
        packClosedEqSubst fitsEq
          (compTransTyClosed
            (compSymTyClosed closedσ)
            closedστ))

  computableTyClosed : {A : RawType}
    -> Derivable (isType [] A)
    -> Computable (isType [] A)
  computableTyClosed {A = A} d =
    subst
      (λ T -> Computable (isType [] T))
      (subTyId A)
      (substTyClosed d (fitsNil {gamma = []} {delta = []} {sigma = idSubst} wfNil))

  computableTyEqClosed : {A B : RawType}
    -> Derivable (typeEq [] A B)
    -> Computable (typeEq [] A B)
  computableTyEqClosed {A = A} {B = B} d =
    subst
      (λ J -> Computable J)
      (cong₂ (typeEq []) (subTyId A) (subTyId B))
      (substTyEqClosed d (fitsNil {gamma = []} {delta = []} {sigma = idSubst} wfNil))

  computableTmClosed : {t : RawTerm} {A : RawType}
    -> Derivable (hasTy [] t A)
    -> Computable (hasTy [] t A)
  computableTmClosed {t = t} {A = A} d =
    subst
      (λ J -> Computable J)
      (cong₂ (hasTy []) (subTmId t) (subTyId A))
      (substTmClosed d (fitsNil {gamma = []} {delta = []} {sigma = idSubst} wfNil))

  computableTmEqClosed : {t u : RawTerm} {A : RawType}
    -> Derivable (termEq [] t u A)
    -> Computable (termEq [] t u A)
  computableTmEqClosed {t = t} {u = u} {A = A} d =
    subst
      (λ J -> Computable J)
      (cong₃ (termEq []) (subTmId t) (subTmId u) (subTyId A))
      (substTmEqClosed d (fitsNil {gamma = []} {delta = []} {sigma = idSubst} wfNil))

CanonicalForm : JForm -> Type
CanonicalForm (isType [] A) =
  Σ[ G ∈ RawType ] (A =>t G) × Derivable (typeEq [] A G)
CanonicalForm (typeEq [] A B) =
  Σ[ G ∈ RawType ] Σ[ H ∈ RawType ] (A =>t G) × (B =>t H)
CanonicalForm (hasTy [] t A) =
  Σ[ g ∈ RawTerm ] Σ[ G ∈ RawType ] (t =>e g) × (A =>t G)
CanonicalForm (termEq [] t u A) =
  Σ[ g ∈ RawTerm ] Σ[ h ∈ RawTerm ] Σ[ G ∈ RawType ] (t =>e g) × (u =>e h) × (A =>t G)
CanonicalForm (isType (_ ∷ _) A) = Unit
CanonicalForm (typeEq (_ ∷ _) A B) = Unit
CanonicalForm (hasTy (_ ∷ _) t A) = Unit
CanonicalForm (termEq (_ ∷ _) t u A) = Unit

canonicalFormTheorem : {J : JForm} -> Derivable J -> CanonicalForm J
canonicalFormTheorem {J = isType [] A} d =
  canonicalType (computableTyClosed d)
canonicalFormTheorem {J = typeEq [] A B} d =
  canonicalTypeEq (computableTyEqClosed d)
canonicalFormTheorem {J = hasTy [] t A} d =
  canonicalTerm (computableTmClosed d)
canonicalFormTheorem {J = termEq [] t u A} d =
  canonicalTermEq (computableTmEqClosed d)
canonicalFormTheorem {J = isType (_ ∷ _) A} d = tt
canonicalFormTheorem {J = typeEq (_ ∷ _) A B} d = tt
canonicalFormTheorem {J = hasTy (_ ∷ _) t A} d = tt
canonicalFormTheorem {J = termEq (_ ∷ _) t u A} d = tt
