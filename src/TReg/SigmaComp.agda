
{-# OPTIONS --safe #-}

module TReg.SigmaComp where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Empty.Base as Empty using (rec)
open import Cubical.Data.List.Base using ([] ; _∷_)

open import TReg.Syntax
open import TReg.Context
open import TReg.Substitution
open import TReg.Evaluation
open import TReg.Derivability
open import TReg.Computability
open import TReg.Inversion
open import TReg.Presupposition
open import TReg.Structural

compFSigmaClosed : {A B : RawType}
  -> Computable (isType [] A)
  -> Computable (isType (A ∷ []) B)
  -> Computable (isType [] (tySigma A B))
compFSigmaClosed compA compB =
  compTyClosedSigma
    (fSigma (compToDerivable compA) (compToDerivable compB))
    evalSigma
    (reflTy (fSigma (compToDerivable compA) (compToDerivable compB)))
    compA
    compB

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
  -> Computable (isType ((tySigma A B) ∷ []) M)
  -> Computable (hasTy [] b A)
  -> Computable (hasTy [] c (subTy (singleSubst b) B))
  -> Computable (hasTy (B ∷ A ∷ []) m (sigmaBranchTy M))
  -> Computable
       (termEq [] (tmElSigma (tmPair b c) m) (subTm (sigmaCompSub b c) m)
         (subTy (singleSubst (tmPair b c)) M))
compCSigmaClosed {b = b} {c = c} {m = m} {A = A} {B = B} {M = M}
  compM compb compc compm@(compTmOpen neq dm compBranchTy sub subEq) =
  lhsEq body
  where
  db : Derivable (hasTy [] b A)
  db = compToDerivable compb

  dc : Derivable (hasTy [] c (subTy (singleSubst b) B))
  dc = compToDerivable compc

  dM : Derivable (isType ((tySigma A B) ∷ []) M)
  dM = compToDerivable compM

  fits : FitsSubst [] (B ∷ A ∷ []) (sigmaCompSub b c)
  fits = compFitsToFits (sigmaCompCompFitsHelper compb compc)

  rawBody : Computable
    (hasTy [] (subTm (sigmaCompSub b c) m) (subTy (sigmaCompSub b c) (sigmaBranchTy M)))
  rawBody = ClosedSubstComp.closedComp (sub (sigmaCompSub b c) fits)

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

  lhsEq : Computable
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
  lhsEq (compTmOpen neqBody _ _ _ _) = Empty.rec (neqBody refl)

sigmaCompCompFitsEqHelper : {A B : RawType} {b c e f : RawTerm}
  -> Computable (termEq [] b e A)
  -> Computable (termEq [] c f (subTy (singleSubst b) B))
  -> CompFitsEqSubst (B ∷ A ∷ []) (sigmaCompSub b c) (sigmaCompSub e f)
sigmaCompCompFitsEqHelper {A = A} {B = B} {b = b} {c = c} {e = e} {f = f} compbe compcf =
  subst
    (λ sigma -> CompFitsEqSubst (B ∷ A ∷ []) sigma (sigmaCompSub e f))
    (cong (consSubst c) (singleSubstConsKeep b ∙ cong (consSubst b) keepSubstBy0Id))
    (subst
      (λ tau -> CompFitsEqSubst (B ∷ A ∷ []) (consSubst c (singleSubst b)) tau)
      (cong (consSubst f) (singleSubstConsKeep e ∙ cong (consSubst e) keepSubstBy0Id))
      (compFitsEqCons
        (singleCompFitsEqSubstHelper compbe)
        compcf))

compESigmaClosed : {A B M : RawType} {d d' m m' : RawTerm}
  -> Computable (isType ((tySigma A B) ∷ []) M)
  -> Computable (termEq [] d d' (tySigma A B))
  -> Computable (termEq (B ∷ A ∷ []) m m' (sigmaBranchTy M))
  -> Computable
       (termEq [] (tmElSigma d m) (tmElSigma d' m') (subTy (singleSubst d) M))
compESigmaClosed {A = A} {B = B} {M = M} {d = d} {d' = d'} {m = m} {m' = m'}
  compM compdd'
  compmm'@(compTmEqOpen neq dmm' compBranchTy sub subEq) =
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

  branchFitsEq : FitsEqSubst [] (B ∷ A ∷ [])
    (sigmaCompSub sigmaTmEqLeftFst sigmaTmEqLeftSnd)
    (sigmaCompSub sigmaTmEqRightFst sigmaTmEqRightSnd)
  branchFitsEq =
    compFitsEqToFitsEq
      (sigmaCompCompFitsEqHelper sigmaTmEqCompFst sigmaTmEqCompSnd)

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
      (ClosedEqSubstComp.closedEqComp
        (subEq
          (sigmaCompSub sigmaTmEqLeftFst sigmaTmEqLeftSnd)
          (sigmaCompSub sigmaTmEqRightFst sigmaTmEqRightSnd)
          branchFitsEq))

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
  dM = compToDerivable compM

  dm : Derivable (hasTy (B ∷ A ∷ []) m (sigmaBranchTy M))
  dm = assocTmLeft dmm'

  dm' : Derivable (hasTy (B ∷ A ∷ []) m' (sigmaBranchTy M))
  dm' = assocTmRight dmm'

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
  dLeftStep =
    eSigmaEq dM sigmaTmEqLeftCorrPair (reflTm dm)

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
  mkLeftCanon _ _ _ (compTmOpen neqBody _ _ _ _) = Empty.rec (neqBody refl)

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
  mkRightCanon _ _ _ (compTmOpen neqBody _ _ _ _) = Empty.rec (neqBody refl)

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
