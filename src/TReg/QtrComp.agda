{-# OPTIONS --cubical --guardedness #-}

module TReg.QtrComp where

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
  -> Computable (isType ((tyQtr A) ∷ []) L)
  -> Computable (hasTy [] a A)
  -> Computable (hasTy (A ∷ []) l (qtrBranchTy L))
  -> Computable
       (termEq (A ∷ A ∷ []) (wkTmBy 1 l) (renTm qtrSecondBranchRen l) (qtrCohTy L))
  -> Computable
       (termEq [] (tmElQtr l (tmClass a)) (subTm (qtrCompSub a) l)
         (subTy (singleSubst (tmClass a)) L))
compCQtrClosed {a = a} {l = l} {A = A} {L = L}
  compL compa compl@(compTmOpen neq dl compBranchTy sub subEq) coh =
  lhsEq body
  where
  dL : Derivable (isType ((tyQtr A) ∷ []) L)
  dL = compToDerivable compL

  da : Derivable (hasTy [] a A)
  da = compToDerivable compa

  dcoh : Derivable
    (termEq (A ∷ A ∷ []) (wkTmBy 1 l) (renTm qtrSecondBranchRen l) (qtrCohTy L))
  dcoh = compToDerivable coh

  fits : FitsSubst [] (A ∷ []) (qtrCompSub a)
  fits = compFitsToFits (qtrCompCompFitsHelper compa)

  closed : ClosedSubstComp (A ∷ []) (qtrCompSub a)
    (hasTy [] (subTm (qtrCompSub a) l) (subTy (qtrCompSub a) (qtrBranchTy L)))
  closed = sub (qtrCompSub a) fits

  rawBody : Computable
    (hasTy [] (subTm (qtrCompSub a) l) (subTy (qtrCompSub a) (qtrBranchTy L)))
  rawBody = closedSubstCompBody closed

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

  lhsEq : Computable
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
  lhsEq (compTmOpen neqBody _ _ _ _) = Empty.rec (neqBody refl)
