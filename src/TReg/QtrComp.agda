
{-# OPTIONS --safe #-}

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
       (termEq (wkTyBy 1 A ∷ A ∷ []) (wkTmBy 1 l) (renTm qtrSecondBranchRen l) (qtrCohTy L))
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
    (termEq (wkTyBy 1 A ∷ A ∷ []) (wkTmBy 1 l) (renTm qtrSecondBranchRen l) (qtrCohTy L))
  dcoh = compToDerivable coh

  fits : FitsSubst [] (A ∷ []) (qtrCompSub a)
  fits = compFitsToFits (qtrCompCompFitsHelper compa)

  rawBody : Computable
    (hasTy [] (subTm (qtrCompSub a) l) (subTy (qtrCompSub a) (qtrBranchTy L)))
  rawBody = ClosedSubstComp.closedComp (sub (qtrCompSub a) fits)

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

qtrCompCompFitsEqHelper : {A : RawType} {a b : RawTerm}
  -> Computable (termEq [] a b A)
  -> CompFitsEqSubst (A ∷ []) (qtrCompSub a) (qtrCompSub b)
qtrCompCompFitsEqHelper {A = A} {a = a} {b = b} compab =
  subst
    (λ sigma -> CompFitsEqSubst (A ∷ []) sigma (qtrCompSub b))
    (singleSubstConsKeep a ∙ cong (consSubst a) keepSubstBy0Id)
    (subst
      (λ tau -> CompFitsEqSubst (A ∷ []) (singleSubst a) tau)
      (singleSubstConsKeep b ∙ cong (consSubst b) keepSubstBy0Id)
      (singleCompFitsEqSubstHelper compab))

compEQtrClosed : {A L : RawType} {l l' p p' : RawTerm}
  -> Computable (isType ((tyQtr A) ∷ []) L)
  -> Computable (termEq [] p p' (tyQtr A))
  -> Computable (termEq (A ∷ []) l l' (qtrBranchTy L))
  -> Computable
       (termEq (wkTyBy 1 A ∷ A ∷ []) (wkTmBy 1 l) (renTm qtrSecondBranchRen l) (qtrCohTy L))
  -> Computable
       (termEq (wkTyBy 1 A ∷ A ∷ []) (wkTmBy 1 l') (renTm qtrSecondBranchRen l') (qtrCohTy L))
  -> Computable
       (termEq [] (tmElQtr l p) (tmElQtr l' p') (subTy (singleSubst p) L))
compEQtrClosed {A = A} {L = L} {l = l} {l' = l'} {p = p} {p' = p'}
  compL comppp'
  compll'@(compTmEqOpen neq dll' compBranchTy sub subEq)
  coh
  coh'@(compTmEqOpen neqCoh' dcoh'comp compCohTy' subCoh' subEqCoh') =
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
  dL = compToDerivable compL

  dl : Derivable (hasTy (A ∷ []) l (qtrBranchTy L))
  dl = assocTmLeft dll'

  dl' : Derivable (hasTy (A ∷ []) l' (qtrBranchTy L))
  dl' = assocTmRight dll'

  dcoh : Derivable
    (termEq (wkTyBy 1 A ∷ A ∷ []) (wkTmBy 1 l) (renTm qtrSecondBranchRen l) (qtrCohTy L))
  dcoh = compToDerivable coh

  dcoh' : Derivable
    (termEq (wkTyBy 1 A ∷ A ∷ []) (wkTmBy 1 l') (renTm qtrSecondBranchRen l') (qtrCohTy L))
  dcoh' = compToDerivable coh'

  da : Derivable (hasTy [] qtrTmEqLeftRepr A)
  da = compToDerivable qtrTmEqCompLeftRepr

  db : Derivable (hasTy [] qtrTmEqRightRepr A)
  db = compToDerivable qtrTmEqCompRightRepr

  dHeadTyEq : Derivable
    (typeEq [] A (subTy (qtrCompSub qtrTmEqLeftRepr) (wkTyBy 1 A)))
  dHeadTyEq =
    subst
      (λ T -> Derivable (typeEq [] A T))
      (sym
        (cong (subTy (qtrCompSub qtrTmEqLeftRepr)) (renTyKeepSubstBy 1 A)
          ∙ subTyComp (qtrCompSub qtrTmEqLeftRepr) (keepSubstBy 1) A
          ∙ cong (λ rho -> subTy rho A) (funExt λ n -> refl)
          ∙ subTyId A))
      (reflTy (assocTy db))

  dbOnHead : Derivable
    (hasTy [] qtrTmEqRightRepr (subTy (qtrCompSub qtrTmEqLeftRepr) (wkTyBy 1 A)))
  dbOnHead = conv db dHeadTyEq

  branchFitsLeft : FitsSubst [] (A ∷ []) (qtrCompSub qtrTmEqLeftRepr)
  branchFitsLeft = qtrCompFitsHelper da

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
      (ClosedSubstComp.closedComp
        (sub
          (qtrCompSub qtrTmEqLeftRepr)
          branchFitsLeft))

  cohFitsRight : FitsSubst [] (wkTyBy 1 A ∷ A ∷ [])
    (consSubst qtrTmEqRightRepr (consSubst qtrTmEqLeftRepr idSubst))
  cohFitsRight =
    fitsCons
      (qtrCompFitsHelper da)
      dbOnHead

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
          (ClosedSubstComp.closedComp
            (subCoh'
              (consSubst qtrTmEqRightRepr (consSubst qtrTmEqLeftRepr idSubst))
              cohFitsRight))))

  bodyEqClassA : Computable
    (termEq []
      (subTm (qtrCompSub qtrTmEqLeftRepr) l)
      (subTm (qtrCompSub qtrTmEqRightRepr) l')
      (subTy (singleSubst (tmClass qtrTmEqLeftRepr)) L))
  bodyEqClassA =
    compTransTmClosed branchEqClassA cohEqClassA

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
      (eQtrEq
        dL
        (compToDerivable compRightCorr)
        (reflTm dl')
        dcoh'
        dcoh')
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
  mkLeftCanon _ _ _ (compTmOpen neqBody _ _ _ _) = Empty.rec (neqBody refl)

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
  mkRightCanon _ _ _ (compTmOpen neqBody _ _ _ _) = Empty.rec (neqBody refl)

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
