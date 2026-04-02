{-# OPTIONS --safe --cubical #-}

module TReg.Structural where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Empty.Base as Empty using (rec)
open import Cubical.Data.List.Base using ([] ; _∷_)
open import Cubical.Data.Nat.Order using (_<_ ; <-wellfounded)
open import Cubical.Data.Sigma using (Σ ; _,_ ; fst ; snd)
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
open import TReg.StructuralBase public

compTyEqRightClosed : {A B : RawType}
  -> Computable (typeEq [] A B)
  -> Computable (isType [] B)
compTyEqRightClosed (compTyEqClosedTop _ _ compB _ _) = compB
compTyEqRightClosed (compTyEqClosedSigma _ _ compB _ _ _ _) = compB
compTyEqRightClosed (compTyEqClosedEq _ _ compB _ _ _ _ _) = compB
compTyEqRightClosed (compTyEqClosedQtr _ _ compB _ _ _) = compB

compTmEqRightClosed : {t u : RawTerm} {A : RawType}
  -> Computable (termEq [] t u A)
  -> Computable (hasTy [] u A)
compTmEqRightClosed (compTmEqClosedTop _ _ compu _ _ _) = compu
compTmEqRightClosed (compTmEqClosedSigma _ _ compu _ _ _ _ _) = compu
compTmEqRightClosed (compTmEqClosedEq _ _ compu _ _ _ _) = compu
compTmEqRightClosed (compTmEqClosedQtr _ _ compu _ _ _ _ _) = compu

mutual
  compReflTyClosedAcc : {A : RawType}
    -> Computable (isType [] A)
    -> Acc _<_ (closedTaskMeasure A)
    -> Computable (typeEq [] A A)
  compReflTyClosedAcc comp@(compTyClosedTop d ev corr) (acc rs) =
    compTyEqClosedTop (reflTy d) comp comp ev ev
  compReflTyClosedAcc
    comp@(compTyClosedSigma {B = B} {C = C} d ev corr compA dC)
    (acc rs) =
    let
      acHead =
        rs _ (rewriteClosedUpper {H = tySigma B C} (evalSigmaPath ev)
          (smallerClosedTask<ClosedTask {A = B} {B = tySigma B C}
            (tyDepth-fst<Sigma B C)))
    in
    compTyEqClosedSigma
      (reflTy d)
      comp
      comp
      ev
      ev
      (compReflTyClosedAcc compA acHead)
      (reflTy dC)
  compReflTyClosedAcc
    comp@(compTyClosedEq {B = B} {a = a} {b = b} d ev corr compA compa compb)
    (acc rs) =
    let
      acBase =
        rs _ (rewriteClosedUpper {H = tyEq B a b} (evalEqPath ev)
          (smallerClosedTask<ClosedTask {A = B} {B = tyEq B a b}
            (tyDepth-base<Eq B a b)))
    in
    compTyEqClosedEq
      (reflTy d)
      comp
      comp
      ev
      ev
      (compReflTyClosedAcc compA acBase)
      (compReflTmClosedAcc compa acBase)
      (compReflTmClosedAcc compb acBase)
  compReflTyClosedAcc comp@(compTyClosedQtr {B = B} d ev corr compA) (acc rs) =
    let
      acBase =
        rs _ (rewriteClosedUpper {H = tyQtr B} (evalQtrPath ev)
          (smallerClosedTask<ClosedTask {A = B} {B = tyQtr B}
            (tyDepth-base<Qtr B)))
    in
    compTyEqClosedQtr
      (reflTy d)
      comp
      comp
      ev
      ev
      (compReflTyClosedAcc compA acBase)

  compReflTmClosedAcc : {t : RawTerm} {A : RawType}
    -> Computable (hasTy [] t A)
    -> Acc _<_ (closedTaskMeasure A)
    -> Computable (termEq [] t t A)
  compReflTmClosedAcc comp@(compTmClosedTop d compA evA evt corr) (acc rs) =
    compTmEqClosedTop (reflTm d) comp comp evA evt evt
  compReflTmClosedAcc
    comp@(compTmClosedSigma {a = a} {A = B} {B = C} d compA evA evt corr compa compb)
    (acc rs) =
    let
      acFst =
        rs _ (rewriteClosedUpper {H = tySigma B C} (evalSigmaPath evA)
          (smallerClosedTask<ClosedTask {A = B} {B = tySigma B C}
            (tyDepth-fst<Sigma B C)))
      acSnd =
        rs _ (rewriteClosedUpper {H = tySigma B C} (evalSigmaPath evA)
          (smallerClosedTask<ClosedTask {A = subTy (singleSubst a) C} {B = tySigma B C}
            (subTySigmaFamilyDepth< (singleSubst a) B C)))
    in
    compTmEqClosedSigma
      (reflTm d)
      comp
      comp
      evA
      evt
      evt
      (compReflTmClosedAcc compa acFst)
      (compReflTmClosedAcc compb acSnd)
  compReflTmClosedAcc comp@(compTmClosedEq d compA evA evt corr compEq) (acc rs) =
    compTmEqClosedEq
      (reflTm d)
      comp
      comp
      evA
      evt
      evt
      compEq
  compReflTmClosedAcc comp@(compTmClosedQtr d compA evA evt corr compa) (acc rs) =
    compTmEqClosedQtr
      (reflTm d)
      comp
      comp
      evA
      evt
      evt
      compa
      compa

compReflTyClosed : {A : RawType}
  -> Computable (isType [] A)
  -> Computable (typeEq [] A A)
compReflTyClosed {A = A} comp =
  compReflTyClosedAcc comp (<-wellfounded (closedTaskMeasure A))

compReflTmClosed : {t : RawTerm} {A : RawType}
  -> Computable (hasTy [] t A)
  -> Computable (termEq [] t t A)
compReflTmClosed {A = A} comp =
  compReflTmClosedAcc comp (<-wellfounded (closedTaskMeasure A))

singleComputableFitsSubstHelper : {A : RawType} {t : RawTerm}
  -> Computable (hasTy [] t A)
  -> Σ (FitsSubst [] (A ∷ []) (singleSubst t)) (λ fits -> ComputableFits fits)
singleComputableFitsSubstHelper {A = A} {t = t} compt =
  subst
    (λ sigma -> Σ (FitsSubst [] (A ∷ []) sigma) (λ fits -> ComputableFits fits))
    (sym (singleSubstConsKeep t))
    base
  where
  base : Σ (FitsSubst [] (A ∷ []) (consSubst t (keepSubstBy 0))) (λ fits -> ComputableFits fits)
  base =
    fitsCons
      (fitsKeep {delta = []} {gamma = []} wfNil)
      (subst
        (λ T -> Derivable (hasTy [] t T))
        (sym (subTyId A) ∙ sym (cong (λ sigma -> subTy sigma A) keepSubstBy0Id))
        (compToDerivable compt))
    ,
    compFitsCons
      {sigma = keepSubstBy 0}
      compFitsNil
      (subst
        (λ T -> Computable (hasTy [] t T))
        (sym (subTyId A) ∙ sym (cong (λ sigma -> subTy sigma A) keepSubstBy0Id))
        compt)

singleComputableFitsEqSubstHelper : {A : RawType} {t u : RawTerm}
  -> Computable (termEq [] t u A)
  -> Σ (FitsEqSubst [] (A ∷ []) (singleSubst t) (singleSubst u)) (λ fitsEq -> ComputableFitsEq fitsEq)
singleComputableFitsEqSubstHelper {A = A} {t = t} {u = u} comptu =
  subst
    (λ sigma -> Σ (FitsEqSubst [] (A ∷ []) sigma (singleSubst u)) (λ fitsEq -> ComputableFitsEq fitsEq))
    (sym (singleSubstConsKeep t))
    (subst
      (λ tau -> Σ (FitsEqSubst [] (A ∷ []) (consSubst t (keepSubstBy 0)) tau) (λ fitsEq -> ComputableFitsEq fitsEq))
      (sym (singleSubstConsKeep u))
      base)
  where
  base :
    Σ (FitsEqSubst [] (A ∷ []) (consSubst t (keepSubstBy 0)) (consSubst u (keepSubstBy 0)))
      (λ fitsEq -> ComputableFitsEq fitsEq)
  base =
    fitsEqCons
      {sigma = keepSubstBy 0}
      {tau = keepSubstBy 0}
      (fitsEqNil wfNil)
      (subst
        (λ T -> Derivable (termEq [] t u T))
        (sym (subTyId A) ∙ sym (cong (λ sigma -> subTy sigma A) keepSubstBy0Id))
        (compToDerivable comptu))
    ,
    compFitsEqCons
      {sigma = keepSubstBy 0}
      {tau = keepSubstBy 0}
      compFitsEqNil
      (subst
        (λ T -> Computable (termEq [] t u T))
        (sym (subTyId A) ∙ sym (cong (λ sigma -> subTy sigma A) keepSubstBy0Id))
        comptu)
qtrCompComputableFitsHelper : {A : RawType} {a : RawTerm}
  -> Computable (hasTy [] a A)
  -> Σ (FitsSubst [] (A ∷ []) (qtrCompSub a)) (λ fits -> ComputableFits fits)
qtrCompComputableFitsHelper {A = A} {a = a} compa =
  subst
    (λ sigma -> Σ (FitsSubst [] (A ∷ []) sigma) (λ fits -> ComputableFits fits))
      (singleSubstConsKeep a ∙ cong (consSubst a) keepSubstBy0Id)
      base
  where
  base : Σ (FitsSubst [] (A ∷ []) (singleSubst a)) (λ fits -> ComputableFits fits)
  base = singleComputableFitsSubstHelper compa

sigmaCompComputableFitsHelper : {A B : RawType} {b c : RawTerm}
  -> Computable (hasTy [] b A)
  -> Computable (hasTy [] c (subTy (singleSubst b) B))
  -> Σ (FitsSubst [] (B ∷ A ∷ []) (sigmaCompSub b c)) (λ fits -> ComputableFits fits)
sigmaCompComputableFitsHelper {A = A} {B = B} {b = b} {c = c} compb compc =
  subst
    (λ sigma -> Σ (FitsSubst [] (B ∷ A ∷ []) sigma) (λ fits -> ComputableFits fits))
    (cong (consSubst c) (singleSubstConsKeep b ∙ cong (consSubst b) keepSubstBy0Id))
    base
  where
  base : Σ (FitsSubst [] (B ∷ A ∷ []) (consSubst c (singleSubst b))) (λ fits -> ComputableFits fits)
  base =
    fitsCons
      (fst (singleComputableFitsSubstHelper compb))
      (compToDerivable compc)
    ,
    compFitsCons (snd (singleComputableFitsSubstHelper compb)) compc

qtrCompComputableFitsEqHelper : {A : RawType} {a b : RawTerm}
  -> Computable (termEq [] a b A)
  -> Σ
       (FitsEqSubst [] (A ∷ []) (qtrCompSub a) (qtrCompSub b))
       (λ fitsEq -> ComputableFitsEq fitsEq)
qtrCompComputableFitsEqHelper {A = A} {a = a} {b = b} compab =
  subst
    (λ sigma -> Σ (FitsEqSubst [] (A ∷ []) sigma (qtrCompSub b)) (λ fitsEq -> ComputableFitsEq fitsEq))
    (singleSubstConsKeep a ∙ cong (consSubst a) keepSubstBy0Id)
    (subst
      (λ tau -> Σ (FitsEqSubst [] (A ∷ []) (singleSubst a) tau) (λ fitsEq -> ComputableFitsEq fitsEq))
      (singleSubstConsKeep b ∙ cong (consSubst b) keepSubstBy0Id)
      base)
  where
  base :
    Σ (FitsEqSubst [] (A ∷ []) (singleSubst a) (singleSubst b))
      (λ fitsEq -> ComputableFitsEq fitsEq)
  base = singleComputableFitsEqSubstHelper compab

sigmaCompComputableFitsEqHelper : {A B : RawType} {b c e f : RawTerm}
  -> Computable (termEq [] b e A)
  -> Computable (termEq [] c f (subTy (singleSubst b) B))
  -> Σ
       (FitsEqSubst [] (B ∷ A ∷ []) (sigmaCompSub b c) (sigmaCompSub e f))
       (λ fitsEq -> ComputableFitsEq fitsEq)
sigmaCompComputableFitsEqHelper {A = A} {B = B} {b = b} {c = c} {e = e} {f = f} compbe compcf =
  subst
    (λ sigma -> Σ (FitsEqSubst [] (B ∷ A ∷ []) sigma (sigmaCompSub e f)) (λ fitsEq -> ComputableFitsEq fitsEq))
    (cong (consSubst c) (singleSubstConsKeep b ∙ cong (consSubst b) keepSubstBy0Id))
    (subst
      (λ tau -> Σ (FitsEqSubst [] (B ∷ A ∷ []) (consSubst c (singleSubst b)) tau) (λ fitsEq -> ComputableFitsEq fitsEq))
      (cong (consSubst f) (singleSubstConsKeep e ∙ cong (consSubst e) keepSubstBy0Id))
      base)
  where
  base :
    Σ (FitsEqSubst [] (B ∷ A ∷ []) (consSubst c (singleSubst b)) (consSubst f (singleSubst e)))
      (λ fitsEq -> ComputableFitsEq fitsEq)
  base =
    fitsEqCons
      (fst (singleComputableFitsEqSubstHelper compbe))
      (compToDerivable compcf)
    ,
    compFitsEqCons
      (snd (singleComputableFitsEqSubstHelper compbe))
      compcf

compSingleSubstTyEqClosed : {A B C : RawType} {t : RawTerm}
  -> HypComputable (typeEq (A ∷ []) B C)
  -> Computable (hasTy [] t A)
  -> Computable (typeEq [] (subTy (singleSubst t) B) (subTy (singleSubst t) C))
compSingleSubstTyEqClosed {t = t} (hypTyEqOpen _ _ _ sub _) compt =
  sub (singleSubst t)
    (fst (singleComputableFitsSubstHelper compt))
    (snd (singleComputableFitsSubstHelper compt))

compSingleEqSubstTyClosed : {A B : RawType} {t u : RawTerm}
  -> HypComputable (isType (A ∷ []) B)
  -> Computable (termEq [] t u A)
  -> Computable (typeEq [] (subTy (singleSubst t) B) (subTy (singleSubst u) B))
compSingleEqSubstTyClosed {t = t} {u = u} (hypTyOpen _ _ _ subEq) comptu =
  subEq
    (singleSubst t)
    (singleSubst u)
    (fst (singleComputableFitsEqSubstHelper comptu))
    (snd (singleComputableFitsEqSubstHelper comptu))
