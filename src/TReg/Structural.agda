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
open import Cubical.Data.Nat using (ℕ)
open import TReg.Computability
open import TReg.Inversion
open import TReg.Presupposition
open import TReg.StructuralBase public

compTyEqRightClosed : {n : ℕ} -> {A B : RawType}
  -> Computable n (typeEq [] A B)
  -> Computable n (isType [] B)
compTyEqRightClosed (compTyEqClosedTop _ _ compB _ _) = compB
compTyEqRightClosed (compTyEqClosedSigma _ _ compB _ _ _ _) = compB
compTyEqRightClosed (compTyEqClosedEq _ _ compB _ _ _ _ _) = compB
compTyEqRightClosed (compTyEqClosedQtr _ _ compB _ _ _) = compB

compTmEqRightClosed : {n : ℕ} -> {t u : RawTerm} {A : RawType}
  -> Computable n (termEq [] t u A)
  -> Computable n (hasTy [] u A)
compTmEqRightClosed (compTmEqClosedTop _ _ compu _ _ _) = compu
compTmEqRightClosed (compTmEqClosedSigma _ _ compu _ _ _ _ _) = compu
compTmEqRightClosed (compTmEqClosedEq _ _ compu _ _ _ _) = compu
compTmEqRightClosed (compTmEqClosedQtr _ _ compu _ _ _ _ _) = compu

mutual
  compReflTyClosedAcc : {n : ℕ} -> {A : RawType}
    -> Computable n (isType [] A)
    -> Acc _<_ (closedTaskMeasure A)
    -> Computable n (typeEq [] A A)
  compReflTyClosedAcc comp@(compTyClosedTop d ev corr) (acc rs) =
    compTyEqClosedTop (reflTy d) comp comp ev ev
  compReflTyClosedAcc
    comp@(compTyClosedSigma {B = B} {C = C} d ev corr compA dFam subFam subEqFam)
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
      (reflTy dFam)
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

  compReflTmClosedAcc : {n : ℕ} -> {t : RawTerm} {A : RawType}
    -> Computable n (hasTy [] t A)
    -> Acc _<_ (closedTaskMeasure A)
    -> Computable n (termEq [] t t A)
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

compReflTyClosed : {n : ℕ} -> {A : RawType}
  -> Computable n (isType [] A)
  -> Computable n (typeEq [] A A)
compReflTyClosed {A = A} comp =
  compReflTyClosedAcc comp (<-wellfounded (closedTaskMeasure A))

compReflTmClosed : {n : ℕ} -> {t : RawTerm} {A : RawType}
  -> Computable n (hasTy [] t A)
  -> Computable n (termEq [] t t A)
compReflTmClosed {A = A} comp =
  compReflTmClosedAcc comp (<-wellfounded (closedTaskMeasure A))

singleComputableFitsSubstHelper : {n : ℕ} -> {A : RawType} {t : RawTerm}
  -> Computable n (hasTy [] t A)
  -> CompFitsBundle n (A ∷ []) (singleSubst t)
singleComputableFitsSubstHelper {n} {A = A} {t = t} compt =
  subst
    (λ sigma -> CompFitsBundle n (A ∷ []) sigma)
    (sym (singleSubstConsKeep t))
    base
  where
  base : CompFitsBundle n (A ∷ []) (consSubst t (keepSubstBy 0))
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
        (λ T -> Computable n (hasTy [] t T))
        (sym (subTyId A) ∙ sym (cong (λ sigma -> subTy sigma A) keepSubstBy0Id))
        compt)

singleComputableFitsEqSubstHelper : {n : ℕ} -> {A : RawType} {t u : RawTerm}
  -> Computable n (termEq [] t u A)
  -> CompFitsEqBundle n (A ∷ []) (singleSubst t) (singleSubst u)
singleComputableFitsEqSubstHelper {n} {A = A} {t = t} {u = u} comptu =
  subst
    (λ sigma -> CompFitsEqBundle n (A ∷ []) sigma (singleSubst u))
    (sym (singleSubstConsKeep t))
    (subst
      (λ tau -> CompFitsEqBundle n (A ∷ []) (consSubst t (keepSubstBy 0)) tau)
      (sym (singleSubstConsKeep u))
      base)
  where
  base :
    Σ (FitsEqSubst [] (A ∷ []) (consSubst t (keepSubstBy 0)) (consSubst u (keepSubstBy 0)))
      (ComputableFitsEq n)
  base =
    fitsEqCons
      {sigma = keepSubstBy 0}
      {tau = keepSubstBy 0}
      (fitsEqNil
        {gamma = []} {delta = []}
        {sigma = keepSubstBy 0} {tau = keepSubstBy 0}
        wfNil)
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
        (λ T -> Computable n (termEq [] t u T))
        (sym (subTyId A) ∙ sym (cong (λ sigma -> subTy sigma A) keepSubstBy0Id))
        comptu)
qtrCompComputableFitsHelper : {n : ℕ} -> {A : RawType} {a : RawTerm}
  -> Computable n (hasTy [] a A)
  -> CompFitsBundle n (A ∷ []) (qtrCompSub a)
qtrCompComputableFitsHelper {n} {A = A} {a = a} compa =
  subst
    (λ sigma -> CompFitsBundle n (A ∷ []) sigma)
      (singleSubstConsKeep a ∙ cong (consSubst a) keepSubstBy0Id)
      base
  where
  base : CompFitsBundle n (A ∷ []) (singleSubst a)
  base = singleComputableFitsSubstHelper compa

sigmaCompComputableFitsHelper : {n : ℕ} -> {A B : RawType} {b c : RawTerm}
  -> Computable n (hasTy [] b A)
  -> Computable n (hasTy [] c (subTy (singleSubst b) B))
  -> CompFitsBundle n (B ∷ A ∷ []) (sigmaCompSub b c)
sigmaCompComputableFitsHelper {n} {A = A} {B = B} {b = b} {c = c} compb compc =
  subst
    (λ sigma -> CompFitsBundle n (B ∷ A ∷ []) sigma)
    (cong (consSubst c) (singleSubstConsKeep b ∙ cong (consSubst b) keepSubstBy0Id))
    base
  where
  base : CompFitsBundle n (B ∷ A ∷ []) (consSubst c (singleSubst b))
  base =
    fitsCons
      (fst (singleComputableFitsSubstHelper compb))
      (compToDerivable compc)
    ,
    compFitsCons (snd (singleComputableFitsSubstHelper compb)) compc

qtrCompComputableFitsEqHelper : {n : ℕ} -> {A : RawType} {a b : RawTerm}
  -> Computable n (termEq [] a b A)
  -> Σ
       (FitsEqSubst [] (A ∷ []) (qtrCompSub a) (qtrCompSub b))
       (ComputableFitsEq n)
qtrCompComputableFitsEqHelper {n} {A = A} {a = a} {b = b} compab =
  subst
    (λ sigma -> CompFitsEqBundle n (A ∷ []) sigma (qtrCompSub b))
    (singleSubstConsKeep a ∙ cong (consSubst a) keepSubstBy0Id)
    (subst
      (λ tau -> CompFitsEqBundle n (A ∷ []) (singleSubst a) tau)
      (singleSubstConsKeep b ∙ cong (consSubst b) keepSubstBy0Id)
      base)
  where
  base :
    Σ (FitsEqSubst [] (A ∷ []) (singleSubst a) (singleSubst b))
      (ComputableFitsEq n)
  base = singleComputableFitsEqSubstHelper compab

sigmaCompComputableFitsEqHelper : {n : ℕ} -> {A B : RawType} {b c e f : RawTerm}
  -> Computable n (termEq [] b e A)
  -> Computable n (termEq [] c f (subTy (singleSubst b) B))
  -> Σ
       (FitsEqSubst [] (B ∷ A ∷ []) (sigmaCompSub b c) (sigmaCompSub e f))
       (ComputableFitsEq n)
sigmaCompComputableFitsEqHelper {n} {A = A} {B = B} {b = b} {c = c} {e = e} {f = f} compbe compcf =
  subst
    (λ sigma -> CompFitsEqBundle n (B ∷ A ∷ []) sigma (sigmaCompSub e f))
    (cong (consSubst c) (singleSubstConsKeep b ∙ cong (consSubst b) keepSubstBy0Id))
    (subst
      (λ tau -> CompFitsEqBundle n (B ∷ A ∷ []) (consSubst c (singleSubst b)) tau)
      (cong (consSubst f) (singleSubstConsKeep e ∙ cong (consSubst e) keepSubstBy0Id))
      base)
  where
  base :
    Σ (FitsEqSubst [] (B ∷ A ∷ []) (consSubst c (singleSubst b)) (consSubst f (singleSubst e)))
      (ComputableFitsEq n)
  base =
    fitsEqCons
      (fst (singleComputableFitsEqSubstHelper compbe))
      (compToDerivable compcf)
    ,
    compFitsEqCons
      (snd (singleComputableFitsEqSubstHelper compbe))
      compcf

compSingleSubstTyEqClosed : {n : ℕ} -> {A B C : RawType} {t : RawTerm}
  -> HypComputable n (typeEq (A ∷ []) B C)
  -> Computable n (hasTy [] t A)
  -> Computable n (typeEq [] (subTy (singleSubst t) B) (subTy (singleSubst t) C))
compSingleSubstTyEqClosed {t = t} (hypTyEqOpen _ _ _ sub _) compt =
  sub (singleSubst t)
    (fst (singleComputableFitsSubstHelper compt))
    (snd (singleComputableFitsSubstHelper compt))

compSingleEqSubstTyClosed : {n : ℕ} -> {A B : RawType} {t u : RawTerm}
  -> HypComputable n (isType (A ∷ []) B)
  -> Computable n (termEq [] t u A)
  -> Computable n (typeEq [] (subTy (singleSubst t) B) (subTy (singleSubst u) B))
compSingleEqSubstTyClosed {t = t} {u = u} (hypTyOpen _ _ _ subEq) comptu =
  subEq
    (singleSubst t)
    (singleSubst u)
    (fst (singleComputableFitsEqSubstHelper comptu))
    (snd (singleComputableFitsEqSubstHelper comptu))
