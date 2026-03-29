{-# OPTIONS --safe --cubical #-}

module TReg.Structural where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Empty.Base as Empty using (rec)
open import Cubical.Data.List.Base using ([] ; _∷_ ; _++_ ; length)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; doubleℕ)
open import Cubical.Data.Nat.Order using
  (_<_ ; _≤_ ; zero-≤ ; suc-≤-suc ; ≤-suc ; pred-≤-pred ; <-suc ; suc-< ; ¬-<-zero ; <-wellfounded)
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

wkJBy : Ctx -> JForm -> JForm
wkJBy delta (isType gamma A) =
  isType (delta ++ gamma) (wkTyBy (length delta) A)
wkJBy delta (typeEq gamma A B) =
  typeEq (delta ++ gamma) (wkTyBy (length delta) A) (wkTyBy (length delta) B)
wkJBy delta (hasTy gamma t A) =
  hasTy (delta ++ gamma) (wkTmBy (length delta) t) (wkTyBy (length delta) A)
wkJBy delta (termEq gamma t u A) =
  termEq (delta ++ gamma) (wkTmBy (length delta) t) (wkTmBy (length delta) u)
    (wkTyBy (length delta) A)

subJInto : Ctx -> Subst -> JForm -> JForm
subJInto gamma sigma (isType delta A) = isType gamma (subTy sigma A)
subJInto gamma sigma (typeEq delta A B) = typeEq gamma (subTy sigma A) (subTy sigma B)
subJInto gamma sigma (hasTy delta t A) = hasTy gamma (subTm sigma t) (subTy sigma A)
subJInto gamma sigma (termEq delta t u A) =
  termEq gamma (subTm sigma t) (subTm sigma u) (subTy sigma A)

eqSubJInto : Ctx -> Subst -> Subst -> JForm -> JForm
eqSubJInto gamma sigma tau (isType delta A) = typeEq gamma (subTy sigma A) (subTy tau A)
eqSubJInto gamma sigma tau (typeEq delta A B) =
  typeEq gamma (subTy sigma A) (subTy tau B)
eqSubJInto gamma sigma tau (hasTy delta t A) =
  termEq gamma (subTm sigma t) (subTm tau t) (subTy sigma A)
eqSubJInto gamma sigma tau (termEq delta t u A) =
  termEq gamma (subTm sigma t) (subTm tau u) (subTy sigma A)

closedTaskMeasure : RawType -> ℕ
closedTaskMeasure A = doubleℕ (tyDepth A)

openTaskMeasure : RawType -> ℕ
openTaskMeasure A = suc (closedTaskMeasure A)

doubleℕ-≤ : {m n : ℕ} -> m ≤ n -> doubleℕ m ≤ doubleℕ n
doubleℕ-≤ {m = zero} _ = zero-≤
doubleℕ-≤ {m = suc m} {n = zero} p = Empty.rec (¬-<-zero p)
doubleℕ-≤ {m = suc m} {n = suc n} p =
  suc-≤-suc (suc-≤-suc (doubleℕ-≤ (pred-≤-pred p)))

closedTask<openTask : (A : RawType) -> closedTaskMeasure A < openTaskMeasure A
closedTask<openTask A = <-suc

smallerOpenTask<ClosedTask : {A B : RawType}
  -> tyDepth A < tyDepth B
  -> openTaskMeasure A < closedTaskMeasure B
smallerOpenTask<ClosedTask p = doubleℕ-≤ p

smallerClosedTask<ClosedTask : {A B : RawType}
  -> tyDepth A < tyDepth B
  -> closedTaskMeasure A < closedTaskMeasure B
smallerClosedTask<ClosedTask p = suc-< (smallerOpenTask<ClosedTask p)

smallerClosedTask<OpenTask : {A B : RawType}
  -> tyDepth A < tyDepth B
  -> closedTaskMeasure A < openTaskMeasure B
smallerClosedTask<OpenTask p = ≤-suc (smallerClosedTask<ClosedTask p)

smallerOpenTask<OpenTask : {A B : RawType}
  -> tyDepth A < tyDepth B
  -> openTaskMeasure A < openTaskMeasure B
smallerOpenTask<OpenTask p = ≤-suc (smallerOpenTask<ClosedTask p)

rewriteClosedUpper : {m : ℕ} {A H : RawType}
  -> A ≡ H
  -> m < closedTaskMeasure H
  -> m < closedTaskMeasure A
rewriteClosedUpper {m = m} p =
  subst (λ n -> m < n) (sym (cong closedTaskMeasure p))

rewriteOpenUpper : {m : ℕ} {A H : RawType}
  -> A ≡ H
  -> m < openTaskMeasure H
  -> m < openTaskMeasure A
rewriteOpenUpper {m = m} p =
  subst (λ n -> m < n) (sym (cong openTaskMeasure p))

closedSubTask<OpenTask : (sigma : Subst) (A : RawType)
  -> closedTaskMeasure (subTy sigma A) < openTaskMeasure A
closedSubTask<OpenTask sigma A =
  subst
    (λ n -> closedTaskMeasure (subTy sigma A) < suc (doubleℕ n))
    (tyDepth-subTy sigma A)
    (closedTask<openTask (subTy sigma A))

subTySigmaFamilyDepth< : (sigma : Subst) (A B : RawType)
  -> tyDepth (subTy sigma B) < tyDepth (tySigma A B)
subTySigmaFamilyDepth< sigma A B =
  subst
    (λ n -> n < tyDepth (tySigma A B))
    (sym (tyDepth-subTy sigma B))
    (tyDepth-snd<Sigma A B)

compTyEqRightClosed : {A B : RawType}
  -> Computable (typeEq [] A B)
  -> Computable (isType [] B)
compTyEqRightClosed (compTyEqClosedTop _ _ compB _ _) = compB
compTyEqRightClosed (compTyEqClosedSigma _ _ compB _ _ _ _) = compB
compTyEqRightClosed (compTyEqClosedEq _ _ compB _ _ _ _ _) = compB
compTyEqRightClosed (compTyEqClosedQtr _ _ compB _ _ _) = compB
compTyEqRightClosed (compTyEqOpen neq _ _ _ _) = Empty.rec (neq refl)

compTmEqRightClosed : {t u : RawTerm} {A : RawType}
  -> Computable (termEq [] t u A)
  -> Computable (hasTy [] u A)
compTmEqRightClosed (compTmEqClosedTop _ _ compu _ _ _) = compu
compTmEqRightClosed (compTmEqClosedSigma _ _ compu _ _ _ _ _) = compu
compTmEqRightClosed (compTmEqClosedEq _ _ compu _ _ _ _) = compu
compTmEqRightClosed (compTmEqClosedQtr _ _ compu _ _ _ _ _) = compu
compTmEqRightClosed (compTmEqOpen neq _ _ _ _) = Empty.rec (neq refl)

mutual
  compReflTyClosedAcc : {A : RawType}
    -> Computable (isType [] A)
    -> Acc _<_ (closedTaskMeasure A)
    -> Computable (typeEq [] A A)
  compReflTyClosedAcc comp@(compTyClosedTop d ev corr) (acc rs) =
    compTyEqClosedTop (reflTy d) comp comp ev ev
  compReflTyClosedAcc
    comp@(compTyClosedSigma {B = B} {C = C} d ev corr compA compB)
    (acc rs) =
    let
      acHead =
        rs _ (rewriteClosedUpper {H = tySigma B C} (evalSigmaPath ev)
          (smallerClosedTask<ClosedTask {A = B} {B = tySigma B C}
            (tyDepth-fst<Sigma B C)))
      acFam =
        rs _ (rewriteClosedUpper {H = tySigma B C} (evalSigmaPath ev)
          (smallerOpenTask<ClosedTask {A = C} {B = tySigma B C}
            (tyDepth-snd<Sigma B C)))
    in
    compTyEqClosedSigma
      (reflTy d)
      comp
      comp
      ev
      ev
      (compReflTyClosedAcc compA acHead)
      (compReflTyAcc compB acFam)
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
  compReflTyClosedAcc (compTyOpen neq _ _ _) _ = Empty.rec (neq refl)

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
  compReflTmClosedAcc (compTmOpen neq _ _ _ _) _ = Empty.rec (neq refl)

  compReflTyAcc : {gamma : Ctx} {A : RawType}
    -> Computable (isType gamma A)
    -> Acc _<_ (openTaskMeasure A)
    -> Computable (typeEq gamma A A)
  compReflTyAcc {A = A} comp@(compTyClosedTop _ _ _) (acc rs) =
    compReflTyClosedAcc comp (rs _ (closedTask<openTask A))
  compReflTyAcc {A = A} comp@(compTyClosedSigma _ _ _ _ _) (acc rs) =
    compReflTyClosedAcc comp (rs _ (closedTask<openTask A))
  compReflTyAcc {A = A} comp@(compTyClosedEq _ _ _ _ _ _) (acc rs) =
    compReflTyClosedAcc comp (rs _ (closedTask<openTask A))
  compReflTyAcc {A = A} comp@(compTyClosedQtr _ _ _ _) (acc rs) =
    compReflTyClosedAcc comp (rs _ (closedTask<openTask A))
  compReflTyAcc {A = A} comp@(compTyOpen neq d sub subEq) (acc rs) =
    compTyEqOpen
      neq
      (reflTy d)
      comp
      (λ sigma fits ->
        let
          closedσ = sub sigma fits
        in
        closedSubstComp
          (compReflTyClosedAcc
            (ClosedSubstComp.closedComp closedσ)
            (rs _ (closedSubTask<OpenTask sigma A)))
          (ClosedSubstComp.closedCompFits closedσ))
      (λ sigma tau fitsEq ->
        let
          closedστ = subEq sigma tau fitsEq
        in
        closedEqSubstComp
          (ClosedEqSubstComp.closedEqComp closedστ)
          (ClosedEqSubstComp.closedEqCompFits closedστ))

  compReflTmAcc : {gamma : Ctx} {t : RawTerm} {A : RawType}
    -> Computable (hasTy gamma t A)
    -> Acc _<_ (openTaskMeasure A)
    -> Computable (termEq gamma t t A)
  compReflTmAcc {A = A} comp@(compTmClosedTop _ _ _ _ _) (acc rs) =
    compReflTmClosedAcc comp (rs _ (closedTask<openTask A))
  compReflTmAcc {A = A} comp@(compTmClosedSigma _ _ _ _ _ _ _) (acc rs) =
    compReflTmClosedAcc comp (rs _ (closedTask<openTask A))
  compReflTmAcc {A = A} comp@(compTmClosedEq _ _ _ _ _ _) (acc rs) =
    compReflTmClosedAcc comp (rs _ (closedTask<openTask A))
  compReflTmAcc {A = A} comp@(compTmClosedQtr _ _ _ _ _ _) (acc rs) =
    compReflTmClosedAcc comp (rs _ (closedTask<openTask A))
  compReflTmAcc {A = A} comp@(compTmOpen neq d compA sub subEq) (acc rs) =
    compTmEqOpen
      neq
      (reflTm d)
      comp
      (λ sigma fits ->
        let
          closedσ = sub sigma fits
        in
        closedSubstComp
          (compReflTmClosedAcc
            (ClosedSubstComp.closedComp closedσ)
            (rs _ (closedSubTask<OpenTask sigma A)))
          (ClosedSubstComp.closedCompFits closedσ))
      (λ sigma tau fitsEq ->
        let
          closedστ = subEq sigma tau fitsEq
        in
        closedEqSubstComp
          (ClosedEqSubstComp.closedEqComp closedστ)
          (ClosedEqSubstComp.closedEqCompFits closedστ))

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

compReflTy : {gamma : Ctx} {A : RawType}
  -> Computable (isType gamma A)
  -> Computable (typeEq gamma A A)
compReflTy {A = A} comp =
  compReflTyAcc comp (<-wellfounded (openTaskMeasure A))

compReflTm : {gamma : Ctx} {t : RawTerm} {A : RawType}
  -> Computable (hasTy gamma t A)
  -> Computable (termEq gamma t t A)
compReflTm {A = A} comp =
  compReflTmAcc comp (<-wellfounded (openTaskMeasure A))

singleCompFitsSubstHelper : {A : RawType} {t : RawTerm}
  -> Computable (hasTy [] t A)
  -> CompFitsSubst (A ∷ []) (singleSubst t)
singleCompFitsSubstHelper {A = A} {t = t} compt =
  subst
    (λ sigma -> CompFitsSubst (A ∷ []) sigma)
    (sym (singleSubstConsKeep t))
    (compFitsCons
      {sigma = keepSubstBy 0}
      compFitsNil
      (subst
        (λ T -> Computable (hasTy [] t T))
        (sym (subTyId A) ∙ sym (cong (λ sigma -> subTy sigma A) keepSubstBy0Id))
        compt))

singleCompFitsEqSubstHelper : {A : RawType} {t u : RawTerm}
  -> Computable (termEq [] t u A)
  -> CompFitsEqSubst (A ∷ []) (singleSubst t) (singleSubst u)
singleCompFitsEqSubstHelper {A = A} {t = t} {u = u} comptu =
  subst
    (λ sigma -> CompFitsEqSubst (A ∷ []) sigma (singleSubst u))
    (sym (singleSubstConsKeep t))
    (subst
      (λ tau -> CompFitsEqSubst (A ∷ []) (consSubst t (keepSubstBy 0)) tau)
      (sym (singleSubstConsKeep u))
      (compFitsEqCons
        {sigma = keepSubstBy 0}
        {tau = keepSubstBy 0}
        compFitsEqNil
        (subst
          (λ T -> Computable (termEq [] t u T))
          (sym (subTyId A) ∙ sym (cong (λ sigma -> subTy sigma A) keepSubstBy0Id))
          comptu)))

qtrCompCompFitsHelper : {A : RawType} {a : RawTerm}
  -> Computable (hasTy [] a A)
  -> CompFitsSubst (A ∷ []) (qtrCompSub a)
qtrCompCompFitsHelper {A = A} {a = a} compa =
  subst
    (λ sigma -> CompFitsSubst (A ∷ []) sigma)
    (singleSubstConsKeep a ∙ cong (consSubst a) keepSubstBy0Id)
    (singleCompFitsSubstHelper compa)

sigmaCompCompFitsHelper : {A B : RawType} {b c : RawTerm}
  -> Computable (hasTy [] b A)
  -> Computable (hasTy [] c (subTy (singleSubst b) B))
  -> CompFitsSubst (B ∷ A ∷ []) (sigmaCompSub b c)
sigmaCompCompFitsHelper {A = A} {B = B} {b = b} {c = c} compb compc =
  subst
    (λ sigma -> CompFitsSubst (B ∷ A ∷ []) sigma)
    (cong (consSubst c) (singleSubstConsKeep b ∙ cong (consSubst b) keepSubstBy0Id))
    (compFitsCons (singleCompFitsSubstHelper compb) compc)

compSingleSubstTyEqClosed : {A B C : RawType} {t : RawTerm}
  -> Computable (typeEq (A ∷ []) B C)
  -> Computable (hasTy [] t A)
  -> Computable (typeEq [] (subTy (singleSubst t) B) (subTy (singleSubst t) C))
compSingleSubstTyEqClosed {t = t} (compTyEqOpen _ _ _ sub _) compt =
  ClosedSubstComp.closedComp (sub (singleSubst t) (compFitsToFits (singleCompFitsSubstHelper compt)))

compSingleEqSubstTyClosed : {A B : RawType} {t u : RawTerm}
  -> Computable (isType (A ∷ []) B)
  -> Computable (termEq [] t u A)
  -> Computable (typeEq [] (subTy (singleSubst t) B) (subTy (singleSubst u) B))
compSingleEqSubstTyClosed {t = t} {u = u} (compTyOpen _ _ _ subEq) comptu =
  ClosedEqSubstComp.closedEqComp (subEq (singleSubst t) (singleSubst u) (compFitsEqToFitsEq (singleCompFitsEqSubstHelper comptu)))

closedSigmaFamily : {G A B : RawType}
  -> Computable (isType [] G)
  -> G =>t tySigma A B
  -> Computable (isType (A ∷ []) B)
closedSigmaFamily compG ev = ClosedSigmaTyInv.sigmaTyCompFam (invertSigmaTy compG ev)

mutual
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
    (compTyEqClosedSigma {C = C} {D = D} dAB compA compB evA evB compCE compDF)
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
      compDFa = compSingleSubstTyEqClosed compDF sigmaTmCompFst
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
  compConvTmClosedAcc _ (compTyEqOpen neq _ _ _ _) _ = Empty.rec (neq refl)

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
    compAB@(compTyEqClosedSigma {C = C} {D = D} dAB compA compB evA evB compCE compDF)
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
      compDFa = compSingleSubstTyEqClosed compDF (compTmEqLeft sigmaTmEqCompFst)
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
  compConvTmEqClosedAcc _ (compTyEqOpen neq _ _ _ _) _ = Empty.rec (neq refl)

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
      compB = closedSigmaFamily (compTmToCompTy compt) evA
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
  compSymTmClosedAcc (compTmEqOpen neq _ _ _ _) _ = Empty.rec (neq refl)

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
      compB = closedSigmaFamily (compTmToCompTy compt) evA
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
  compTransTmClosedAcc (compTmEqOpen neq _ _ _ _) _ _ = Empty.rec (neq refl)

compConvTmClosed : {t : RawTerm} {A B : RawType}
  -> Computable (hasTy [] t A)
  -> Computable (typeEq [] A B)
  -> Computable (hasTy [] t B)
compConvTmClosed {A = A} comp compAB =
  compConvTmClosedAcc comp compAB (<-wellfounded (closedTaskMeasure A))

compConvTmEqClosed : {t u : RawTerm} {A B : RawType}
  -> Computable (termEq [] t u A)
  -> Computable (typeEq [] A B)
  -> Computable (termEq [] t u B)
compConvTmEqClosed {A = A} comp compAB =
  compConvTmEqClosedAcc comp compAB (<-wellfounded (openTaskMeasure A))

compSymTmClosed : {t u : RawTerm} {A : RawType}
  -> Computable (termEq [] t u A)
  -> Computable (termEq [] u t A)
compSymTmClosed {A = A} comp =
  compSymTmClosedAcc comp (<-wellfounded (closedTaskMeasure A))

compTransTmClosed : {t u v : RawTerm} {A : RawType}
  -> Computable (termEq [] t u A)
  -> Computable (termEq [] u v A)
  -> Computable (termEq [] t v A)
compTransTmClosed {A = A} comp₁ comp₂ =
  compTransTmClosedAcc comp₁ comp₂ (<-wellfounded (closedTaskMeasure A))

compSubCons : (rho : Subst) (t : RawTerm) (sigma : Subst)
  -> compSub rho (consSubst t sigma) ≡ consSubst (subTm rho t) (compSub rho sigma)
compSubCons rho t sigma = funExt λ where
  zero -> refl
  (suc n) -> refl

composeFits : {theta gamma delta : Ctx} {rho sigma : Subst}
  -> FitsSubst theta gamma rho
  -> FitsSubst gamma delta sigma
  -> FitsSubst theta delta (compSub rho sigma)
composeFits {theta = theta} {rho = rho} {sigma = sigma} fitsThetaGamma (fitsNil wfGamma) =
  fitsNil {gamma = theta} {delta = []} {sigma = compSub rho sigma}
    (fitsSubstCtxWF fitsThetaGamma)
composeFits {theta = theta} {rho = rho} fitsThetaGamma
  (fitsCons {delta = delta} {sigma = sigma} {A = A} {t = t} fitsGammaDelta dt) =
  subst
    (λ zeta -> FitsSubst theta (A ∷ delta) zeta)
    (sym (compSubCons rho t sigma))
    (fitsCons
      (composeFits fitsThetaGamma fitsGammaDelta)
      (subst
        (λ T -> Derivable (hasTy theta (subTm rho t) T))
        (subTyComp rho sigma A)
        (substTmRule dt fitsThetaGamma)))

composeEqFits : {theta gamma delta : Ctx} {rho eta sigma : Subst}
  -> FitsEqSubst theta gamma rho eta
  -> FitsSubst gamma delta sigma
  -> FitsEqSubst theta delta (compSub rho sigma) (compSub eta sigma)
composeEqFits {theta = theta} {rho = rho} {eta = eta} {sigma = sigma} fitsEqThetaGamma (fitsNil wfGamma) =
  fitsEqNil {gamma = theta} {delta = []} {sigma = compSub rho sigma} {tau = compSub eta sigma}
    (fitsEqSubstCtxWF fitsEqThetaGamma)
composeEqFits {theta = theta} {rho = rho} {eta = eta} fitsEqThetaGamma
  (fitsCons {delta = delta} {sigma = sigma} {A = A} {t = t} fitsGammaDelta dt) =
  subst
    (λ zeta -> FitsEqSubst theta (A ∷ delta) zeta (compSub eta (consSubst t sigma)))
    (sym (compSubCons rho t sigma))
    (subst
      (λ zeta -> FitsEqSubst theta (A ∷ delta) (consSubst (subTm rho t) (compSub rho sigma)) zeta)
      (sym (compSubCons eta t sigma))
      (fitsEqCons
        (composeEqFits fitsEqThetaGamma fitsGammaDelta)
        (subst
          (λ T -> Derivable (termEq theta (subTm rho t) (subTm eta t) T))
          (subTyComp rho sigma A)
          (eqSubTmRule dt fitsEqThetaGamma))))

composeFitsEq : {theta gamma delta : Ctx} {rho sigma tau : Subst}
  -> FitsSubst theta gamma rho
  -> FitsEqSubst gamma delta sigma tau
  -> FitsEqSubst theta delta (compSub rho sigma) (compSub rho tau)
composeFitsEq {theta = theta} {rho = rho} {sigma = sigma} {tau = tau} fitsThetaGamma (fitsEqNil wfGamma) =
  fitsEqNil {gamma = theta} {delta = []} {sigma = compSub rho sigma} {tau = compSub rho tau}
    (fitsSubstCtxWF fitsThetaGamma)
composeFitsEq {theta = theta} {rho = rho} fitsThetaGamma
  (fitsEqCons {delta = delta} {sigma = sigma} {tau = tau} {A = A} {t = t} {u = u} fitsEqGammaDelta dtu) =
  subst
    (λ zeta -> FitsEqSubst theta (A ∷ delta) zeta (compSub rho (consSubst u tau)))
    (sym (compSubCons rho t sigma))
    (subst
      (λ zeta -> FitsEqSubst theta (A ∷ delta) (consSubst (subTm rho t) (compSub rho sigma)) zeta)
      (sym (compSubCons rho u tau))
      (fitsEqCons
        (composeFitsEq fitsThetaGamma fitsEqGammaDelta)
        (subst
          (λ T -> Derivable (termEq theta (subTm rho t) (subTm rho u) T))
          (subTyComp rho sigma A)
          (substTmEqRule dtu fitsThetaGamma))))

composeEqFitsEq : {theta gamma delta : Ctx} {rho eta sigma tau : Subst}
  -> FitsEqSubst theta gamma rho eta
  -> FitsEqSubst gamma delta sigma tau
  -> FitsEqSubst theta delta (compSub rho sigma) (compSub eta tau)
composeEqFitsEq {theta = theta} {rho = rho} {eta = eta} {sigma = sigma} {tau = tau} fitsEqThetaGamma (fitsEqNil wfGamma) =
  fitsEqNil {gamma = theta} {delta = []} {sigma = compSub rho sigma} {tau = compSub eta tau}
    (fitsEqSubstCtxWF fitsEqThetaGamma)
composeEqFitsEq {theta = theta} {rho = rho} {eta = eta} fitsEqThetaGamma
  (fitsEqCons {delta = delta} {sigma = sigma} {tau = tau} {A = A} {t = t} {u = u} fitsEqGammaDelta dtu) =
  subst
    (λ zeta -> FitsEqSubst theta (A ∷ delta) zeta (compSub eta (consSubst u tau)))
    (sym (compSubCons rho t sigma))
    (subst
      (λ zeta -> FitsEqSubst theta (A ∷ delta) (consSubst (subTm rho t) (compSub rho sigma)) zeta)
      (sym (compSubCons eta u tau))
      (fitsEqCons
        (composeEqFitsEq fitsEqThetaGamma fitsEqGammaDelta)
        (subst
          (λ T -> Derivable (termEq theta (subTm rho t) (subTm eta u) T))
          (subTyComp rho sigma A)
          (eqSubTmEqRule dtu fitsEqThetaGamma))))
