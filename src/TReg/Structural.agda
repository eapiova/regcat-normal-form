{-# OPTIONS --cubical --guardedness #-}

module TReg.Structural where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Empty.Base as Empty using (rec)
open import Cubical.Data.List.Base using ([] ; _∷_ ; _++_ ; length)
open import Cubical.Data.Nat using (zero ; suc)

open import TReg.Syntax
open import TReg.Context
open import TReg.Substitution
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

mutual
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

  {-# TERMINATING #-}
  compReflTyClosed : {A : RawType}
    -> Computable (isType [] A)
    -> Computable (typeEq [] A A)
  compReflTyClosed comp@(compTyClosedTop d ev corr) =
    compTyEqClosedTop (reflTy d) comp comp ev ev
  compReflTyClosed comp@(compTyClosedSigma d ev corr compA compB) =
    compTyEqClosedSigma
      (reflTy d)
      comp
      comp
      ev
      ev
      (compReflTyClosed compA)
      (compReflTy compB)
  compReflTyClosed comp@(compTyClosedEq d ev corr compA compa compb) =
    compTyEqClosedEq
      (reflTy d)
      comp
      comp
      ev
      ev
      (compReflTyClosed compA)
      (compReflTmClosed compa)
      (compReflTmClosed compb)
  compReflTyClosed comp@(compTyClosedQtr d ev corr compA) =
    compTyEqClosedQtr
      (reflTy d)
      comp
      comp
      ev
      ev
      (compReflTyClosed compA)
  compReflTyClosed (compTyOpen neq _ _ _) = Empty.rec (neq refl)

  {-# TERMINATING #-}
  compReflTmClosed : {t : RawTerm} {A : RawType}
    -> Computable (hasTy [] t A)
    -> Computable (termEq [] t t A)
  compReflTmClosed comp@(compTmClosedTop d compA evA evt corr) =
    compTmEqClosedTop (reflTm d) comp comp evA evt evt
  compReflTmClosed comp@(compTmClosedSigma d compA evA evt corr compa compb) =
    compTmEqClosedSigma
      (reflTm d)
      comp
      comp
      evA
      evt
      evt
      (compReflTmClosed compa)
      (compReflTmClosed compb)
  compReflTmClosed comp@(compTmClosedEq d compA evA evt corr compEq) =
    compTmEqClosedEq
      (reflTm d)
      comp
      comp
      evA
      evt
      evt
      compEq
  compReflTmClosed comp@(compTmClosedQtr d compA evA evt corr compa) =
    compTmEqClosedQtr
      (reflTm d)
      comp
      comp
      evA
      evt
      evt
      compa
      compa
  compReflTmClosed (compTmOpen neq _ _ _ _) = Empty.rec (neq refl)

  {-# TERMINATING #-}
  compReflTy : {gamma : Ctx} {A : RawType}
    -> Computable (isType gamma A)
    -> Computable (typeEq gamma A A)
  compReflTy comp@(compTyClosedTop _ _ _) = compReflTyClosed comp
  compReflTy comp@(compTyClosedSigma _ _ _ _ _) = compReflTyClosed comp
  compReflTy comp@(compTyClosedEq _ _ _ _ _ _) = compReflTyClosed comp
  compReflTy comp@(compTyClosedQtr _ _ _ _) = compReflTyClosed comp
  compReflTy comp@(compTyOpen neq d sub subEq) =
    compTyEqOpen
      neq
      (reflTy d)
      comp
      (λ sigma fits ->
        let closed = sub sigma fits in
        closeSubstComp
          (closedSubstCompFits closed)
          (compReflTyClosed (closedSubstCompBody closed)))
      (λ sigma tau fitsEq -> subEq sigma tau fitsEq)

  {-# TERMINATING #-}
  compReflTm : {gamma : Ctx} {t : RawTerm} {A : RawType}
    -> Computable (hasTy gamma t A)
    -> Computable (termEq gamma t t A)
  compReflTm comp@(compTmClosedTop _ _ _ _ _) = compReflTmClosed comp
  compReflTm comp@(compTmClosedSigma _ _ _ _ _ _ _) = compReflTmClosed comp
  compReflTm comp@(compTmClosedEq _ _ _ _ _ _) = compReflTmClosed comp
  compReflTm comp@(compTmClosedQtr _ _ _ _ _ _) = compReflTmClosed comp
  compReflTm comp@(compTmOpen neq d compA sub subEq) =
    compTmEqOpen
      neq
      (reflTm d)
      comp
      (λ sigma fits ->
        let closed = sub sigma fits in
        closeSubstComp
          (closedSubstCompFits closed)
          (compReflTmClosed (closedSubstCompBody closed)))
      (λ sigma tau fitsEq -> subEq sigma tau fitsEq)

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
  closedSubstCompBody (sub (singleSubst t) (compFitsToFits (singleCompFitsSubstHelper compt)))

compSingleEqSubstTyClosed : {A B : RawType} {t u : RawTerm}
  -> Computable (isType (A ∷ []) B)
  -> Computable (termEq [] t u A)
  -> Computable (typeEq [] (subTy (singleSubst t) B) (subTy (singleSubst u) B))
compSingleEqSubstTyClosed {t = t} {u = u} (compTyOpen _ _ _ subEq) comptu =
  closedEqSubstCompBody
    (subEq (singleSubst t) (singleSubst u) (compFitsEqToFitsEq (singleCompFitsEqSubstHelper comptu)))

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
