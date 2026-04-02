{-# OPTIONS --safe --cubical #-}

module TReg.StructuralBase where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Empty.Base as Empty using (⊥ ; rec)
open import Cubical.Data.List.Base using ([] ; _∷_ ; _++_ ; length)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; doubleℕ)
open import Cubical.Data.Nat.Order using
  (_<_ ; _≤_ ; zero-≤ ; suc-≤-suc ; ≤-suc ; pred-≤-pred ; <-suc ; suc-< ; ¬-<-zero)

open import TReg.Syntax
open import TReg.Context
open import TReg.Substitution
open import TReg.Measure
open import TReg.Evaluation
open import TReg.Derivability
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
