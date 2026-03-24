{-# OPTIONS --cubical --guardedness #-}

module TReg.Inversion where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Empty.Base as Empty using (rec)
open import Cubical.Data.Sigma
open import Cubical.Data.List.Base using ([] ; _∷_)

open import TReg.Syntax
open import TReg.Context
open import TReg.Substitution
open import TReg.Evaluation
open import TReg.Derivability
open import TReg.Computability

closedSubstCompFits : {gamma : Ctx} {sigma : Subst} {J : JForm}
  -> ClosedSubstComp gamma sigma J
  -> CompFitsSubst gamma sigma
closedSubstCompFits (closeSubstComp compSigma _) = compSigma

closedSubstCompBody : {gamma : Ctx} {sigma : Subst} {J : JForm}
  -> ClosedSubstComp gamma sigma J
  -> Computable J
closedSubstCompBody (closeSubstComp _ compJ) = compJ

closedEqSubstCompFits : {gamma : Ctx} {sigma tau : Subst} {J : JForm}
  -> ClosedEqSubstComp gamma sigma tau J
  -> CompFitsEqSubst gamma sigma tau
closedEqSubstCompFits (closeEqSubstComp compSigma _) = compSigma

closedEqSubstCompBody : {gamma : Ctx} {sigma tau : Subst} {J : JForm}
  -> ClosedEqSubstComp gamma sigma tau J
  -> Computable J
closedEqSubstCompBody (closeEqSubstComp _ compJ) = compJ

compToDerivable : {J : JForm} -> Computable J -> Derivable J
compToDerivable (compTyClosedTop d _ _) = d
compToDerivable (compTyClosedSigma d _ _ _ _) = d
compToDerivable (compTyClosedEq d _ _ _ _ _) = d
compToDerivable (compTyClosedQtr d _ _ _) = d
compToDerivable (compTyEqClosedTop d _ _ _ _) = d
compToDerivable (compTyEqClosedSigma d _ _ _ _ _ _) = d
compToDerivable (compTyEqClosedEq d _ _ _ _ _ _ _) = d
compToDerivable (compTyEqClosedQtr d _ _ _ _ _) = d
compToDerivable (compTmClosedTop d _ _ _ _) = d
compToDerivable (compTmClosedSigma d _ _ _ _ _ _) = d
compToDerivable (compTmClosedEq d _ _ _ _ _) = d
compToDerivable (compTmClosedQtr d _ _ _ _ _) = d
compToDerivable (compTmEqClosedTop d _ _ _ _ _) = d
compToDerivable (compTmEqClosedSigma d _ _ _ _ _ _ _) = d
compToDerivable (compTmEqClosedEq d _ _ _ _ _ _) = d
compToDerivable (compTmEqClosedQtr d _ _ _ _ _ _ _) = d
compToDerivable (compTyOpen _ d _ _) = d
compToDerivable (compTyEqOpen _ d _ _ _) = d
compToDerivable (compTmOpen _ d _ _ _) = d
compToDerivable (compTmEqOpen _ d _ _ _) = d

compTyEval : {A : RawType} -> Computable (isType [] A) -> Σ RawType (λ G -> A =>t G)
compTyEval (compTyClosedTop _ ev _) = tyTop , ev
compTyEval (compTyClosedSigma {B = B} {C = C} _ ev _ _ _) = tySigma B C , ev
compTyEval (compTyClosedEq {B = B} {a = a} {b = b} _ ev _ _ _ _) = tyEq B a b , ev
compTyEval (compTyClosedQtr {B = B} _ ev _ _) = tyQtr B , ev
compTyEval (compTyOpen neq _ _ _) = Empty.rec (neq refl)

compTmToCompTy : {gamma : Ctx} {t : RawTerm} {A : RawType}
  -> Computable (hasTy gamma t A)
  -> Computable (isType gamma A)
compTmToCompTy (compTmClosedTop _ compA _ _ _) = compA
compTmToCompTy (compTmClosedSigma _ compA _ _ _ _ _) = compA
compTmToCompTy (compTmClosedEq _ compA _ _ _ _) = compA
compTmToCompTy (compTmClosedQtr _ compA _ _ _ _) = compA
compTmToCompTy (compTmOpen _ _ compA _ _) = compA

compTyEqLeft : {gamma : Ctx} {A B : RawType}
  -> Computable (typeEq gamma A B)
  -> Computable (isType gamma A)
compTyEqLeft (compTyEqClosedTop _ compA _ _ _) = compA
compTyEqLeft (compTyEqClosedSigma _ compA _ _ _ _ _) = compA
compTyEqLeft (compTyEqClosedEq _ compA _ _ _ _ _ _) = compA
compTyEqLeft (compTyEqClosedQtr _ compA _ _ _ _) = compA
compTyEqLeft (compTyEqOpen _ _ compA _ _) = compA

compTmEqLeft : {gamma : Ctx} {t u : RawTerm} {A : RawType}
  -> Computable (termEq gamma t u A)
  -> Computable (hasTy gamma t A)
compTmEqLeft (compTmEqClosedTop _ compt _ _ _ _) = compt
compTmEqLeft (compTmEqClosedSigma _ compt _ _ _ _ _ _) = compt
compTmEqLeft (compTmEqClosedEq _ compt _ _ _ _ _) = compt
compTmEqLeft (compTmEqClosedQtr _ compt _ _ _ _ _ _) = compt
compTmEqLeft (compTmEqOpen _ _ compt _ _) = compt

compFitsToFits : {gamma : Ctx} {sigma : Subst}
  -> CompFitsSubst gamma sigma
  -> FitsSubst [] gamma sigma
compFitsToFits {sigma = sigma} compFitsNil =
  fitsNil {gamma = []} {delta = []} {sigma = sigma} wfNil
compFitsToFits (compFitsCons compSigma compt) =
  fitsCons (compFitsToFits compSigma) (compToDerivable compt)

compFitsEqToFitsEq : {gamma : Ctx} {sigma tau : Subst}
  -> CompFitsEqSubst gamma sigma tau
  -> FitsEqSubst [] gamma sigma tau
compFitsEqToFitsEq {sigma = sigma} {tau = tau} compFitsEqNil =
  fitsEqNil {gamma = []} {delta = []} {sigma = sigma} {tau = tau} wfNil
compFitsEqToFitsEq (compFitsEqCons compSigma compt) =
  fitsEqCons (compFitsEqToFitsEq compSigma) (compToDerivable compt)

compFitsEqLeft : {gamma : Ctx} {sigma tau : Subst}
  -> CompFitsEqSubst gamma sigma tau
  -> CompFitsSubst gamma sigma
compFitsEqLeft compFitsEqNil = compFitsNil
compFitsEqLeft (compFitsEqCons compSigma compt) =
  compFitsCons (compFitsEqLeft compSigma) (compTmEqLeft compt)
