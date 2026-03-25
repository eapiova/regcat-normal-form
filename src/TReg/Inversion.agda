{-# OPTIONS --cubical --guardedness #-}

module TReg.Inversion where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Empty.Base as Empty using (⊥ ; rec)
open import Cubical.Data.Sigma
open import Cubical.Data.List.Base using ([] ; _∷_)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Nat.Properties using (znots ; snotz ; injSuc)

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

evalSigmaPath : {A B C : RawType}
  -> A =>t tySigma B C
  -> A ≡ tySigma B C
evalSigmaPath evalSigma = refl

evalTopPath : {A : RawType}
  -> A =>t tyTop
  -> A ≡ tyTop
evalTopPath evalTop = refl

evalEqPath : {A B : RawType} {a b : RawTerm}
  -> A =>t tyEq B a b
  -> A ≡ tyEq B a b
evalEqPath evalEq = refl

evalQtrPath : {A B : RawType}
  -> A =>t tyQtr B
  -> A ≡ tyQtr B
evalQtrPath evalQtr = refl

tyTag : RawType -> ℕ
tyTag tyTop = zero
tyTag (tySigma _ _) = suc zero
tyTag (tyEq _ _ _) = suc (suc zero)
tyTag (tyQtr _) = suc (suc (suc zero))

zeroNeOne : zero ≡ suc zero -> ⊥
zeroNeOne = znots

zeroNeTwo : zero ≡ suc (suc zero) -> ⊥
zeroNeTwo = znots

zeroNeThree : zero ≡ suc (suc (suc zero)) -> ⊥
zeroNeThree = znots

oneNeZero : suc zero ≡ zero -> ⊥
oneNeZero = snotz

oneNeTwo : suc zero ≡ suc (suc zero) -> ⊥
oneNeTwo p = znots (injSuc p)

oneNeThree : suc zero ≡ suc (suc (suc zero)) -> ⊥
oneNeThree p = znots (injSuc p)

twoNeZero : suc (suc zero) ≡ zero -> ⊥
twoNeZero = snotz

twoNeOne : suc (suc zero) ≡ suc zero -> ⊥
twoNeOne p = snotz (injSuc p)

twoNeThree : suc (suc zero) ≡ suc (suc (suc zero)) -> ⊥
twoNeThree p = znots (injSuc (injSuc p))

threeNeZero : suc (suc (suc zero)) ≡ zero -> ⊥
threeNeZero = snotz

threeNeOne : suc (suc (suc zero)) ≡ suc zero -> ⊥
threeNeOne p = snotz (injSuc p)

threeNeTwo : suc (suc (suc zero)) ≡ suc (suc zero) -> ⊥
threeNeTwo p = snotz (injSuc (injSuc p))

topNeSigma : {A B : RawType} -> tyTop ≡ tySigma A B -> ⊥
topNeSigma p = zeroNeOne (cong tyTag p)

topNeEq : {A : RawType} {a b : RawTerm} -> tyTop ≡ tyEq A a b -> ⊥
topNeEq p = zeroNeTwo (cong tyTag p)

topNeQtr : {A : RawType} -> tyTop ≡ tyQtr A -> ⊥
topNeQtr p = zeroNeThree (cong tyTag p)

sigmaNeTop : {A B : RawType} -> tySigma A B ≡ tyTop -> ⊥
sigmaNeTop p = oneNeZero (cong tyTag p)

sigmaNeEq : {A B C : RawType} {a b : RawTerm} -> tySigma A B ≡ tyEq C a b -> ⊥
sigmaNeEq p = oneNeTwo (cong tyTag p)

sigmaNeQtr : {A B C : RawType} -> tySigma A B ≡ tyQtr C -> ⊥
sigmaNeQtr p = oneNeThree (cong tyTag p)

eqNeTop : {A : RawType} {a b : RawTerm} -> tyEq A a b ≡ tyTop -> ⊥
eqNeTop p = twoNeZero (cong tyTag p)

eqNeSigma : {A B C : RawType} {a b : RawTerm} -> tyEq A a b ≡ tySigma B C -> ⊥
eqNeSigma p = twoNeOne (cong tyTag p)

eqNeQtr : {A B : RawType} {a b : RawTerm} -> tyEq A a b ≡ tyQtr B -> ⊥
eqNeQtr p = twoNeThree (cong tyTag p)

qtrNeTop : {A : RawType} -> tyQtr A ≡ tyTop -> ⊥
qtrNeTop p = threeNeZero (cong tyTag p)

qtrNeSigma : {A B C : RawType} -> tyQtr A ≡ tySigma B C -> ⊥
qtrNeSigma p = threeNeOne (cong tyTag p)

qtrNeEq : {A B : RawType} {a b : RawTerm} -> tyQtr A ≡ tyEq B a b -> ⊥
qtrNeEq p = threeNeTwo (cong tyTag p)

record ClosedTopTmInv (t : RawTerm) : Type where
  field
    topTmDeriv : Derivable (hasTy [] t tyTop)
    topTmCompTy : Computable (isType [] tyTop)
    topTmEvalStar : t =>e tmStar
    topTmCorrStar : Derivable (termEq [] t tmStar tyTop)

record ClosedTopTyInv (A : RawType) : Type where
  field
    topTyDeriv : Derivable (isType [] A)
    topTyCorr : Derivable (typeEq [] A tyTop)

record ClosedTopTmEqInv (t u : RawTerm) : Type where
  field
    topTmEqDeriv : Derivable (termEq [] t u tyTop)
    topTmEqCompLeft : Computable (hasTy [] t tyTop)
    topTmEqCompRight : Computable (hasTy [] u tyTop)
    topTmEqEvalLeftStar : t =>e tmStar
    topTmEqEvalRightStar : u =>e tmStar

record ClosedSigmaTmInv (t : RawTerm) (A B : RawType) : Type where
  field
    sigmaTmFst : RawTerm
    sigmaTmSnd : RawTerm
    sigmaTmDeriv : Derivable (hasTy [] t (tySigma A B))
    sigmaTmCompTy : Computable (isType [] (tySigma A B))
    sigmaTmEvalPair : t =>e tmPair sigmaTmFst sigmaTmSnd
    sigmaTmCorrPair : Derivable (termEq [] t (tmPair sigmaTmFst sigmaTmSnd) (tySigma A B))
    sigmaTmCompFst : Computable (hasTy [] sigmaTmFst A)
    sigmaTmCompSnd : Computable (hasTy [] sigmaTmSnd (subTy (singleSubst sigmaTmFst) B))

record ClosedSigmaTyInv (G A B : RawType) : Type where
  field
    sigmaTyDeriv : Derivable (isType [] G)
    sigmaTyCorr : Derivable (typeEq [] G (tySigma A B))
    sigmaTyCompHead : Computable (isType [] A)
    sigmaTyCompFam : Computable (isType (A ∷ []) B)

record ClosedSigmaTmEqInv (t u : RawTerm) (A B : RawType) : Type where
  field
    sigmaTmEqLeftFst : RawTerm
    sigmaTmEqLeftSnd : RawTerm
    sigmaTmEqRightFst : RawTerm
    sigmaTmEqRightSnd : RawTerm
    sigmaTmEqDeriv : Derivable (termEq [] t u (tySigma A B))
    sigmaTmEqCompLeft : Computable (hasTy [] t (tySigma A B))
    sigmaTmEqCompRight : Computable (hasTy [] u (tySigma A B))
    sigmaTmEqEvalLeftPair : t =>e tmPair sigmaTmEqLeftFst sigmaTmEqLeftSnd
    sigmaTmEqEvalRightPair : u =>e tmPair sigmaTmEqRightFst sigmaTmEqRightSnd
    sigmaTmEqCompFst : Computable (termEq [] sigmaTmEqLeftFst sigmaTmEqRightFst A)
    sigmaTmEqCompSnd : Computable (termEq [] sigmaTmEqLeftSnd sigmaTmEqRightSnd (subTy (singleSubst sigmaTmEqLeftFst) B))

record ClosedEqTmInv (t : RawTerm) (A : RawType) (a b : RawTerm) : Type where
  field
    eqTmDeriv : Derivable (hasTy [] t (tyEq A a b))
    eqTmCompTy : Computable (isType [] (tyEq A a b))
    eqTmEvalRhs : t =>e tmR
    eqTmCorrRhs : Derivable (termEq [] t tmR (tyEq A a b))
    eqTmCompInner : Computable (termEq [] a b A)

record ClosedEqTyInv (G A : RawType) (a b : RawTerm) : Type where
  field
    eqTyDeriv : Derivable (isType [] G)
    eqTyCorr : Derivable (typeEq [] G (tyEq A a b))
    eqTyCompBase : Computable (isType [] A)
    eqTyCompLeft : Computable (hasTy [] a A)
    eqTyCompRight : Computable (hasTy [] b A)

record ClosedEqTmEqInv (t u : RawTerm) (A : RawType) (a b : RawTerm) : Type where
  field
    eqTmEqDeriv : Derivable (termEq [] t u (tyEq A a b))
    eqTmEqCompLeft : Computable (hasTy [] t (tyEq A a b))
    eqTmEqCompRight : Computable (hasTy [] u (tyEq A a b))
    eqTmEqEvalLeftR : t =>e tmR
    eqTmEqEvalRightR : u =>e tmR
    eqTmEqCompInner : Computable (termEq [] a b A)

record ClosedQtrTmInv (t : RawTerm) (A : RawType) : Type where
  field
    qtrTmRepr : RawTerm
    qtrTmDeriv : Derivable (hasTy [] t (tyQtr A))
    qtrTmCompTy : Computable (isType [] (tyQtr A))
    qtrTmEvalClass : t =>e tmClass qtrTmRepr
    qtrTmCorrClass : Derivable (termEq [] t (tmClass qtrTmRepr) (tyQtr A))
    qtrTmCompRepr : Computable (hasTy [] qtrTmRepr A)

record ClosedQtrTyInv (G A : RawType) : Type where
  field
    qtrTyDeriv : Derivable (isType [] G)
    qtrTyCorr : Derivable (typeEq [] G (tyQtr A))
    qtrTyCompBase : Computable (isType [] A)

record ClosedQtrTmEqInv (t u : RawTerm) (A : RawType) : Type where
  field
    qtrTmEqLeftRepr : RawTerm
    qtrTmEqRightRepr : RawTerm
    qtrTmEqDeriv : Derivable (termEq [] t u (tyQtr A))
    qtrTmEqCompLeft : Computable (hasTy [] t (tyQtr A))
    qtrTmEqCompRight : Computable (hasTy [] u (tyQtr A))
    qtrTmEqEvalLeftClass : t =>e tmClass qtrTmEqLeftRepr
    qtrTmEqEvalRightClass : u =>e tmClass qtrTmEqRightRepr
    qtrTmEqCompLeftRepr : Computable (hasTy [] qtrTmEqLeftRepr A)
    qtrTmEqCompRightRepr : Computable (hasTy [] qtrTmEqRightRepr A)

record ClosedSigmaTyEqInv (B A₁ A₂ : RawType) : Type where
  field
    sigmaTyEqRightHead : RawType
    sigmaTyEqRightFam : RawType
    sigmaTyEqDeriv : Derivable (typeEq [] (tySigma A₁ A₂) B)
    sigmaTyEqCompLeft : Computable (isType [] (tySigma A₁ A₂))
    sigmaTyEqCompRight : Computable (isType [] B)
    sigmaTyEqEvalRight : B =>t tySigma sigmaTyEqRightHead sigmaTyEqRightFam
    sigmaTyEqCompHead : Computable (typeEq [] A₁ sigmaTyEqRightHead)
    sigmaTyEqCompFam : Computable (typeEq (A₁ ∷ []) A₂ sigmaTyEqRightFam)

record ClosedEqTyEqInv (B A : RawType) (a b : RawTerm) : Type where
  field
    eqTyEqRightBase : RawType
    eqTyEqRightLeft : RawTerm
    eqTyEqRightRight : RawTerm
    eqTyEqDeriv : Derivable (typeEq [] (tyEq A a b) B)
    eqTyEqCompLeft : Computable (isType [] (tyEq A a b))
    eqTyEqCompRight : Computable (isType [] B)
    eqTyEqEvalRight : B =>t tyEq eqTyEqRightBase eqTyEqRightLeft eqTyEqRightRight
    eqTyEqCompBase : Computable (typeEq [] A eqTyEqRightBase)
    eqTyEqCompLeftTerm : Computable (termEq [] a eqTyEqRightLeft A)
    eqTyEqCompRightTerm : Computable (termEq [] b eqTyEqRightRight A)

record ClosedQtrTyEqInv (B A : RawType) : Type where
  field
    qtrTyEqRightBase : RawType
    qtrTyEqDeriv : Derivable (typeEq [] (tyQtr A) B)
    qtrTyEqCompLeft : Computable (isType [] (tyQtr A))
    qtrTyEqCompRight : Computable (isType [] B)
    qtrTyEqEvalRight : B =>t tyQtr qtrTyEqRightBase
    qtrTyEqCompBase : Computable (typeEq [] A qtrTyEqRightBase)

invertTopTm0 : {t : RawTerm}
  -> Computable (hasTy [] t tyTop)
  -> ClosedTopTmInv t
invertTopTm0 (compTmClosedTop d compTy evalTop evt corr) =
  record
    { topTmDeriv = d
    ; topTmCompTy = compTy
    ; topTmEvalStar = evt
    ; topTmCorrStar = corr
    }
invertTopTm0 (compTmClosedSigma _ _ () _ _ _ _)
invertTopTm0 (compTmClosedEq _ _ () _ _ _)
invertTopTm0 (compTmClosedQtr _ _ () _ _ _)
invertTopTm0 (compTmOpen neq _ _ _ _) = rec (neq refl)

invertTopTm : {t : RawTerm} {A : RawType}
  -> Computable (hasTy [] t A)
  -> A =>t tyTop
  -> ClosedTopTmInv t
invertTopTm {t = t} comp ev =
  invertTopTm0
    (subst
      (λ T -> Computable (hasTy [] t T))
      (evalTopPath ev)
      comp)

invertTopTmEq0 : {t u : RawTerm}
  -> Computable (termEq [] t u tyTop)
  -> ClosedTopTmEqInv t u
invertTopTmEq0 (compTmEqClosedTop d compt compu evalTop evt evu) =
  record
    { topTmEqDeriv = d
    ; topTmEqCompLeft = compt
    ; topTmEqCompRight = compu
    ; topTmEqEvalLeftStar = evt
    ; topTmEqEvalRightStar = evu
    }
invertTopTmEq0 (compTmEqClosedSigma _ _ _ () _ _ _ _)
invertTopTmEq0 (compTmEqClosedEq _ _ _ () _ _ _)
invertTopTmEq0 (compTmEqClosedQtr _ _ _ () _ _ _ _)
invertTopTmEq0 (compTmEqOpen neq _ _ _ _) = rec (neq refl)

invertTopTmEq : {t u : RawTerm} {A : RawType}
  -> Computable (termEq [] t u A)
  -> A =>t tyTop
  -> ClosedTopTmEqInv t u
invertTopTmEq {t = t} {u = u} comp ev =
  invertTopTmEq0
    (subst
      (λ T -> Computable (termEq [] t u T))
      (evalTopPath ev)
      comp)

invertSigmaTm0 : {t : RawTerm} {A B : RawType}
  -> Computable (hasTy [] t (tySigma A B))
  -> ClosedSigmaTmInv t A B
invertSigmaTm0 (compTmClosedSigma {a = a} {b = b} d compG evalSigma evt corr compa compb) =
  record
    { sigmaTmFst = a
    ; sigmaTmSnd = b
    ; sigmaTmDeriv = d
    ; sigmaTmCompTy = compG
    ; sigmaTmEvalPair = evt
    ; sigmaTmCorrPair = corr
    ; sigmaTmCompFst = compa
    ; sigmaTmCompSnd = compb
    }
invertSigmaTm0 (compTmClosedTop _ _ () _ _)
invertSigmaTm0 (compTmClosedEq _ _ () _ _ _)
invertSigmaTm0 (compTmClosedQtr _ _ () _ _ _)
invertSigmaTm0 (compTmOpen neq _ _ _ _) = rec (neq refl)

invertSigmaTm : {t : RawTerm} {G A B : RawType}
  -> Computable (hasTy [] t G)
  -> G =>t tySigma A B
  -> ClosedSigmaTmInv t A B
invertSigmaTm {t = t} comp ev =
  invertSigmaTm0
    (subst
      (λ T -> Computable (hasTy [] t T))
      (evalSigmaPath ev)
      comp)

invertSigmaTmEq0 : {t u : RawTerm} {A B : RawType}
  -> Computable (termEq [] t u (tySigma A B))
  -> ClosedSigmaTmEqInv t u A B
invertSigmaTmEq0 (compTmEqClosedSigma {a = a} {b = b} {c = c} {d = d}
  dEq compt compu evalSigma evt evu compac compbd) =
  record
    { sigmaTmEqLeftFst = a
    ; sigmaTmEqLeftSnd = b
    ; sigmaTmEqRightFst = c
    ; sigmaTmEqRightSnd = d
    ; sigmaTmEqDeriv = dEq
    ; sigmaTmEqCompLeft = compt
    ; sigmaTmEqCompRight = compu
    ; sigmaTmEqEvalLeftPair = evt
    ; sigmaTmEqEvalRightPair = evu
    ; sigmaTmEqCompFst = compac
    ; sigmaTmEqCompSnd = compbd
    }
invertSigmaTmEq0 (compTmEqClosedTop _ _ _ () _ _)
invertSigmaTmEq0 (compTmEqClosedEq _ _ _ () _ _ _)
invertSigmaTmEq0 (compTmEqClosedQtr _ _ _ () _ _ _ _)
invertSigmaTmEq0 (compTmEqOpen neq _ _ _ _) = rec (neq refl)

invertSigmaTmEq : {t u : RawTerm} {G A B : RawType}
  -> Computable (termEq [] t u G)
  -> G =>t tySigma A B
  -> ClosedSigmaTmEqInv t u A B
invertSigmaTmEq {t = t} {u = u} comp ev =
  invertSigmaTmEq0
    (subst
      (λ T -> Computable (termEq [] t u T))
      (evalSigmaPath ev)
      comp)

invertEqTm0 : {t : RawTerm} {A : RawType} {a b : RawTerm}
  -> Computable (hasTy [] t (tyEq A a b))
  -> ClosedEqTmInv t A a b
invertEqTm0 (compTmClosedEq d compG evalEq evt corr compab) =
  record
    { eqTmDeriv = d
    ; eqTmCompTy = compG
    ; eqTmEvalRhs = evt
    ; eqTmCorrRhs = corr
    ; eqTmCompInner = compab
    }
invertEqTm0 (compTmClosedTop _ _ () _ _)
invertEqTm0 (compTmClosedSigma _ _ () _ _ _ _)
invertEqTm0 (compTmClosedQtr _ _ () _ _ _)
invertEqTm0 (compTmOpen neq _ _ _ _) = rec (neq refl)

invertEqTm : {t : RawTerm} {G A : RawType} {a b : RawTerm}
  -> Computable (hasTy [] t G)
  -> G =>t tyEq A a b
  -> ClosedEqTmInv t A a b
invertEqTm {t = t} comp ev =
  invertEqTm0
    (subst
      (λ T -> Computable (hasTy [] t T))
      (evalEqPath ev)
      comp)

invertEqTmEq0 : {t u : RawTerm} {A : RawType} {a b : RawTerm}
  -> Computable (termEq [] t u (tyEq A a b))
  -> ClosedEqTmEqInv t u A a b
invertEqTmEq0 (compTmEqClosedEq d compt compu evalEq evt evu compab) =
  record
    { eqTmEqDeriv = d
    ; eqTmEqCompLeft = compt
    ; eqTmEqCompRight = compu
    ; eqTmEqEvalLeftR = evt
    ; eqTmEqEvalRightR = evu
    ; eqTmEqCompInner = compab
    }
invertEqTmEq0 (compTmEqClosedTop _ _ _ () _ _)
invertEqTmEq0 (compTmEqClosedSigma _ _ _ () _ _ _ _)
invertEqTmEq0 (compTmEqClosedQtr _ _ _ () _ _ _ _)
invertEqTmEq0 (compTmEqOpen neq _ _ _ _) = rec (neq refl)

invertEqTmEq : {t u : RawTerm} {G A : RawType} {a b : RawTerm}
  -> Computable (termEq [] t u G)
  -> G =>t tyEq A a b
  -> ClosedEqTmEqInv t u A a b
invertEqTmEq {t = t} {u = u} comp ev =
  invertEqTmEq0
    (subst
      (λ T -> Computable (termEq [] t u T))
      (evalEqPath ev)
      comp)

invertQtrTm0 : {t : RawTerm} {A : RawType}
  -> Computable (hasTy [] t (tyQtr A))
  -> ClosedQtrTmInv t A
invertQtrTm0 (compTmClosedQtr {a = a} d compG evalQtr evt corr compa) =
  record
    { qtrTmRepr = a
    ; qtrTmDeriv = d
    ; qtrTmCompTy = compG
    ; qtrTmEvalClass = evt
    ; qtrTmCorrClass = corr
    ; qtrTmCompRepr = compa
    }
invertQtrTm0 (compTmClosedTop _ _ () _ _)
invertQtrTm0 (compTmClosedSigma _ _ () _ _ _ _)
invertQtrTm0 (compTmClosedEq _ _ () _ _ _)
invertQtrTm0 (compTmOpen neq _ _ _ _) = rec (neq refl)

invertQtrTm : {t : RawTerm} {G A : RawType}
  -> Computable (hasTy [] t G)
  -> G =>t tyQtr A
  -> ClosedQtrTmInv t A
invertQtrTm {t = t} comp ev =
  invertQtrTm0
    (subst
      (λ T -> Computable (hasTy [] t T))
      (evalQtrPath ev)
      comp)

invertQtrTmEq0 : {t u : RawTerm} {A : RawType}
  -> Computable (termEq [] t u (tyQtr A))
  -> ClosedQtrTmEqInv t u A
invertQtrTmEq0 (compTmEqClosedQtr {a = a} {b = b} d compt compu evalQtr evt evu compa compb) =
  record
    { qtrTmEqLeftRepr = a
    ; qtrTmEqRightRepr = b
    ; qtrTmEqDeriv = d
    ; qtrTmEqCompLeft = compt
    ; qtrTmEqCompRight = compu
    ; qtrTmEqEvalLeftClass = evt
    ; qtrTmEqEvalRightClass = evu
    ; qtrTmEqCompLeftRepr = compa
    ; qtrTmEqCompRightRepr = compb
    }
invertQtrTmEq0 (compTmEqClosedTop _ _ _ () _ _)
invertQtrTmEq0 (compTmEqClosedSigma _ _ _ () _ _ _ _)
invertQtrTmEq0 (compTmEqClosedEq _ _ _ () _ _ _)
invertQtrTmEq0 (compTmEqOpen neq _ _ _ _) = rec (neq refl)

invertQtrTmEq : {t u : RawTerm} {G A : RawType}
  -> Computable (termEq [] t u G)
  -> G =>t tyQtr A
  -> ClosedQtrTmEqInv t u A
invertQtrTmEq {t = t} {u = u} comp ev =
  invertQtrTmEq0
    (subst
      (λ T -> Computable (termEq [] t u T))
      (evalQtrPath ev)
      comp)

invertSigmaTyEq0 : {B A₁ A₂ : RawType}
  -> Computable (typeEq [] (tySigma A₁ A₂) B)
  -> ClosedSigmaTyEqInv B A₁ A₂
invertSigmaTyEq0
  (compTyEqClosedSigma {E = E} {F = F}
    d compA compB evalSigma evB compCE compDF) =
  record
    { sigmaTyEqRightHead = E
    ; sigmaTyEqRightFam = F
    ; sigmaTyEqDeriv = d
    ; sigmaTyEqCompLeft = compA
    ; sigmaTyEqCompRight = compB
    ; sigmaTyEqEvalRight = evB
    ; sigmaTyEqCompHead = compCE
    ; sigmaTyEqCompFam = compDF
    }
invertSigmaTyEq0 (compTyEqClosedTop _ _ _ () _)
invertSigmaTyEq0 (compTyEqClosedEq _ _ _ () _ _ _ _)
invertSigmaTyEq0 (compTyEqClosedQtr _ _ _ () _ _)
invertSigmaTyEq0 (compTyEqOpen neq _ _ _ _) = rec (neq refl)

invertSigmaTyEq : {A B A₁ A₂ : RawType}
  -> Computable (typeEq [] A B)
  -> A =>t tySigma A₁ A₂
  -> ClosedSigmaTyEqInv B A₁ A₂
invertSigmaTyEq {B = B} comp ev =
  invertSigmaTyEq0
    (subst
      (λ T -> Computable (typeEq [] T B))
      (evalSigmaPath ev)
      comp)

invertEqTyEq0 : {B A : RawType} {a b : RawTerm}
  -> Computable (typeEq [] (tyEq A a b) B)
  -> ClosedEqTyEqInv B A a b
invertEqTyEq0
  (compTyEqClosedEq {D = D} {c = c} {d = d}
    dEq compA compB evalEq evB compCD compac compbd) =
  record
    { eqTyEqRightBase = D
    ; eqTyEqRightLeft = c
    ; eqTyEqRightRight = d
    ; eqTyEqDeriv = dEq
    ; eqTyEqCompLeft = compA
    ; eqTyEqCompRight = compB
    ; eqTyEqEvalRight = evB
    ; eqTyEqCompBase = compCD
    ; eqTyEqCompLeftTerm = compac
    ; eqTyEqCompRightTerm = compbd
    }
invertEqTyEq0 (compTyEqClosedTop _ _ _ () _)
invertEqTyEq0 (compTyEqClosedSigma _ _ _ () _ _ _)
invertEqTyEq0 (compTyEqClosedQtr _ _ _ () _ _)
invertEqTyEq0 (compTyEqOpen neq _ _ _ _) = rec (neq refl)

invertEqTyEq : {A B C : RawType} {a b : RawTerm}
  -> Computable (typeEq [] A B)
  -> A =>t tyEq C a b
  -> ClosedEqTyEqInv B C a b
invertEqTyEq {B = B} comp ev =
  invertEqTyEq0
    (subst
      (λ T -> Computable (typeEq [] T B))
      (evalEqPath ev)
      comp)

invertQtrTyEq0 : {B A : RawType}
  -> Computable (typeEq [] (tyQtr A) B)
  -> ClosedQtrTyEqInv B A
invertQtrTyEq0
  (compTyEqClosedQtr {D = D} d compA compB evalQtr evB compCD) =
  record
    { qtrTyEqRightBase = D
    ; qtrTyEqDeriv = d
    ; qtrTyEqCompLeft = compA
    ; qtrTyEqCompRight = compB
    ; qtrTyEqEvalRight = evB
    ; qtrTyEqCompBase = compCD
    }
invertQtrTyEq0 (compTyEqClosedTop _ _ _ () _)
invertQtrTyEq0 (compTyEqClosedSigma _ _ _ () _ _ _)
invertQtrTyEq0 (compTyEqClosedEq _ _ _ () _ _ _ _)
invertQtrTyEq0 (compTyEqOpen neq _ _ _ _) = rec (neq refl)

invertQtrTyEq : {A B C : RawType}
  -> Computable (typeEq [] A B)
  -> A =>t tyQtr C
  -> ClosedQtrTyEqInv B C
invertQtrTyEq {B = B} comp ev =
  invertQtrTyEq0
    (subst
      (λ T -> Computable (typeEq [] T B))
      (evalQtrPath ev)
      comp)

invertTopTy : {A : RawType}
  -> Computable (isType [] A)
  -> A =>t tyTop
  -> ClosedTopTyInv A
invertTopTy (compTyClosedTop d _ corr) _ =
  record
    { topTyDeriv = d
    ; topTyCorr = corr
    }
invertTopTy (compTyClosedSigma _ evSigma _ _ _) ev =
  rec (topNeSigma (sym (evalTopPath ev) ∙ evalSigmaPath evSigma))
invertTopTy (compTyClosedEq _ evEq _ _ _ _) ev =
  rec (topNeEq (sym (evalTopPath ev) ∙ evalEqPath evEq))
invertTopTy (compTyClosedQtr _ evQtr _ _) ev =
  rec (topNeQtr (sym (evalTopPath ev) ∙ evalQtrPath evQtr))
invertTopTy (compTyOpen neq _ _ _) _ = rec (neq refl)

invertSigmaTy : {G A B : RawType}
  -> Computable (isType [] G)
  -> G =>t tySigma A B
  -> ClosedSigmaTyInv G A B
invertSigmaTy {A = A} {B = B}
  (compTyClosedSigma {B = A} {C = B} d evalSigma corr compA compB) evalSigma =
  record
    { sigmaTyDeriv = d
    ; sigmaTyCorr = corr
    ; sigmaTyCompHead = compA
    ; sigmaTyCompFam = compB
    }
invertSigmaTy (compTyClosedTop _ evTop _) ev =
  rec (sigmaNeTop (sym (evalSigmaPath ev) ∙ evalTopPath evTop))
invertSigmaTy (compTyClosedEq _ evEq _ _ _ _) ev =
  rec (sigmaNeEq (sym (evalSigmaPath ev) ∙ evalEqPath evEq))
invertSigmaTy (compTyClosedQtr _ evQtr _ _) ev =
  rec (sigmaNeQtr (sym (evalSigmaPath ev) ∙ evalQtrPath evQtr))
invertSigmaTy (compTyOpen neq _ _ _) _ = rec (neq refl)

invertEqTy : {G A : RawType} {a b : RawTerm}
  -> Computable (isType [] G)
  -> G =>t tyEq A a b
  -> ClosedEqTyInv G A a b
invertEqTy {A = A} {a = a} {b = b}
  (compTyClosedEq {B = A} {a = a} {b = b} d evalEq corr compA compa compb) evalEq =
  record
    { eqTyDeriv = d
    ; eqTyCorr = corr
    ; eqTyCompBase = compA
    ; eqTyCompLeft = compa
    ; eqTyCompRight = compb
    }
invertEqTy (compTyClosedTop _ evTop _) ev =
  rec (eqNeTop (sym (evalEqPath ev) ∙ evalTopPath evTop))
invertEqTy (compTyClosedSigma _ evSigma _ _ _) ev =
  rec (eqNeSigma (sym (evalEqPath ev) ∙ evalSigmaPath evSigma))
invertEqTy (compTyClosedQtr _ evQtr _ _) ev =
  rec (eqNeQtr (sym (evalEqPath ev) ∙ evalQtrPath evQtr))
invertEqTy (compTyOpen neq _ _ _) _ = rec (neq refl)

invertQtrTy : {G A : RawType}
  -> Computable (isType [] G)
  -> G =>t tyQtr A
  -> ClosedQtrTyInv G A
invertQtrTy {A = A} (compTyClosedQtr {B = A} d evalQtr corr compA) evalQtr =
  record
    { qtrTyDeriv = d
    ; qtrTyCorr = corr
    ; qtrTyCompBase = compA
    }
invertQtrTy (compTyClosedTop _ evTop _) ev =
  rec (qtrNeTop (sym (evalQtrPath ev) ∙ evalTopPath evTop))
invertQtrTy (compTyClosedSigma _ evSigma _ _ _) ev =
  rec (qtrNeSigma (sym (evalQtrPath ev) ∙ evalSigmaPath evSigma))
invertQtrTy (compTyClosedEq _ evEq _ _ _ _) ev =
  rec (qtrNeEq (sym (evalQtrPath ev) ∙ evalEqPath evEq))
invertQtrTy (compTyOpen neq _ _ _) _ = rec (neq refl)
