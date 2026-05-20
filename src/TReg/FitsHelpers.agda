{-# OPTIONS --safe #-}
-- Helpers extracted from CompTheorem.agda pre-mutual section.
-- Phase F.5 (Stage 1): file split to enable extracting openHypTm* helpers.

module TReg.FitsHelpers where

open import TReg.Prelude
open import Data.Empty as Empty using (⊥) renaming (⊥-elim to rec)
open import Data.Product using (Σ ; Σ-syntax ; _×_ ; _,_) renaming (proj₁ to fst ; proj₂ to snd)
open import Data.List.Base using ([] ; _∷_ ; _++_ ; length)
open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Nat.Base using (_<_)
open import Data.Nat.Induction using () renaming (<-wellFounded to <-wellfounded)
open import Data.Nat.Properties using () renaming (1+n≢0 to snotz)
open import Data.Unit using (tt) renaming (⊤ to Unit)
open import Induction.WellFounded using (Acc ; acc) renaming (acc-inverse to access)

open import TReg.Syntax
open import TReg.Context
open import TReg.Substitution
open import TReg.Measure
open import TReg.Evaluation
open import TReg.Derivability
open import TReg.Computability
open import TReg.Inversion
open import TReg.Presupposition
open import TReg.Structural
open import TReg.TopComp
open import TReg.EqComp

nonemptyNeNil : {A : RawType} {gamma : Ctx} -> (A ∷ gamma ≡ []) -> ⊥
nonemptyNeNil {gamma = gamma} p = snotz (cong length p)

case_of_ : {A B : Type} -> A -> (A -> B) -> B
case x of f = f x

compReflTy : {n : ℕ} -> {A : RawType}
  -> Computable n (isType [] A)
  -> Computable n (typeEq [] A A)
compReflTy {n} = compReflTyClosed

compReflTm : {n : ℕ} -> {t : RawTerm} {A : RawType}
  -> Computable n (hasTy [] t A)
  -> Computable n (termEq [] t t A)
compReflTm {n} = compReflTmClosed

-- compFitsEqRight: extract ComputableFits for the right substitution
-- from ComputableFitsEq. Needs conv transport matching fitsEqSubstRight.
-- TODO: implement properly; for now used with a hole in compSymTm

liftFitsNR : {theta gamma : Ctx} {A : RawType} {sigma : Subst}
  -> FitsSubst theta gamma sigma
  -> Derivable (isType theta (subTy sigma A))
  -> FitsSubst (subTy sigma A ∷ theta) (A ∷ gamma)
       (consSubst (var zero) (compSub (keepSubstCtx 1 theta) sigma))
liftFitsNR {theta = theta} {gamma = gamma} {A = A} {sigma = sigma} fits dAσ =
  fitsCons tail headVar
  where
  wfAσ : CtxWF (subTy sigma A ∷ theta)
  wfAσ = wfCons (fitsSubstCtxWF fits) dAσ

  tail : FitsSubst (subTy sigma A ∷ theta) gamma (compSub (keepSubstCtx 1 theta) sigma)
  tail =
    composeFits
      (fitsKeep {delta = subTy sigma A ∷ []} {gamma = theta} wfAσ)
      fits

  headVar0 : Derivable
    (hasTy (subTy sigma A ∷ theta) (var zero) (wkTyBy 1 (subTy sigma A)))
  headVar0 = varStar {gamma = theta} {delta = []} {A = subTy sigma A} wfAσ dAσ

  headVar : Derivable
    (hasTy (subTy sigma A ∷ theta) (var zero) (subTy (compSub (keepSubstCtx 1 theta) sigma) A))
  headVar =
    subst
      (λ T -> Derivable (hasTy (subTy sigma A ∷ theta) (var zero) T))
      (renTyKeepSubstBy 1 (subTy sigma A)
        ∙ sym (keepSubstCtx-subTy 1 theta (subTy sigma A))
        ∙ subTyComp (keepSubstCtx 1 theta) sigma A)
      headVar0

liftFitsOneNR : {gamma : Ctx} {A : RawType} {sigma : Subst}
  -> FitsSubst [] gamma sigma
  -> Derivable (isType [] (subTy sigma A))
  -> FitsSubst (subTy sigma A ∷ []) (A ∷ gamma)
       (consSubst (var zero) (compSub (keepSubstBy 1) sigma))
liftFitsOneNR = liftFitsNR

liftFitsEqNR : {theta gamma : Ctx} {A : RawType} {sigma tau : Subst}
  -> FitsEqSubst theta gamma sigma tau
  -> Derivable (isType theta (subTy sigma A))
  -> FitsEqSubst (subTy sigma A ∷ theta) (A ∷ gamma)
       (consSubst (var zero) (compSub (keepSubstCtx 1 theta) sigma))
       (consSubst (var zero) (compSub (keepSubstCtx 1 theta) tau))
liftFitsEqNR {theta = theta} {gamma = gamma} {A = A} {sigma = sigma} {tau = tau} fitsEq dAσ =
  fitsEqCons tail (reflTm headVar)
  where
  wfAσ : CtxWF (subTy sigma A ∷ theta)
  wfAσ = wfCons (fitsEqSubstCtxWF fitsEq) dAσ

  tail : FitsEqSubst (subTy sigma A ∷ theta) gamma
    (compSub (keepSubstCtx 1 theta) sigma)
    (compSub (keepSubstCtx 1 theta) tau)
  tail =
    composeFitsEq
      (fitsKeep {delta = subTy sigma A ∷ []} {gamma = theta} wfAσ)
      fitsEq

  headVar0 : Derivable
    (hasTy (subTy sigma A ∷ theta) (var zero) (wkTyBy 1 (subTy sigma A)))
  headVar0 = varStar {gamma = theta} {delta = []} {A = subTy sigma A} wfAσ dAσ

  headVar : Derivable
    (hasTy (subTy sigma A ∷ theta) (var zero) (subTy (compSub (keepSubstCtx 1 theta) sigma) A))
  headVar =
    subst
      (λ T -> Derivable (hasTy (subTy sigma A ∷ theta) (var zero) T))
      (renTyKeepSubstBy 1 (subTy sigma A)
        ∙ sym (keepSubstCtx-subTy 1 theta (subTy sigma A))
        ∙ subTyComp (keepSubstCtx 1 theta) sigma A)
      headVar0

liftFitsEqOneNR : {gamma : Ctx} {A : RawType} {sigma tau : Subst}
  -> FitsEqSubst [] gamma sigma tau
  -> Derivable (isType [] (subTy sigma A))
  -> FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma)
       (consSubst (var zero) (compSub (keepSubstBy 1) sigma))
       (consSubst (var zero) (compSub (keepSubstBy 1) tau))
liftFitsEqOneNR = liftFitsEqNR

compSubKeep1RenSub : (sigma : Subst)
  -> compSub (keepSubstBy 1) sigma ≡ renSub sucRen sigma
compSubKeep1RenSub (shiftSub zero) = refl
compSubKeep1RenSub (shiftSub (suc k)) = refl
compSubKeep1RenSub (consSub t sigma) =
  cong₂ consSubst (sym (renTmKeepSubstBy 1 t)) (compSubKeep1RenSub sigma)

abstract
  liftSubstCompKeepNR : (sigma : Subst)
    -> consSubst (var zero) (compSub (keepSubstBy 1) sigma) ≡ liftSubst sigma
  liftSubstCompKeepNR sigma = cong (consSubst (var zero)) (compSubKeep1RenSub sigma)

composeOneBinderNR : {gamma : Ctx} {A : RawType} {sigma tau : Subst}
  -> FitsSubst [] gamma sigma
  -> Derivable (isType [] (subTy sigma A))
  -> FitsSubst [] (subTy sigma A ∷ []) tau
  -> FitsSubst [] (A ∷ gamma) (compSub tau (liftSubst sigma))
composeOneBinderNR {gamma = gamma} {A = A} {sigma = sigma} {tau = tau} fits dAσ fits2 =
  subst
    (λ rho -> FitsSubst [] (A ∷ gamma) rho)
    (cong (compSub tau) (liftSubstCompKeepNR sigma))
    (composeFits fits2 (liftFitsOneNR fits dAσ))

composeOneBinderEqNR : {gamma : Ctx} {A : RawType} {sigma tau₁ tau₂ : Subst}
  -> FitsSubst [] gamma sigma
  -> Derivable (isType [] (subTy sigma A))
  -> FitsEqSubst [] (subTy sigma A ∷ []) tau₁ tau₂
  -> FitsEqSubst [] (A ∷ gamma) (compSub tau₁ (liftSubst sigma)) (compSub tau₂ (liftSubst sigma))
composeOneBinderEqNR {gamma = gamma} {A = A} {sigma = sigma} {tau₁ = tau₁} {tau₂ = tau₂} fits dAσ fitsEq =
  subst
    (λ rho -> FitsEqSubst [] (A ∷ gamma) rho (compSub tau₂ (liftSubst sigma)))
    (cong (compSub tau₁) (liftSubstCompKeepNR sigma))
    (subst
      (λ rho ->
        FitsEqSubst [] (A ∷ gamma)
          (compSub tau₁ (consSubst (var zero) (compSub (keepSubstBy 1) sigma)))
          rho)
      (cong (compSub tau₂) (liftSubstCompKeepNR sigma))
      (composeEqFits fitsEq (liftFitsOneNR fits dAσ)))

-- Status of termination-pragma removal (post Apr 25 F.5 module split):
-- See ~/.claude/plans/sharded-prancing-forest.md for full status and the
-- Tier 1-4 verification roadmap. Leading suspected residual termination
-- issues are:
--   - "Scope C" sites at compEQtrClosed / compESigmaClosed invocations
--     (Acc witnesses for derived derivations rather than pattern subterms);
--   - sigmaTyFamHypClosed → mkHypComputableTy dB closure-Acc extraction.
-- This long-form historical narrative was removed because it drifted out
-- of date through Apr 19 and Apr 25 work.
nilComputableFits : {n : ℕ} ->    {sigma : Subst}
  -> (fits : FitsSubst [] [] sigma)
  -> ComputableFits n fits
nilComputableFits {n} (fitsNil {gamma = []} {sigma = sigma} wf) =
  compFitsNil {sigma = sigma} {wf = wf}

nilComputableFitsEq : {n : ℕ} ->    {sigma tau : Subst}
  -> (fitsEq : FitsEqSubst [] [] sigma tau)
  -> ComputableFitsEq n fitsEq
nilComputableFitsEq
  (fitsEqNil {gamma = []} {sigma = sigma} {tau = tau} wf) =
  compFitsEqNil {sigma = sigma} {tau = tau} {wf = wf}

abstract
  compFSigmaClosed : {n : ℕ} -> {A B : RawType}
    -> Computable n (isType [] A)
    -> Derivable (isType (A ∷ []) B)
    -> Computable n (isType [] (tySigma A B))
  compFSigmaClosed {n} compA dB =
    compTyClosedSigma
      (fSigma (compToDerivable compA) dB)
      evalSigma
      (reflTy (fSigma (compToDerivable compA) dB))
      compA
      dB

compISigmaClosed : {n : ℕ} -> {a b : RawTerm} {A B : RawType}
  -> Computable n (hasTy [] a A)
  -> Computable n (hasTy [] b (subTy (singleSubst a) B))
  -> Computable n (isType [] (tySigma A B))
  -> Computable n (hasTy [] (tmPair a b) (tySigma A B))
compISigmaClosed {n} compa compb compSigma =
  compTmClosedSigma
    (iSigma (compToDerivable compa) (compToDerivable compb) (compToDerivable compSigma))
    compSigma
    evalSigma
    evalPair
    (reflTm (iSigma (compToDerivable compa) (compToDerivable compb) (compToDerivable compSigma)))
    compa
    compb

compCSigmaClosed : {n : ℕ} -> {b c m : RawTerm} {A B M : RawType}
  -> HypComputable (suc n) (isType ((tySigma A B) ∷ []) M)
  -> Computable n (hasTy [] b A)
  -> Computable n (hasTy [] c (subTy (singleSubst b) B))
  -> (dm : Derivable (hasTy (B ∷ A ∷ []) m (sigmaBranchTy M)))
  -> Computable n
       (hasTy [] (subTm (sigmaCompSub b c) m) (subTy (sigmaCompSub b c) (sigmaBranchTy M)))
  -> Computable n
       (termEq [] (tmElSigma (tmPair b c) m) (subTm (sigmaCompSub b c) m)
         (subTy (singleSubst (tmPair b c)) M))
compCSigmaClosed {n} {b = b} {c = c} {m = m} {A = A} {B = B} {M = M}
  compM compb compc dm rawBody =
  lhsEq body
  where
  db : Derivable (hasTy [] b A)
  db = compToDerivable compb

  dc : Derivable (hasTy [] c (subTy (singleSubst b) B))
  dc = compToDerivable compc

  dM : Derivable (isType ((tySigma A B) ∷ []) M)
  dM = hypCompToDerivable compM

  dSigma : Derivable (isType [] (tySigma A B))
  dSigma = ctxSuffixTy {delta = []} {gamma = []} {A = tySigma A B} (derivToCtxWF dM)

  body : Computable n
    (hasTy [] (subTm (sigmaCompSub b c) m) (subTy (singleSubst (tmPair b c)) M))
  body =
    subst
      (λ T -> Computable n (hasTy [] (subTm (sigmaCompSub b c) m) T))
      (sigmaBranchTyComp b c M)
      rawBody

  dEq : Derivable
    (termEq [] (tmElSigma (tmPair b c) m) (subTm (sigmaCompSub b c) m)
      (subTy (singleSubst (tmPair b c)) M))
  dEq = cSigma dM dSigma db dc dm

  dLeft : Derivable
    (hasTy [] (tmElSigma (tmPair b c) m) (subTy (singleSubst (tmPair b c)) M))
  dLeft = assocTmLeft dEq

  lhsEq : 
    Computable n
      (hasTy [] (subTm (sigmaCompSub b c) m) (subTy (singleSubst (tmPair b c)) M))
    -> Computable n
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

abstract
  compFQtrClosed : {n : ℕ} -> {A : RawType}
    -> Computable n (isType [] A)
    -> Computable n (isType [] (tyQtr A))
  compFQtrClosed {n} compA =
    compTyClosedQtr
      (fQtr (compToDerivable compA))
      evalQtr
      (reflTy (fQtr (compToDerivable compA)))
      compA

compIQtrClosed : {n : ℕ} -> {a : RawTerm} {A : RawType}
  -> Computable n (hasTy [] a A)
  -> Computable n (hasTy [] (tmClass a) (tyQtr A))
compIQtrClosed {n} compa =
  compTmClosedQtr
    (iQtr (compToDerivable compa))
    (compFQtrClosed (compTmToCompTy compa))
    evalQtr
    evalClass
    (reflTm (iQtr (compToDerivable compa)))
    compa

compIQtrEqClosed : {n : ℕ} -> {a b : RawTerm} {A : RawType}
  -> Computable n (hasTy [] a A)
  -> Computable n (hasTy [] b A)
  -> Computable n (termEq [] (tmClass a) (tmClass b) (tyQtr A))
compIQtrEqClosed {n} compa compb =
  compTmEqClosedQtr
    (iQtrEq (compToDerivable compa) (compToDerivable compb))
    (compIQtrClosed compa)
    (compIQtrClosed compb)
    evalQtr
    evalClass
    evalClass
    compa
    compb

compCQtrClosed : {n : ℕ} -> {a l : RawTerm} {A L : RawType}
  -> HypComputable (suc n) (isType ((tyQtr A) ∷ []) L)
  -> Computable n (hasTy [] a A)
  -> (dBranch : Derivable (isType (A ∷ []) (qtrBranchTy L)))
  -> (dl : Derivable (hasTy (A ∷ []) l (qtrBranchTy L)))
  -> Computable n
       (hasTy [] (subTm (qtrCompSub a) l) (subTy (qtrCompSub a) (qtrBranchTy L)))
  -> HypComputable (suc n)
       (termEq (wkTyBy 1 A ∷ A ∷ []) (wkTmBy 1 l) (renTm qtrSecondBranchRen l) (qtrCohTy L))
  -> Computable n
       (termEq [] (tmElQtr l (tmClass a)) (subTm (qtrCompSub a) l)
         (subTy (singleSubst (tmClass a)) L))
compCQtrClosed {n} {a = a} {l = l} {A = A} {L = L}
  compL compa dBranch dl rawBody coh =
  lhsEq body
  where
  dL : Derivable (isType ((tyQtr A) ∷ []) L)
  dL = hypCompToDerivable compL

  da : Derivable (hasTy [] a A)
  da = compToDerivable compa

  dcoh : Derivable
    (termEq (wkTyBy 1 A ∷ A ∷ []) (wkTmBy 1 l) (renTm qtrSecondBranchRen l) (qtrCohTy L))
  dcoh = hypCompToDerivable coh

  body : Computable n
    (hasTy [] (subTm (qtrCompSub a) l) (subTy (singleSubst (tmClass a)) L))
  body =
    subst
      (λ T -> Computable n (hasTy [] (subTm (qtrCompSub a) l) T))
      (qtrBranchTyComp a L)
      rawBody

  dEq : Derivable
    (termEq [] (tmElQtr l (tmClass a)) (subTm (qtrCompSub a) l)
      (subTy (singleSubst (tmClass a)) L))
  dEq = cQtr dL da dBranch dl dcoh

  dLeft : Derivable
    (hasTy [] (tmElQtr l (tmClass a)) (subTy (singleSubst (tmClass a)) L))
  dLeft = assocTmLeft dEq

  lhsEq : 
    Computable n
      (hasTy [] (subTm (qtrCompSub a) l) (subTy (singleSubst (tmClass a)) L))
    -> Computable n
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

compSubKeepBy : (sigma : Subst) (k : ℕ)
  -> compSub sigma (keepSubstBy k) ≡ dropSubstBy k sigma
compSubKeepBy sigma k = refl

subTyWkBy : (sigma : Subst) (k : ℕ) (A : RawType)
  -> subTy sigma (wkTyBy k A) ≡ subTy (dropSubstBy k sigma) A
subTyWkBy sigma k A =
  cong (subTy sigma) (renTyKeepSubstBy k A)
  ∙ subTyComp sigma (keepSubstBy k) A
  ∙ cong (λ rho -> subTy rho A) (compSubKeepBy sigma k)

subTmWkBy : (sigma : Subst) (k : ℕ) (t : RawTerm)
  -> subTm sigma (wkTmBy k t) ≡ subTm (dropSubstBy k sigma) t
subTmWkBy sigma k t =
  cong (subTm sigma) (renTmKeepSubstBy k t)
  ∙ subTmComp sigma (keepSubstBy k) t
  ∙ cong (λ rho -> subTm rho t) (compSubKeepBy sigma k)

wkTyBy0 : (A : RawType) -> wkTyBy 0 A ≡ A
wkTyBy0 A =
  renTyKeepSubstBy 0 A
  ∙ cong (λ sigma -> subTy sigma A) keepSubstBy0Id
  ∙ subTyId A

dropCons : (t : RawTerm) (sigma : Subst) (k : ℕ)
  -> dropSubstBy (suc k) (consSubst t sigma) ≡ dropSubstBy k sigma
dropCons t sigma k = refl

subTyWkStep : (t : RawTerm) (sigma : Subst) (k : ℕ) (A : RawType)
  -> subTy (consSubst t sigma) (wkTyBy (suc k) A)
   ≡ subTy sigma (wkTyBy k A)
subTyWkStep t sigma k A =
  subTyWkBy (consSubst t sigma) (suc k) A
  ∙ cong (λ rho -> subTy rho A) (dropCons t sigma k)
  ∙ sym (subTyWkBy sigma k A)

lookupCompFits : {n : ℕ} -> {delta gamma : Ctx} {A : RawType} {sigma : Subst}
  {fits : FitsSubst [] (delta ++ (A ∷ gamma)) sigma}
  -> ComputableFits n fits
  -> Computable n
       (hasTy [] (subTm sigma (var (length delta)))
         (subTy sigma (wkTyBy (suc (length delta)) A)))
lookupCompFits {n} {delta = []} {A = A}
  {fits = fitsCons {sigma = sigma} {t = t} fits dt}
  (compFitsCons compFits compt) =
  subst
    (λ T -> Computable n (hasTy [] t T))
    (sym (subTyWkStep t sigma 0 A ∙ cong (subTy sigma) (wkTyBy0 A)))
    compt
lookupCompFits {n} {delta = D ∷ delta} {A = A}
  {fits = fitsCons {sigma = sigma} {t = t} fits dt}
  (compFitsCons compFits compt) =
  subst
    (λ T -> Computable n (hasTy [] (subTm sigma (var (length delta))) T))
    (sym (subTyWkStep t sigma (suc (length delta)) A))
    (lookupCompFits {delta = delta} {A = A} {sigma = sigma} {fits = fits} compFits)

lookupCompFitsEq : {n : ℕ} -> {delta gamma : Ctx} {A : RawType} {sigma tau : Subst}
  {fitsEq : FitsEqSubst [] (delta ++ (A ∷ gamma)) sigma tau}
  -> ComputableFitsEq n fitsEq
  -> Computable n
       (termEq [] (subTm sigma (var (length delta))) (subTm tau (var (length delta)))
         (subTy sigma (wkTyBy (suc (length delta)) A)))
lookupCompFitsEq {n} {delta = []} {A = A}
  {fitsEq = fitsEqCons {sigma = sigma} {tau = tau} {t = t} {u = u} fitsEq dtu}
  (compFitsEqCons compFitsEq comptu) =
  subst
    (λ T -> Computable n (termEq [] t u T))
    (sym (subTyWkStep t sigma 0 A ∙ cong (subTy sigma) (wkTyBy0 A)))
    comptu
lookupCompFitsEq {n} {delta = D ∷ delta} {A = A}
  {fitsEq = fitsEqCons {sigma = sigma} {tau = tau} {t = t} {u = u} fitsEq dtu}
  (compFitsEqCons compFitsEq comptu) =
  subst
    (λ T ->
      Computable n
        (termEq [] (subTm sigma (var (length delta))) (subTm tau (var (length delta))) T))
    (sym (subTyWkStep t sigma (suc (length delta)) A))
    (lookupCompFitsEq
      {delta = delta} {A = A} {sigma = sigma} {tau = tau} {fitsEq = fitsEq}
      compFitsEq)

substCompFits : {n : ℕ} -> {delta : Ctx} {sigma tau : Subst}
  -> (p : sigma ≡ tau)
  -> {fits : FitsSubst [] delta sigma}
  -> ComputableFits n fits
  -> ComputableFits n (subst (λ rho -> FitsSubst [] delta rho) p fits)
substCompFits refl compFits = compFits

substCompFitsEqLeft : {n : ℕ} -> {delta : Ctx} {sigma sigma' tau : Subst}
  -> (p : sigma ≡ sigma')
  -> {fitsEq : FitsEqSubst [] delta sigma tau}
  -> ComputableFitsEq n fitsEq
  -> ComputableFitsEq n (subst (λ rho -> FitsEqSubst [] delta rho tau) p fitsEq)
substCompFitsEqLeft refl compFitsEq = compFitsEq

substCompFitsEqRight : {n : ℕ} -> {delta : Ctx} {sigma tau tau' : Subst}
  -> (p : tau ≡ tau')
  -> {fitsEq : FitsEqSubst [] delta sigma tau}
  -> ComputableFitsEq n fitsEq
  -> ComputableFitsEq n (subst (λ rho -> FitsEqSubst [] delta sigma rho) p fitsEq)
substCompFitsEqRight refl compFitsEq = compFitsEq

dropFits : {delta : Ctx} {sigma : Subst}
  -> (drop : Ctx)
  -> FitsSubst [] (drop ++ delta) sigma
  -> FitsSubst [] delta (dropSubstBy (length drop) sigma)
dropFits {delta = delta} {sigma = sigma} [] fits = fits
dropFits {delta = delta} {sigma = sigma} (A ∷ drop)
  (fitsCons {sigma = sigmaTail} {t = t} fits dt) =
  subst
    (λ rho -> FitsSubst [] delta rho)
    (dropCons t sigmaTail (length drop))
    (dropFits {delta = delta} {sigma = sigmaTail} drop fits)

dropFitsEq : {delta : Ctx} {sigma tau : Subst}
  -> (drop : Ctx)
  -> FitsEqSubst [] (drop ++ delta) sigma tau
  -> FitsEqSubst [] delta (dropSubstBy (length drop) sigma) (dropSubstBy (length drop) tau)
dropFitsEq {delta = delta} {sigma = sigma} {tau = tau} [] fitsEq = fitsEq
dropFitsEq {delta = delta} {sigma = sigma} {tau = tau} (A ∷ drop)
  (fitsEqCons {sigma = sigmaTail} {tau = tauTail} {t = t} {u = u} fitsEq dtu) =
  subst
    (λ rho ->
      FitsEqSubst [] delta rho
        (dropSubstBy (suc (length drop)) (consSubst u tauTail)))
    (dropCons t sigmaTail (length drop))
    (subst
      (λ rho ->
        FitsEqSubst [] delta
          (dropSubstBy (suc (length drop)) (consSubst t sigmaTail))
          rho)
      (dropCons u tauTail (length drop))
      (dropFitsEq {delta = delta} {sigma = sigmaTail} {tau = tauTail} drop fitsEq))

dropCompFits : {n : ℕ} -> {delta : Ctx} {sigma : Subst}
  -> (drop : Ctx)
  -> {fits : FitsSubst [] (drop ++ delta) sigma}
  -> ComputableFits n fits
  -> ComputableFits n (dropFits {delta = delta} {sigma = sigma} drop fits)
dropCompFits {n} [] compFits = compFits
dropCompFits {n} {delta = delta} (A ∷ drop)
  {fits = fitsCons {sigma = sigmaTail} {t = t} fits dt}
  (compFitsCons compFits compt) =
  substCompFits
    (dropCons t sigmaTail (length drop))
    (dropCompFits {delta = delta} {sigma = sigmaTail} drop {fits = fits} compFits)

dropCompFitsEq : {n : ℕ} -> {delta : Ctx} {sigma tau : Subst}
  -> (drop : Ctx)
  -> {fitsEq : FitsEqSubst [] (drop ++ delta) sigma tau}
  -> ComputableFitsEq n fitsEq
  -> ComputableFitsEq n (dropFitsEq {delta = delta} {sigma = sigma} {tau = tau} drop fitsEq)
dropCompFitsEq {n} [] compFitsEq = compFitsEq
dropCompFitsEq {n} {delta = delta} (A ∷ drop)
  {fitsEq = fitsEqCons {sigma = sigmaTail} {tau = tauTail} {t = t} {u = u} fitsEq dtu}
  (compFitsEqCons compFitsEq comptu) =
  substCompFitsEqLeft
    (dropCons t sigmaTail (length drop))
    (substCompFitsEqRight
      (dropCons u tauTail (length drop))
      (dropCompFitsEq
        {delta = delta} {sigma = sigmaTail} {tau = tauTail} drop {fitsEq = fitsEq}
        compFitsEq))

liftFits : {theta gamma : Ctx} {A : RawType} {sigma : Subst}
  -> FitsSubst theta gamma sigma
  -> Derivable (isType theta (subTy sigma A))
  -> FitsSubst (subTy sigma A ∷ theta) (A ∷ gamma)
       (consSubst (var zero) (compSub (keepSubstCtx 1 theta) sigma))
liftFits {theta = theta} {gamma = gamma} {A = A} {sigma = sigma} fits dAσ =
  fitsCons tail headVar
  where
  wfAσ : CtxWF (subTy sigma A ∷ theta)
  wfAσ = wfCons (fitsSubstCtxWF fits) dAσ

  tail : FitsSubst (subTy sigma A ∷ theta) gamma (compSub (keepSubstCtx 1 theta) sigma)
  tail =
    composeFits
      (fitsKeep {delta = subTy sigma A ∷ []} {gamma = theta} wfAσ)
      fits

  headVar0 : Derivable
    (hasTy (subTy sigma A ∷ theta) (var zero) (wkTyBy 1 (subTy sigma A)))
  headVar0 = varStar {gamma = theta} {delta = []} {A = subTy sigma A} wfAσ dAσ

  headVar : Derivable
    (hasTy (subTy sigma A ∷ theta) (var zero) (subTy (compSub (keepSubstCtx 1 theta) sigma) A))
  headVar =
    subst
      (λ T -> Derivable (hasTy (subTy sigma A ∷ theta) (var zero) T))
      (renTyKeepSubstBy 1 (subTy sigma A)
        ∙ sym (keepSubstCtx-subTy 1 theta (subTy sigma A))
        ∙ subTyComp (keepSubstCtx 1 theta) sigma A)
      headVar0

liftFitsOne : {gamma : Ctx} {A : RawType} {sigma : Subst}
  -> FitsSubst [] gamma sigma
  -> Derivable (isType [] (subTy sigma A))
  -> FitsSubst (subTy sigma A ∷ []) (A ∷ gamma)
       (consSubst (var zero) (compSub (keepSubstBy 1) sigma))
liftFitsOne = liftFits

liftFitsEq : {theta gamma : Ctx} {A : RawType} {sigma tau : Subst}
  -> FitsEqSubst theta gamma sigma tau
  -> Derivable (isType theta (subTy sigma A))
  -> FitsEqSubst (subTy sigma A ∷ theta) (A ∷ gamma)
       (consSubst (var zero) (compSub (keepSubstCtx 1 theta) sigma))
       (consSubst (var zero) (compSub (keepSubstCtx 1 theta) tau))
liftFitsEq {theta = theta} {gamma = gamma} {A = A} {sigma = sigma} {tau = tau} fitsEq dAσ =
  fitsEqCons tail (reflTm headVar)
  where
  wfAσ : CtxWF (subTy sigma A ∷ theta)
  wfAσ = wfCons (fitsEqSubstCtxWF fitsEq) dAσ

  tail : FitsEqSubst (subTy sigma A ∷ theta) gamma
    (compSub (keepSubstCtx 1 theta) sigma)
    (compSub (keepSubstCtx 1 theta) tau)
  tail =
    composeFitsEq
      (fitsKeep {delta = subTy sigma A ∷ []} {gamma = theta} wfAσ)
      fitsEq

  headVar0 : Derivable
    (hasTy (subTy sigma A ∷ theta) (var zero) (wkTyBy 1 (subTy sigma A)))
  headVar0 = varStar {gamma = theta} {delta = []} {A = subTy sigma A} wfAσ dAσ

  headVar : Derivable
    (hasTy (subTy sigma A ∷ theta) (var zero) (subTy (compSub (keepSubstCtx 1 theta) sigma) A))
  headVar =
    subst
      (λ T -> Derivable (hasTy (subTy sigma A ∷ theta) (var zero) T))
      (renTyKeepSubstBy 1 (subTy sigma A)
        ∙ sym (keepSubstCtx-subTy 1 theta (subTy sigma A))
        ∙ subTyComp (keepSubstCtx 1 theta) sigma A)
      headVar0

liftFitsEqOne : {gamma : Ctx} {A : RawType} {sigma tau : Subst}
  -> FitsEqSubst [] gamma sigma tau
  -> Derivable (isType [] (subTy sigma A))
  -> FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma)
       (consSubst (var zero) (compSub (keepSubstBy 1) sigma))
       (consSubst (var zero) (compSub (keepSubstBy 1) tau))
liftFitsEqOne = liftFitsEq

abstract
  liftSubstCompKeep : (sigma : Subst)
    -> consSubst (var zero) (compSub (keepSubstBy 1) sigma) ≡ liftSubst sigma
  liftSubstCompKeep sigma = cong (consSubst (var zero)) (compSubKeep1RenSub sigma)

  compSubIdLeft : (sigma : Subst) -> compSub idSubst sigma ≡ sigma
  compSubIdLeft (shiftSub zero) = refl
  compSubIdLeft (shiftSub (suc k)) = refl
  compSubIdLeft (consSub t sigma) =
    cong₂ consSubst (subTmId t) (compSubIdLeft sigma)

  dropSub1-compose : (tau : Subst) (k : ℕ)
    -> dropSubstBy (suc k) (dropSubstBy 1 tau) ≡ dropSubstBy (suc (suc k)) tau
  dropSub1-compose (shiftSub j) k = cong shiftSub (+-assoc j 1 (suc k))
  dropSub1-compose (consSub t tau) k = refl

  compSubDrop1RenSub : (tau sigma : Subst)
    -> compSub (dropSubstBy 1 tau) sigma ≡ compSub tau (renSub sucRen sigma)
  compSubDrop1RenSub tau (shiftSub zero) = refl
  compSubDrop1RenSub tau (shiftSub (suc k)) = dropSub1-compose tau k
  compSubDrop1RenSub tau (consSub t sigma) =
    cong₂ consSubst (sym (subTmRen tau sucRen t)) (compSubDrop1RenSub tau sigma)

  oneBinderCompSub : (tau sigma : Subst)
    -> consSubst (applySubst tau zero) (compSub (dropSubstBy 1 tau) sigma) ≡ compSub tau (liftSubst sigma)
  oneBinderCompSub tau sigma =
    cong (consSubst (applySubst tau zero)) (compSubDrop1RenSub tau sigma)

  keepSubstCtx1 : Subst
  keepSubstCtx1 = consSubst (var (suc zero)) (keepSubstBy 2)

  keepSubstCtx1RenSubComp : (sigma : Subst)
    -> compSub keepSubstCtx1 (renSub sucRen sigma)
       ≡ compSub (keepSubstBy 1) (renSub sucRen sigma)
  keepSubstCtx1RenSubComp (shiftSub zero) = refl
  keepSubstCtx1RenSubComp (shiftSub (suc k)) = refl
  keepSubstCtx1RenSubComp (consSub t sigma) =
    cong₂ consSubst
      (subTmRen keepSubstCtx1 sucRen t ∙ sym (subTmRen (keepSubstBy 1) sucRen t))
      (keepSubstCtx1RenSubComp sigma)

  keepSubstCtx1LiftComp : (sigma : Subst)
    -> compSub keepSubstCtx1 (liftSubst sigma)
       ≡ compSub (keepSubstBy 1) (liftSubst sigma)
  keepSubstCtx1LiftComp sigma =
    cong (consSubst (var (suc zero))) (keepSubstCtx1RenSubComp sigma)

  keepSubstCtx1LiftCompFor : (X : RawType) (sigma : Subst)
    -> compSub (keepSubstCtx 1 (X ∷ [])) (liftSubst sigma)
       ≡ compSub (keepSubstBy 1) (liftSubst sigma)
  keepSubstCtx1LiftCompFor X sigma = keepSubstCtx1LiftComp sigma

composeOneBinder : {gamma : Ctx} {A : RawType} {sigma tau : Subst}
  -> FitsSubst [] gamma sigma
  -> Derivable (isType [] (subTy sigma A))
  -> FitsSubst [] (subTy sigma A ∷ []) tau
  -> FitsSubst [] (A ∷ gamma) (compSub tau (liftSubst sigma))
composeOneBinder {gamma = gamma} {A = A} {sigma = sigma} {tau = tau} fits dAσ fits2 =
  subst
    (λ rho -> FitsSubst [] (A ∷ gamma) rho)
    (cong (compSub tau) (liftSubstCompKeep sigma))
    (composeFits fits2 (liftFitsOne fits dAσ))

composeOneBinderEq : {gamma : Ctx} {A : RawType} {sigma tau₁ tau₂ : Subst}
  -> FitsSubst [] gamma sigma
  -> Derivable (isType [] (subTy sigma A))
  -> FitsEqSubst [] (subTy sigma A ∷ []) tau₁ tau₂
  -> FitsEqSubst [] (A ∷ gamma) (compSub tau₁ (liftSubst sigma)) (compSub tau₂ (liftSubst sigma))
composeOneBinderEq {gamma = gamma} {A = A} {sigma = sigma} {tau₁ = tau₁} {tau₂ = tau₂} fits dAσ fitsEq =
  subst
    (λ rho -> FitsEqSubst [] (A ∷ gamma) rho (compSub tau₂ (liftSubst sigma)))
    (cong (compSub tau₁) (liftSubstCompKeep sigma))
    (subst
      (λ rho ->
        FitsEqSubst [] (A ∷ gamma)
          (compSub tau₁ (consSubst (var zero) (compSub (keepSubstBy 1) sigma)))
          rho)
      (cong (compSub tau₂) (liftSubstCompKeep sigma))
      (composeEqFits fitsEq (liftFitsOne fits dAσ)))

composeTwoBinders : {gamma : Ctx} {A B : RawType} {sigma tau : Subst}
  -> FitsSubst [] gamma sigma
  -> Derivable (isType [] (subTy sigma A))
  -> Derivable (isType (subTy sigma A ∷ []) (subTy (liftSubst sigma) B))
  -> FitsSubst [] (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) tau
  -> FitsSubst [] (B ∷ A ∷ gamma) (compSub tau (liftSubst (liftSubst sigma)))
composeTwoBinders {gamma = gamma} {A = A} {B = B} {sigma = sigma} {tau = tau} fits dAσ dBσ fits2 =
  let
    lifted1 : FitsSubst (subTy sigma A ∷ []) (A ∷ gamma) (liftSubst sigma)
    lifted1 =
      subst
        (λ rho -> FitsSubst (subTy sigma A ∷ []) (A ∷ gamma) rho)
        (liftSubstCompKeep sigma)
        (liftFitsOne fits dAσ)
  in
  subst
    (λ rho -> FitsSubst [] (B ∷ A ∷ gamma) rho)
    (cong (compSub tau) (liftSubstCompKeep (liftSubst sigma)))
    (subst
      (λ rho -> FitsSubst [] (B ∷ A ∷ gamma) (compSub tau rho))
      (cong (consSubst (var zero)) (keepSubstCtx1LiftCompFor (subTy sigma A) sigma))
      (composeFits fits2 (liftFits lifted1 dBσ)))

composeTwoBindersEq : {gamma : Ctx} {A B : RawType} {sigma tau₁ tau₂ : Subst}
  -> FitsSubst [] gamma sigma
  -> Derivable (isType [] (subTy sigma A))
  -> Derivable (isType (subTy sigma A ∷ []) (subTy (liftSubst sigma) B))
  -> FitsEqSubst [] (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) tau₁ tau₂
  -> FitsEqSubst [] (B ∷ A ∷ gamma)
       (compSub tau₁ (liftSubst (liftSubst sigma)))
       (compSub tau₂ (liftSubst (liftSubst sigma)))
composeTwoBindersEq {gamma = gamma} {A = A} {B = B} {sigma = sigma} {tau₁ = tau₁} {tau₂ = tau₂} fits dAσ dBσ fitsEq =
  let
    lifted1 : FitsSubst (subTy sigma A ∷ []) (A ∷ gamma) (liftSubst sigma)
    lifted1 =
      subst
        (λ rho -> FitsSubst (subTy sigma A ∷ []) (A ∷ gamma) rho)
        (liftSubstCompKeep sigma)
        (liftFitsOne fits dAσ)
    lifted2ctx : Subst
    lifted2ctx =
      consSubst (var zero)
        (compSub (keepSubstCtx 1 (subTy sigma A ∷ [])) (liftSubst sigma))
    lifted2Path : lifted2ctx ≡ liftSubst (liftSubst sigma)
    lifted2Path =
      cong (consSubst (var zero)) (keepSubstCtx1LiftCompFor (subTy sigma A) sigma)
      ∙ liftSubstCompKeep (liftSubst sigma)
  in
  subst
    (λ rho ->
      FitsEqSubst [] (B ∷ A ∷ gamma) rho (compSub tau₂ (liftSubst (liftSubst sigma))))
    (cong (compSub tau₁) lifted2Path)
    (subst
      (λ rho ->
        FitsEqSubst [] (B ∷ A ∷ gamma)
          (compSub tau₁ lifted2ctx)
          rho)
      (cong (compSub tau₂) lifted2Path)
      (composeEqFits fitsEq (liftFits lifted1 dBσ)))

singleSubstLiftTailFor : (sigma : Subst) (v : RawTerm)
  -> compSub (singleSubst v) (renSub sucRen sigma) ≡ sigma
singleSubstLiftTailFor (shiftSub zero) v = refl
singleSubstLiftTailFor (shiftSub (suc k)) v = refl
singleSubstLiftTailFor (consSub u sigma) v =
  cong₂ consSubst
    (subTmRen (singleSubst v) sucRen u ∙ subTmId u)
    (singleSubstLiftTailFor sigma v)

singleSubstLiftTail : (sigma : Subst) (t : RawTerm)
  -> compSub (singleSubst (subTm sigma t)) (renSub sucRen sigma) ≡ sigma
singleSubstLiftTail sigma t = singleSubstLiftTailFor sigma (subTm sigma t)

singleSubstCompLift : (sigma : Subst) (t : RawTerm)
  -> compSub (singleSubst (subTm sigma t)) (liftSubst sigma) ≡ compSub sigma (singleSubst t)
singleSubstCompLift sigma t =
  cong (consSubst (subTm sigma t)) (singleSubstLiftTail sigma t)

qtrBranchSubLiftTail : (sigma : Subst)
  -> compSub qtrBranchSub (renSub sucRen sigma) ≡ renSub sucRen sigma
qtrBranchSubLiftTail (shiftSub zero) = refl
qtrBranchSubLiftTail (shiftSub (suc k)) = refl
qtrBranchSubLiftTail (consSub t sigma) =
  cong₂ consSubst
    (subTmRen qtrBranchSub sucRen t ∙ sym (renTmKeepSubstBy 1 t))
    (qtrBranchSubLiftTail sigma)

qtrBranchSubLiftComp : (sigma : Subst)
  -> compSub (liftSubst sigma) qtrBranchSub ≡ compSub qtrBranchSub (liftSubst sigma)
qtrBranchSubLiftComp sigma =
  cong (consSubst (tmClass (var zero))) (sym (qtrBranchSubLiftTail sigma))

sigmaCompSubLiftComp : (sigma : Subst) (b c : RawTerm)
  -> compSub sigma (sigmaCompSub b c)
   ≡ compSub (sigmaCompSub (subTm sigma b) (subTm sigma c)) (liftSubst (liftSubst sigma))
sigmaCompSubLiftComp sigma b c =
  cong (consSubst (subTm sigma c)) (sym (singleSubstCompLift sigma b))
  ∙ oneBinderCompSub (sigmaCompSub (subTm sigma b) (subTm sigma c)) (liftSubst sigma)

sigmaMotSubLiftTail : (sigma : Subst)
  -> compSub sigmaMotSub (renSub sucRen sigma) ≡ dropSubstBy 2 (liftSubst (liftSubst sigma))
sigmaMotSubLiftTail (shiftSub zero) = refl
sigmaMotSubLiftTail (shiftSub (suc k)) = refl
sigmaMotSubLiftTail (consSub t sigma) =
  cong₂ consSubst
    (subTmRen sigmaMotSub sucRen t
      ∙ sym (renTmKeepSubstBy 2 t)
      ∙ sym (renTmComp sucRen sucRen t))
    (sigmaMotSubLiftTail sigma)

sigmaMotSubLiftComp : (sigma : Subst)
  -> compSub (liftSubst (liftSubst sigma)) sigmaMotSub ≡ compSub sigmaMotSub (liftSubst sigma)
sigmaMotSubLiftComp sigma =
  cong (consSubst (tmPair (var (suc zero)) (var zero))) (sym (sigmaMotSubLiftTail sigma))

qtrCohSubLiftTail : (sigma : Subst)
  -> compSub qtrCohSub (renSub sucRen sigma) ≡ dropSubstBy 2 (liftSubst (liftSubst sigma))
qtrCohSubLiftTail (shiftSub zero) = refl
qtrCohSubLiftTail (shiftSub (suc k)) = refl
qtrCohSubLiftTail (consSub t sigma) =
  cong₂ consSubst
    (subTmRen qtrCohSub sucRen t
      ∙ sym (renTmKeepSubstBy 2 t)
      ∙ sym (renTmComp sucRen sucRen t))
    (qtrCohSubLiftTail sigma)

qtrCohSubLiftComp : (sigma : Subst)
  -> compSub (liftSubst (liftSubst sigma)) qtrCohSub ≡ compSub qtrCohSub (liftSubst sigma)
qtrCohSubLiftComp sigma =
  cong (consSubst (tmClass (var (suc zero)))) (sym (qtrCohSubLiftTail sigma))

sigmaBranchTyLiftComp : (sigma : Subst) (M : RawType)
  -> subTy (liftSubst (liftSubst sigma)) (sigmaBranchTy M)
       ≡ sigmaBranchTy (subTy (liftSubst sigma) M)
sigmaBranchTyLiftComp sigma M =
  subTyComp (liftSubst (liftSubst sigma)) sigmaMotSub M
  ∙ cong (λ rho -> subTy rho M) (sigmaMotSubLiftComp sigma)
  ∙ sym (subTyComp sigmaMotSub (liftSubst sigma) M)

qtrBranchTyLiftComp : (sigma : Subst) (L : RawType)
  -> subTy (liftSubst sigma) (qtrBranchTy L)
       ≡ qtrBranchTy (subTy (liftSubst sigma) L)
qtrBranchTyLiftComp sigma L =
  subTyComp (liftSubst sigma) qtrBranchSub L
  ∙ cong (λ rho -> subTy rho L) (qtrBranchSubLiftComp sigma)
  ∙ sym (subTyComp qtrBranchSub (liftSubst sigma) L)

qtrCohTyLiftComp : (sigma : Subst) (L : RawType)
  -> subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)
       ≡ qtrCohTy (subTy (liftSubst sigma) L)
qtrCohTyLiftComp sigma L =
  subTyComp (liftSubst (liftSubst sigma)) qtrCohSub L
  ∙ cong (λ rho -> subTy rho L) (qtrCohSubLiftComp sigma)
  ∙ sym (subTyComp qtrCohSub (liftSubst sigma) L)

qtrSecondBranchSubLiftTail : (sigma : Subst)
  -> renSub qtrSecondBranchRen (renSub sucRen sigma) ≡ dropSubstBy 2 (liftSubst (liftSubst sigma))
qtrSecondBranchSubLiftTail (shiftSub zero) = refl
qtrSecondBranchSubLiftTail (shiftSub (suc k)) = refl
qtrSecondBranchSubLiftTail (consSub t sigma) =
  cong₂ consSubst
    (renTmComp qtrSecondBranchRen sucRen t ∙ sym (renTmComp sucRen sucRen t))
    (qtrSecondBranchSubLiftTail sigma)

qtrSecondBranchSubLiftComp : (sigma : Subst)
  -> compSubRen (liftSubst (liftSubst sigma)) qtrSecondBranchRen
       ≡ renSub qtrSecondBranchRen (liftSubst sigma)
qtrSecondBranchSubLiftComp sigma =
  cong (consSubst (var zero)) (sym (qtrSecondBranchSubLiftTail sigma))

qtrSecondBranchTmLiftComp : (sigma : Subst) (l : RawTerm)
  -> subTm (liftSubst (liftSubst sigma)) (renTm qtrSecondBranchRen l)
       ≡ renTm qtrSecondBranchRen (subTm (liftSubst sigma) l)
qtrSecondBranchTmLiftComp sigma l =
  subTmRen (liftSubst (liftSubst sigma)) qtrSecondBranchRen l
  ∙ cong
      (λ theta -> subTm theta l)
      (qtrSecondBranchSubLiftComp sigma)
  ∙ sym (renTmSub qtrSecondBranchRen (liftSubst sigma) l)

qtrCompSubLiftComp : (sigma : Subst) (a : RawTerm)
  -> compSub sigma (qtrCompSub a)
       ≡ compSub (qtrCompSub (subTm sigma a)) (liftSubst sigma)
qtrCompSubLiftComp sigma a =
  cong
    (compSub sigma)
    (sym (singleSubstConsKeep a ∙ cong (consSubst a) keepSubstBy0Id))
  ∙ sym (singleSubstCompLift sigma a)
  ∙ cong
      (λ rho -> compSub rho (liftSubst sigma))
      (singleSubstConsKeep (subTm sigma a)
        ∙ cong (consSubst (subTm sigma a)) keepSubstBy0Id)

qtrBranchTyWk : (L : RawType)
  -> wkTyBy 1 (qtrBranchTy L) ≡ qtrCohTy L
qtrBranchTyWk L =
  renTySub sucRen qtrBranchSub L

mutual
  leftTyWitnessEq : {gamma : Ctx} {A B : RawType}
    -> Derivable (typeEq gamma A B)
    -> Derivable (isType gamma A)
  leftTyWitnessEq (weakenTyEq d wf) = weakenTy (leftTyWitnessEq d) wf
  leftTyWitnessEq (reflTy d) = d
  leftTyWitnessEq (symTy _ dB) = dB
  leftTyWitnessEq (transTy d _) = leftTyWitnessEq d
  leftTyWitnessEq (substTyEqRule d fits) = substTyRule (leftTyWitnessEq d) fits
  leftTyWitnessEq (eqSubTyRule d fits) = substTyRule d (fitsEqSubstLeft fits)
  leftTyWitnessEq (eqSubTyEqRule d fits) =
    substTyRule (leftTyWitnessEq d) (fitsEqSubstLeft fits)
  leftTyWitnessEq (fSigmaEq dAC dB _) = fSigma (leftTyWitnessEq dAC) dB
  leftTyWitnessEq (fEqEq dAC dac dbd) =
    fEq (leftTyWitnessEq dAC) (leftTmWitnessEq dac) (leftTmWitnessEq dbd)
  leftTyWitnessEq (fQtrEq d) = fQtr (leftTyWitnessEq d)

  leftTmWitnessEq : {gamma : Ctx} {t u : RawTerm} {A : RawType}
    -> Derivable (termEq gamma t u A)
    -> Derivable (hasTy gamma t A)
  leftTmWitnessEq (weakenTmEq d wf) = weakenTm (leftTmWitnessEq d) wf
  leftTmWitnessEq (reflTm d) = d
  leftTmWitnessEq (symTm _ du _) = du
  leftTmWitnessEq (transTm d _) = leftTmWitnessEq d
  leftTmWitnessEq (convEq d dAB) = conv (leftTmWitnessEq d) dAB
  leftTmWitnessEq (substTmEqRule d fits) = substTmRule (leftTmWitnessEq d) fits
  leftTmWitnessEq (eqSubTmRule d fits) = substTmRule d (fitsEqSubstLeft fits)
  leftTmWitnessEq (eqSubTmEqRule d fits) =
    substTmRule (leftTmWitnessEq d) (fitsEqSubstLeft fits)
  leftTmWitnessEq (cTop d) = d
  leftTmWitnessEq (iSigmaEq d1 d2 dA dB) =
    iSigma (leftTmWitnessEq d1) (leftTmWitnessEq d2) (fSigma dA dB)
  leftTmWitnessEq (eSigmaEq dM dd dmL _) =
    eSigma dM (leftTmWitnessEq dd) dmL
  leftTmWitnessEq (cSigma dM dSigma db dc dm) =
    eSigma dM (iSigma db dc dSigma) dm
  leftTmWitnessEq (iEqEq d) = iEq (leftTmWitnessEq d)
  leftTmWitnessEq (eEqStar _ _ da _) = da
  leftTmWitnessEq (cEq p _ _ _) = p
  leftTmWitnessEq (iQtrEq da _) = iQtr da
  leftTmWitnessEq (eQtrEq dL dp dBranch dlL _ _ coh _) =
    eQtr dL (leftTmWitnessEq dp) dBranch dlL coh
  leftTmWitnessEq (cQtr dL da dBranch dl coh) =
    eQtr dL (iQtr da) dBranch dl coh

hypTyEqLeft : {n : ℕ} -> {gamma : Ctx} {A B : RawType}
  -> HypComputable (suc n) (typeEq gamma A B)
  -> HypComputable (suc n) (isType gamma A)
hypTyEqLeft {n} (hypTyEqOpen _ _ compA _ _) = compA

hypTmEqLeft : {n : ℕ} -> {gamma : Ctx} {t u : RawTerm} {A : RawType}
  -> HypComputable (suc n) (termEq gamma t u A)
  -> HypComputable (suc n) (hasTy gamma t A)
hypTmEqLeft {n} (hypTmEqOpen _ _ compt _ _) = compt

sigmaMotSubTailComp : (sigma : Subst) (b c : RawTerm)
  -> compSub (consSubst c (consSubst b sigma)) sigmaMotSub
     ≡ consSubst (tmPair b c) sigma
sigmaMotSubTailComp sigma b c = refl

abstract
  sigmaBranchTyCompTail : (sigma : Subst) (b c : RawTerm) (M : RawType)
    -> subTy (consSubst c (consSubst b sigma)) (sigmaBranchTy M)
       ≡ subTy (consSubst (tmPair b c) sigma) M
  sigmaBranchTyCompTail sigma b c M =
    subTyComp (consSubst c (consSubst b sigma)) sigmaMotSub M
    ∙ cong (λ theta -> subTy theta M) (sigmaMotSubTailComp sigma b c)
