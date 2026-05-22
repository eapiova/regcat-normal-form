{-# OPTIONS --safe #-}

-- Tait-style rebuild prototype (Phase K) — non-vacuity smoke test.
-- Builds a concrete closed derivation containing a Sigma ELIMINATOR
-- (`tmElSigma (tmPair tmStar tmStar) tmStar`) and checks that
-- `canonicalFormTheorem` genuinely reduces it to its normal form
-- `tmStar` — verified by `refl`, so the theorem really computes.

module Tait.Smoke where

open import Tait.Prelude
open import Data.List.Base using ([] ; _∷_)
open import Data.Product using (Σ-syntax ; _×_ ; _,_ ; proj₁)

open import Tait.Syntax
open import Tait.Context
open import Tait.Substitution
open import Tait.Evaluation
open import Tait.Derivability
open import Tait.CanonicalForm

wf1 : CtxWF (tyTop ∷ [])
wf1 = wfCons wfNil (fTop wfNil)

wf2 : CtxWF (tyTop ∷ tyTop ∷ [])
wf2 = wfCons wf1 (fTop wf1)

-- isType [] (tySigma tyTop tyTop)
dSig : Derivable (isType [] (tySigma tyTop tyTop))
dSig = fSigma (fTop wfNil) (fTop wf1)

-- the pair (*, *) : Sigma Top Top
dPair : Derivable (hasTy [] (tmPair tmStar tmStar) (tySigma tyTop tyTop))
dPair = iSigma (iTop wfNil) (iTop wfNil) dSig

-- motive M = Top over context (Sigma Top Top ∷ [])
dM : Derivable (isType (tySigma tyTop tyTop ∷ []) tyTop)
dM = fTop (wfCons wfNil dSig)

-- branch m = * : sigmaBranchTy Top  (= Top) over (Top ∷ Top ∷ [])
dBranch : Derivable (hasTy (tyTop ∷ tyTop ∷ []) tmStar (sigmaBranchTy tyTop))
dBranch = iTop wf2

-- the eliminator term, well-typed
dElim : Derivable
  (hasTy [] (tmElSigma (tmPair tmStar tmStar) tmStar)
            (subTy (singleSubst (tmPair tmStar tmStar)) tyTop))
dElim = eSigma dM dPair dBranch

-- the canonical-form theorem applied to it inhabits CanonicalForm.
smoke : CanonicalForm
  (hasTy [] (tmElSigma (tmPair tmStar tmStar) tmStar)
            (subTy (singleSubst (tmPair tmStar tmStar)) tyTop))
smoke = canonicalFormTheorem dElim

-- DECISIVE: the theorem computes the eliminator down to `tmStar`.
-- If this `refl` typechecks, normalisation genuinely ran.
smokeReduces : proj₁ (canonicalFormTheorem dElim) ≡ tmStar
smokeReduces = refl

-- Eq-type non-vacuity: refl at Top has canonical representative `tmR`.
dEqTy : Derivable (isType [] (tyEq tyTop tmStar tmStar))
dEqTy = fEq (fTop wfNil) (iTop wfNil) (iTop wfNil)

dEqTerm : Derivable (hasTy [] tmR (tyEq tyTop tmStar tmStar))
dEqTerm = iEq (iTop wfNil)

smokeEqReduces : proj₁ (canonicalFormTheorem dEqTerm) ≡ tmR
smokeEqReduces = refl

-- Qtr-type non-vacuity: a closed quotient eliminator computes to `tmStar`.
dQtrTy : Derivable (isType [] (tyQtr tyTop))
dQtrTy = fQtr (fTop wfNil)

dQtrClass : Derivable (hasTy [] (tmClass tmStar) (tyQtr tyTop))
dQtrClass = iQtr (iTop wfNil)

dQtrMotive : Derivable (isType (tyQtr tyTop ∷ []) tyTop)
dQtrMotive = fTop (wfCons wfNil dQtrTy)

dQtrBranchTy : Derivable (isType (tyTop ∷ []) (qtrBranchTy tyTop))
dQtrBranchTy = fTop wf1

dQtrBranch : Derivable (hasTy (tyTop ∷ []) tmStar (qtrBranchTy tyTop))
dQtrBranch = iTop wf1

dQtrCoh : Derivable
  (termEq (wkTyBy 1 tyTop ∷ tyTop ∷ [])
    (wkTmBy 1 tmStar)
    (renTm qtrSecondBranchRen tmStar)
    (qtrCohTy tyTop))
dQtrCoh = cTop (iTop wf2)

dQtrElim : Derivable
  (hasTy [] (tmElQtr tmStar (tmClass tmStar))
    (subTy (singleSubst (tmClass tmStar)) tyTop))
dQtrElim = eQtr dQtrMotive dQtrClass dQtrBranchTy dQtrBranch dQtrCoh

smokeQtrReduces : proj₁ (canonicalFormTheorem dQtrElim) ≡ tmStar
smokeQtrReduces = refl
