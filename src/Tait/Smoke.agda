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
