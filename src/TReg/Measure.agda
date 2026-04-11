{-# OPTIONS --safe #-}

module TReg.Measure where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_)
open import Cubical.Data.Nat.Properties using (max ; maxSuc)
open import Cubical.Data.Nat.Order using (_<_ ; _≤_ ; ≤-refl ; ≤-suc ; suc-≤-suc ; ≤SumLeft ; ≤SumRight ; <-wellfounded ; maxLUB)
open import Cubical.Induction.WellFounded using (Acc ; acc ; WellFounded)

open import TReg.Syntax
open import TReg.Context
open import TReg.Substitution using (Subst ; subTy ; subTm ; liftSubst)

-- Type depth: measures the nesting of type constructors
tyDepth : RawType -> ℕ
tyDepth tyTop = 0
tyDepth (tySigma A B) = suc (tyDepth A + tyDepth B)
tyDepth (tyEq A a b) = suc (tyDepth A)
tyDepth (tyQtr A) = suc (tyDepth A)

-- Substitution preserves type depth
tyDepth-subTy : (sigma : Subst) -> (A : RawType) -> tyDepth (subTy sigma A) ≡ tyDepth A
tyDepth-subTy sigma tyTop = refl
tyDepth-subTy sigma (tySigma A B) =
  cong suc (cong₂ _+_ (tyDepth-subTy sigma A) (tyDepth-subTy (liftSubst sigma) B))
tyDepth-subTy sigma (tyEq A a b) = cong suc (tyDepth-subTy sigma A)
tyDepth-subTy sigma (tyQtr A) = cong suc (tyDepth-subTy sigma A)

-- Comparison lemmas for Sigma components
tyDepth-fst<Sigma : (A B : RawType) -> tyDepth A < suc (tyDepth A + tyDepth B)
tyDepth-fst<Sigma A B = suc-≤-suc (≤SumLeft {tyDepth A} {tyDepth B})

tyDepth-snd<Sigma : (A B : RawType) -> tyDepth B < suc (tyDepth A + tyDepth B)
tyDepth-snd<Sigma A B = suc-≤-suc (≤SumRight {tyDepth B} {tyDepth A})

-- Comparison lemmas for Eq and Qtr components (n < suc n)
tyDepth-base<Eq : (A : RawType) (a b : RawTerm) -> tyDepth A < tyDepth (tyEq A a b)
tyDepth-base<Eq A a b = ≤-refl

tyDepth-base<Qtr : (A : RawType) -> tyDepth A < tyDepth (tyQtr A)
tyDepth-base<Qtr A = ≤-refl

max3 : ℕ -> ℕ -> ℕ -> ℕ
max3 a b c = max a (max b c)

max-< : {a b n : ℕ} -> a < n -> b < n -> max a b < n
max-< {a = a} {b = b} a<n b<n =
  subst (_≤ _) (maxSuc {n = a} {m = b}) (maxLUB a<n b<n)

max3-< : {a b c n : ℕ} -> a < n -> b < n -> c < n -> max3 a b c < n
max3-< a<n b<n c<n = max-< a<n (max-< b<n c<n)

-- Derivation size: counts constructor nodes in the derivation tree.
-- Used for the Acc-based termination argument in CompTheorem.
open import TReg.Derivability

mutual
  derivSize : {J : JForm} -> Derivable J -> ℕ
  derivSize (varStar wf dA) = suc (ctxWFSize wf + derivSize dA)
  derivSize (weakenTy d wf) = suc (derivSize d + ctxWFSize wf)
  derivSize (weakenTyEq d wf) = suc (derivSize d + ctxWFSize wf)
  derivSize (weakenTm d wf) = suc (derivSize d + ctxWFSize wf)
  derivSize (weakenTmEq d wf) = suc (derivSize d + ctxWFSize wf)
  derivSize (reflTy d) = suc (derivSize d)
  derivSize (reflTm d) = suc (derivSize d)
  derivSize (symTy d dB) = suc (derivSize d + derivSize dB)
  derivSize (symTm d du dA) = suc (derivSize d + derivSize du + derivSize dA)
  derivSize (transTy d₁ d₂) = suc (derivSize d₁ + derivSize d₂)
  derivSize (transTm d₁ d₂) = suc (derivSize d₁ + derivSize d₂)
  derivSize (conv d dAB) = suc (derivSize d + derivSize dAB)
  derivSize (convEq d dAB) = suc (derivSize d + derivSize dAB)
  derivSize (substTyRule d fits) = suc (derivSize d + fitsSize fits)
  derivSize (substTyEqRule d fits) = suc (derivSize d + fitsSize fits)
  derivSize (substTmRule d fits) = suc (derivSize d + fitsSize fits)
  derivSize (substTmEqRule d fits) = suc (derivSize d + fitsSize fits)
  derivSize (eqSubTyRule d fitsEq) = suc (derivSize d + fitsEqSize fitsEq)
  derivSize (eqSubTyEqRule d fitsEq) = suc (derivSize d + fitsEqSize fitsEq)
  derivSize (eqSubTmRule d fitsEq) = suc (derivSize d + fitsEqSize fitsEq)
  derivSize (eqSubTmEqRule d fitsEq) = suc (derivSize d + fitsEqSize fitsEq)
  derivSize (fTop wf) = suc (ctxWFSize wf)
  derivSize (iTop wf) = suc (ctxWFSize wf)
  derivSize (cTop d) = suc (derivSize d)
  derivSize (fSigma dA dB) = suc (derivSize dA + derivSize dB)
  derivSize (fSigmaEq dAC dB dBD) = suc (derivSize dAC + derivSize dB + derivSize dBD)
  derivSize (iSigma da db dSigma) = suc (derivSize da + derivSize db + derivSize dSigma)
  derivSize (iSigmaEq dac dbd dA dB) = suc (derivSize dac + derivSize dbd + derivSize dA + derivSize dB)
  derivSize (eSigma dM dd dm) = suc (derivSize dM + derivSize dd + derivSize dm)
  derivSize (eSigmaEq dM dd dm dm') = suc (derivSize dM + derivSize dd + derivSize dm + derivSize dm')
  derivSize (cSigma dM dSigma db dc dm) = suc (derivSize dM + derivSize dSigma + derivSize db + derivSize dc + derivSize dm)
  derivSize (fEq dA da db) = suc (derivSize dA + derivSize da + derivSize db)
  derivSize (fEqEq dAC dac dbd) = suc (derivSize dAC + derivSize dac + derivSize dbd)
  derivSize (iEq da) = suc (derivSize da)
  derivSize (iEqEq dab) = suc (derivSize dab)
  derivSize (eEqStar dp dA da db) = suc (derivSize dp + derivSize dA + derivSize da + derivSize db)
  derivSize (cEq dp dA da db) = suc (derivSize dp + derivSize dA + derivSize da + derivSize db)
  derivSize (fQtr dA) = suc (derivSize dA)
  derivSize (fQtrEq dAB) = suc (derivSize dAB)
  derivSize (iQtr da) = suc (derivSize da)
  derivSize (iQtrEq da db) = suc (derivSize da + derivSize db)
  derivSize (eQtr dL dp dBranchTy dl dcoh) = suc (derivSize dL + derivSize dp + derivSize dBranchTy + derivSize dl + derivSize dcoh)
  derivSize (eQtrEq dL dp dBranchTy dl dl' dll' dcoh dcoh') = suc (derivSize dL + derivSize dp + derivSize dBranchTy + derivSize dl + derivSize dl' + derivSize dll' + derivSize dcoh + derivSize dcoh')
  derivSize (cQtr dL da dBranchTy dl dcoh) = suc (derivSize dL + derivSize da + derivSize dBranchTy + derivSize dl + derivSize dcoh)

  ctxWFSize : {gamma : Ctx} -> CtxWF gamma -> ℕ
  ctxWFSize wfNil = 0
  ctxWFSize (wfCons wf dA) = suc (ctxWFSize wf + derivSize dA)

  fitsSize : {gamma delta : Ctx} {sigma : Subst} -> FitsSubst gamma delta sigma -> ℕ
  fitsSize (fitsNil wf) = ctxWFSize wf
  fitsSize (fitsCons fits dt) = suc (fitsSize fits + derivSize dt)

  fitsEqSize : {gamma delta : Ctx} {sigma tau : Subst} -> FitsEqSubst gamma delta sigma tau -> ℕ
  fitsEqSize (fitsEqNil wf) = ctxWFSize wf
  fitsEqSize (fitsEqCons fitsEq dtu) = suc (fitsEqSize fitsEq + derivSize dtu)

-- Basic derivSize decrease: sub-derivation is strictly smaller than the constructor
derivSize-sub< : {n m : ℕ} -> n ≤ n + m
derivSize-sub< {n} {m} = ≤SumLeft {n} {m}

-- derivSize of an entry dt in fitsCons is strictly smaller than the whole fits entry
derivSize-fitsEntry< : {gamma delta : Ctx} {sigma : Subst} {A : RawType} {t : RawTerm}
  -> (fits : FitsSubst gamma delta sigma)
  -> (dt : Derivable (hasTy gamma t (subTy sigma A)))
  -> derivSize dt < fitsSize (fitsCons fits dt)
derivSize-fitsEntry< fits dt = suc-≤-suc (≤SumRight {derivSize dt} {fitsSize fits})

-- Output type of a judgment form: the type that appears in the output position.
outputType : JForm -> RawType
outputType (isType _ A) = A
outputType (typeEq _ A _) = A
outputType (hasTy _ _ A) = A
outputType (termEq _ _ _ A) = A

-- The SCC 2 task measure: just tyDepth of the output type.
-- This is substitution-invariant (tyDepth-subTy) and weakening-invariant
-- (tyDepth-wkTy). The Acc parameter based on this handles the tyDepth-crossing
-- calls (fSigma head, fEq/fQtr components). Same-tyDepth calls (reflTy, symTy,
-- transTy, substTyRule, weakenTy, conv, etc.) are structurally decreasing on
-- the derivation and handled by Agda's SCT.
substTaskMeasure : {J : JForm} -> Derivable J -> ℕ
substTaskMeasure {J = J} _ = tyDepth (outputType J)

-- ═══════════════════════════════════════════════════════════════════
-- Decrease lemmas for substTaskMeasure
-- ═══════════════════════════════════════════════════════════════════

open import Cubical.Data.Nat.Order using (≤-trans ; <-+k ; ≤-+k ; ≤-k+)

-- Helper: a < b → a + k < b + k  (already available as <-+k)
-- Helper: a ≤ b → k + a ≤ k + b  (already available as ≤-k+)

-- When derivSize strictly decreases and tyDepth stays the same,
-- substTaskMeasure strictly decreases.
-- Proof: td * suc ds₁ + ds₁ < td * suc ds₂ + ds₂ when ds₁ < ds₂.
-- Since td * suc ds = td + td * ds, we have:
--   td + td * suc ds₁ + ds₁ < td + td * suc ds₂ + ds₂
-- The td prefix is the same, so it suffices to show
--   td * suc ds₁ + ds₁ < td * suc ds₂ + ds₂
-- which follows from ds₁ < ds₂ by monotonicity of * and +.

-- For now, we state the decrease lemmas we need for each SCC 2 case.
-- These will be proved as needed during Phase D.

-- derivSize strictly decreases for each sub-derivation:
derivSize-sub-suc< : {n m : ℕ} -> n < suc (n + m)
derivSize-sub-suc< {n} {m} = suc-≤-suc (≤SumLeft {n} {m})

derivSize-sub-suc-right< : {n m : ℕ} -> m < suc (n + m)
derivSize-sub-suc-right< {n} {m} = suc-≤-suc (≤SumRight {m} {n})

-- ═══════════════════════════════════════════════════════════════════
-- substTaskMeasure decrease lemmas
-- ═══════════════════════════════════════════════════════════════════

-- KEY LEMMA: If tyDepth of the output type strictly decreases,
-- substTaskMeasure decreases. With the simplified measure (just tyDepth),
-- this is trivial.
substMeasure-tyDepth< : {J₁ J₂ : JForm}
  -> (d₁ : Derivable J₁) -> (d₂ : Derivable J₂)
  -> tyDepth (outputType J₁) < tyDepth (outputType J₂)
  -> substTaskMeasure d₁ < substTaskMeasure d₂
substMeasure-tyDepth< _ _ p = p

-- Same tyDepth implies same substTaskMeasure (for sub-witnesses with refl)
substMeasure-sameTyDepth : {J₁ J₂ : JForm}
  -> (d₁ : Derivable J₁) -> (d₂ : Derivable J₂)
  -> tyDepth (outputType J₁) ≡ tyDepth (outputType J₂)
  -> substTaskMeasure d₁ ≡ substTaskMeasure d₂
substMeasure-sameTyDepth _ _ p = p

-- ═══════════════════════════════════════════════════════════════════
-- Concrete decrease lemmas for SCC 2 cases
-- ═══════════════════════════════════════════════════════════════════
-- These state the decrease conditions directly in terms of derivSize
-- and tyDepth, which are the two components of substTaskMeasure.
-- The actual Acc threading in Phase D will use these plus the
-- encoding arithmetic.

-- The output type of a sub-derivation: used to state tyDepth decrease.
-- For fSigma dA dB where J = isType gamma (tySigma A B):
--   outputType J = tySigma A B, but outputType (isType gamma A) = A.
--   tyDepth A < tyDepth (tySigma A B) by tyDepth-fst<Sigma.

-- For substTyRule d' fits' where J = isType gamma (subTy sigma' A):
--   outputType J = subTy sigma' A, outputType (isType delta A) = A.
--   tyDepth A = tyDepth (subTy sigma' A) by tyDepth-subTy.
--   derivSize d' < derivSize (substTyRule d' fits') trivially.

-- For weakenTy d wf where J = isType (delta ++ gamma) (wkTyBy (length delta) A):
--   outputType J = wkTyBy (length delta) A.
--   tyDepth (wkTyBy (length delta) A) = tyDepth A by tyDepth-wkTy (to be proved).
--   derivSize d < derivSize (weakenTy d wf) trivially.

-- tyDepth is preserved by weakening (renaming)
open import TReg.Substitution using (Ren ; renTy ; raiseRen ; addRen ; wkTyBy)

tyDepth-renTy : (rho : Ren) -> (A : RawType) -> tyDepth (renTy rho A) ≡ tyDepth A
tyDepth-renTy rho tyTop = refl
tyDepth-renTy rho (tySigma A B) =
  cong suc (cong₂ _+_ (tyDepth-renTy rho A) (tyDepth-renTy (raiseRen rho) B))
tyDepth-renTy rho (tyEq A a b) = cong suc (tyDepth-renTy rho A)
tyDepth-renTy rho (tyQtr A) = cong suc (tyDepth-renTy rho A)

tyDepth-wkTy : (k : ℕ) -> (A : RawType) -> tyDepth (wkTyBy k A) ≡ tyDepth A
tyDepth-wkTy k A = tyDepth-renTy (addRen k) A
