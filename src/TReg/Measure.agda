{-# OPTIONS --safe #-}

module TReg.Measure where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_)
open import Cubical.Data.Nat.Properties using (max ; maxSuc)
open import Cubical.Data.Nat.Order using (_<_ ; _≤_ ; ≤-refl ; ≤-suc ; suc-≤-suc ; ≤SumLeft ; ≤SumRight ; <-wellfounded ; maxLUB ; <-k+)
open import Cubical.Induction.WellFounded using (Acc ; acc ; WellFounded)
open import Cubical.Data.List.Base using ([] ; _∷_ ; _++_)

open import TReg.Syntax
open import TReg.Context
open import TReg.Substitution using (Subst ; subTy ; subTm ; liftSubst ; singleSubst)

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

-- The SCC 2 task measure: just derivSize.
-- Every direct sub-derivation has strictly smaller derivSize (by structural
-- induction on the Derivable constructors), so the sum is unnecessary.
-- For cases like `conv` where the output type can change unrelated to the
-- parent, derivSize still strictly decreases on the recursive call, while
-- tyDepth has no useful relationship.
substTaskMeasure : {J : JForm} -> Derivable J -> ℕ
substTaskMeasure d = derivSize d

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

-- KEY LEMMA: If derivSize strictly decreases, substTaskMeasure strictly decreases.
-- Since substTaskMeasure = derivSize, this is direct.
substMeasure-derivSize< : {J₁ J₂ : JForm}
  -> (d₁ : Derivable J₁) -> (d₂ : Derivable J₂)
  -> derivSize d₁ < derivSize d₂
  -> substTaskMeasure d₁ < substTaskMeasure d₂
substMeasure-derivSize< _ _ p = p

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
open import TReg.Substitution using (Ren ; renTy ; renTm ; raiseRen ; addRen ; wkTyBy ; wkTmBy)

tyDepth-renTy : (rho : Ren) -> (A : RawType) -> tyDepth (renTy rho A) ≡ tyDepth A
tyDepth-renTy rho tyTop = refl
tyDepth-renTy rho (tySigma A B) =
  cong suc (cong₂ _+_ (tyDepth-renTy rho A) (tyDepth-renTy (raiseRen rho) B))
tyDepth-renTy rho (tyEq A a b) = cong suc (tyDepth-renTy rho A)
tyDepth-renTy rho (tyQtr A) = cong suc (tyDepth-renTy rho A)

tyDepth-wkTy : (k : ℕ) -> (A : RawType) -> tyDepth (wkTyBy k A) ≡ tyDepth A
tyDepth-wkTy k A = tyDepth-renTy (addRen k) A

-- ═══════════════════════════════════════════════════════════════════
-- Per-constructor convenience lemmas: substTaskMeasure d' < substTaskMeasure d
-- ═══════════════════════════════════════════════════════════════════
-- Each of these packages a specific "sub-derivation" decrease into a
-- single <-proof on substTaskMeasure. They are used as the decrease witnesses
-- inside the Acc sub-witness construction `rs _ <proof>`.

-- Per-constructor convenience lemmas. Each proves the recursive sub-derivation
-- has strictly smaller derivSize than its parent.

substMeasure-fSigma-head< : {gamma : Ctx} {A B : RawType}
  -> (dA : Derivable (isType gamma A)) -> (dB : Derivable (isType (A ∷ gamma) B))
  -> substTaskMeasure dA < substTaskMeasure (fSigma dA dB)
substMeasure-fSigma-head< dA dB =
  suc-≤-suc (≤SumLeft {derivSize dA} {derivSize dB})

-- derivSize (fEq dA da db) = suc ((derivSize dA + derivSize da) + derivSize db)
fEqLeft-size≤ : {gamma : Ctx} {A : RawType} {a b : RawTerm}
  -> (dA : Derivable (isType gamma A)) -> (da : Derivable (hasTy gamma a A)) -> (db : Derivable (hasTy gamma b A))
  -> derivSize dA + derivSize da ≤ derivSize dA + derivSize da + derivSize db
fEqLeft-size≤ dA da db =
  ≤SumLeft {derivSize dA + derivSize da} {derivSize db}

substMeasure-fEq-base< : {gamma : Ctx} {A : RawType} {a b : RawTerm}
  -> (dA : Derivable (isType gamma A)) -> (da : Derivable (hasTy gamma a A)) -> (db : Derivable (hasTy gamma b A))
  -> substTaskMeasure dA < substTaskMeasure (fEq dA da db)
substMeasure-fEq-base< dA da db =
  suc-≤-suc (≤-trans (≤SumLeft {derivSize dA} {derivSize da}) (fEqLeft-size≤ dA da db))

substMeasure-fEq-leftTm< : {gamma : Ctx} {A : RawType} {a b : RawTerm}
  -> (dA : Derivable (isType gamma A)) -> (da : Derivable (hasTy gamma a A)) -> (db : Derivable (hasTy gamma b A))
  -> substTaskMeasure da < substTaskMeasure (fEq dA da db)
substMeasure-fEq-leftTm< dA da db =
  suc-≤-suc (≤-trans (≤SumRight {derivSize da} {derivSize dA}) (fEqLeft-size≤ dA da db))

substMeasure-fEq-rightTm< : {gamma : Ctx} {A : RawType} {a b : RawTerm}
  -> (dA : Derivable (isType gamma A)) -> (da : Derivable (hasTy gamma a A)) -> (db : Derivable (hasTy gamma b A))
  -> substTaskMeasure db < substTaskMeasure (fEq dA da db)
substMeasure-fEq-rightTm< dA da db =
  suc-≤-suc (≤SumRight {derivSize db} {derivSize dA + derivSize da})

substMeasure-fQtr-base< : {gamma : Ctx} {A : RawType}
  -> (dA : Derivable (isType gamma A))
  -> substTaskMeasure dA < substTaskMeasure (fQtr dA)
substMeasure-fQtr-base< dA = ≤-refl

-- Structural same-constructor sub-derivation lemmas for weakenTy/substTyRule/
-- conv/reflTy/symTy/transTy/convEq etc. Each one derivSize-strictly-decreases.
substMeasure-weakenTy< : {gamma delta : Ctx} {A : RawType}
  -> (d : Derivable (isType gamma A)) -> (wf : CtxWF (delta ++ gamma))
  -> substTaskMeasure d < substTaskMeasure (weakenTy d wf)
substMeasure-weakenTy< d wf =
  suc-≤-suc (≤SumLeft {derivSize d} {ctxWFSize wf})

substMeasure-weakenTyEq< : {gamma delta : Ctx} {A B : RawType}
  -> (d : Derivable (typeEq gamma A B)) -> (wf : CtxWF (delta ++ gamma))
  -> substTaskMeasure d < substTaskMeasure (weakenTyEq d wf)
substMeasure-weakenTyEq< d wf =
  suc-≤-suc (≤SumLeft {derivSize d} {ctxWFSize wf})

substMeasure-weakenTm< : {gamma delta : Ctx} {t : RawTerm} {A : RawType}
  -> (d : Derivable (hasTy gamma t A)) -> (wf : CtxWF (delta ++ gamma))
  -> substTaskMeasure d < substTaskMeasure (weakenTm d wf)
substMeasure-weakenTm< d wf =
  suc-≤-suc (≤SumLeft {derivSize d} {ctxWFSize wf})

substMeasure-weakenTmEq< : {gamma delta : Ctx} {t u : RawTerm} {A : RawType}
  -> (d : Derivable (termEq gamma t u A)) -> (wf : CtxWF (delta ++ gamma))
  -> substTaskMeasure d < substTaskMeasure (weakenTmEq d wf)
substMeasure-weakenTmEq< d wf =
  suc-≤-suc (≤SumLeft {derivSize d} {ctxWFSize wf})

substMeasure-substTyRule< : {gamma delta : Ctx} {sigma : Subst} {A : RawType}
  -> (d : Derivable (isType delta A)) -> (fits : FitsSubst gamma delta sigma)
  -> substTaskMeasure d < substTaskMeasure (substTyRule d fits)
substMeasure-substTyRule< d fits =
  suc-≤-suc (≤SumLeft {derivSize d} {fitsSize fits})

substMeasure-substTyEqRule< : {gamma delta : Ctx} {sigma : Subst} {A B : RawType}
  -> (d : Derivable (typeEq delta A B)) -> (fits : FitsSubst gamma delta sigma)
  -> substTaskMeasure d < substTaskMeasure (substTyEqRule d fits)
substMeasure-substTyEqRule< d fits =
  suc-≤-suc (≤SumLeft {derivSize d} {fitsSize fits})

substMeasure-substTmRule< : {gamma delta : Ctx} {sigma : Subst} {t : RawTerm} {A : RawType}
  -> (d : Derivable (hasTy delta t A)) -> (fits : FitsSubst gamma delta sigma)
  -> substTaskMeasure d < substTaskMeasure (substTmRule d fits)
substMeasure-substTmRule< d fits =
  suc-≤-suc (≤SumLeft {derivSize d} {fitsSize fits})

substMeasure-substTmEqRule< : {gamma delta : Ctx} {sigma : Subst} {t u : RawTerm} {A : RawType}
  -> (d : Derivable (termEq delta t u A)) -> (fits : FitsSubst gamma delta sigma)
  -> substTaskMeasure d < substTaskMeasure (substTmEqRule d fits)
substMeasure-substTmEqRule< d fits =
  suc-≤-suc (≤SumLeft {derivSize d} {fitsSize fits})

substMeasure-eqSubTyRule< : {gamma delta : Ctx} {sigma tau : Subst} {A : RawType}
  -> (d : Derivable (isType delta A)) -> (fitsEq : FitsEqSubst gamma delta sigma tau)
  -> substTaskMeasure d < substTaskMeasure (eqSubTyRule d fitsEq)
substMeasure-eqSubTyRule< d fitsEq =
  suc-≤-suc (≤SumLeft {derivSize d} {fitsEqSize fitsEq})

substMeasure-eqSubTyEqRule< : {gamma delta : Ctx} {sigma tau : Subst} {A B : RawType}
  -> (d : Derivable (typeEq delta A B)) -> (fitsEq : FitsEqSubst gamma delta sigma tau)
  -> substTaskMeasure d < substTaskMeasure (eqSubTyEqRule d fitsEq)
substMeasure-eqSubTyEqRule< d fitsEq =
  suc-≤-suc (≤SumLeft {derivSize d} {fitsEqSize fitsEq})

substMeasure-eqSubTmRule< : {gamma delta : Ctx} {sigma tau : Subst} {t : RawTerm} {A : RawType}
  -> (d : Derivable (hasTy delta t A)) -> (fitsEq : FitsEqSubst gamma delta sigma tau)
  -> substTaskMeasure d < substTaskMeasure (eqSubTmRule d fitsEq)
substMeasure-eqSubTmRule< d fitsEq =
  suc-≤-suc (≤SumLeft {derivSize d} {fitsEqSize fitsEq})

substMeasure-eqSubTmEqRule< : {gamma delta : Ctx} {sigma tau : Subst} {t u : RawTerm} {A : RawType}
  -> (d : Derivable (termEq delta t u A)) -> (fitsEq : FitsEqSubst gamma delta sigma tau)
  -> substTaskMeasure d < substTaskMeasure (eqSubTmEqRule d fitsEq)
substMeasure-eqSubTmEqRule< d fitsEq =
  suc-≤-suc (≤SumLeft {derivSize d} {fitsEqSize fitsEq})

substMeasure-conv-tm< : {gamma : Ctx} {t : RawTerm} {A B : RawType}
  -> (d : Derivable (hasTy gamma t A)) -> (dAB : Derivable (typeEq gamma A B))
  -> substTaskMeasure d < substTaskMeasure (conv d dAB)
substMeasure-conv-tm< d dAB =
  suc-≤-suc (≤SumLeft {derivSize d} {derivSize dAB})

substMeasure-conv-tyEq< : {gamma : Ctx} {t : RawTerm} {A B : RawType}
  -> (d : Derivable (hasTy gamma t A)) -> (dAB : Derivable (typeEq gamma A B))
  -> substTaskMeasure dAB < substTaskMeasure (conv d dAB)
substMeasure-conv-tyEq< d dAB =
  suc-≤-suc (≤SumRight {derivSize dAB} {derivSize d})

substMeasure-convEq-tm< : {gamma : Ctx} {t u : RawTerm} {A B : RawType}
  -> (d : Derivable (termEq gamma t u A)) -> (dAB : Derivable (typeEq gamma A B))
  -> substTaskMeasure d < substTaskMeasure (convEq d dAB)
substMeasure-convEq-tm< d dAB =
  suc-≤-suc (≤SumLeft {derivSize d} {derivSize dAB})

substMeasure-convEq-tyEq< : {gamma : Ctx} {t u : RawTerm} {A B : RawType}
  -> (d : Derivable (termEq gamma t u A)) -> (dAB : Derivable (typeEq gamma A B))
  -> substTaskMeasure dAB < substTaskMeasure (convEq d dAB)
substMeasure-convEq-tyEq< d dAB =
  suc-≤-suc (≤SumRight {derivSize dAB} {derivSize d})

substMeasure-reflTy< : {gamma : Ctx} {A : RawType}
  -> (d : Derivable (isType gamma A))
  -> substTaskMeasure d < substTaskMeasure (reflTy d)
substMeasure-reflTy< d = ≤-refl

substMeasure-reflTm< : {gamma : Ctx} {t : RawTerm} {A : RawType}
  -> (d : Derivable (hasTy gamma t A))
  -> substTaskMeasure d < substTaskMeasure (reflTm d)
substMeasure-reflTm< d = ≤-refl

substMeasure-symTy-left< : {gamma : Ctx} {A B : RawType}
  -> (d : Derivable (typeEq gamma A B)) -> (dB : Derivable (isType gamma B))
  -> substTaskMeasure d < substTaskMeasure (symTy d dB)
substMeasure-symTy-left< d dB =
  suc-≤-suc (≤SumLeft {derivSize d} {derivSize dB})

substMeasure-symTy-right< : {gamma : Ctx} {A B : RawType}
  -> (d : Derivable (typeEq gamma A B)) -> (dB : Derivable (isType gamma B))
  -> substTaskMeasure dB < substTaskMeasure (symTy d dB)
substMeasure-symTy-right< d dB =
  suc-≤-suc (≤SumRight {derivSize dB} {derivSize d})

substMeasure-symTm-eq< : {gamma : Ctx} {t u : RawTerm} {A : RawType}
  -> (d : Derivable (termEq gamma t u A)) -> (du : Derivable (hasTy gamma u A)) -> (dA : Derivable (isType gamma A))
  -> substTaskMeasure d < substTaskMeasure (symTm d du dA)
substMeasure-symTm-eq< d du dA =
  suc-≤-suc (≤-trans (≤SumLeft {derivSize d} {derivSize du}) (≤SumLeft {derivSize d + derivSize du} {derivSize dA}))

substMeasure-symTm-right< : {gamma : Ctx} {t u : RawTerm} {A : RawType}
  -> (d : Derivable (termEq gamma t u A)) -> (du : Derivable (hasTy gamma u A)) -> (dA : Derivable (isType gamma A))
  -> substTaskMeasure du < substTaskMeasure (symTm d du dA)
substMeasure-symTm-right< d du dA =
  suc-≤-suc (≤-trans (≤SumRight {derivSize du} {derivSize d}) (≤SumLeft {derivSize d + derivSize du} {derivSize dA}))

substMeasure-symTm-ty< : {gamma : Ctx} {t u : RawTerm} {A : RawType}
  -> (d : Derivable (termEq gamma t u A)) -> (du : Derivable (hasTy gamma u A)) -> (dA : Derivable (isType gamma A))
  -> substTaskMeasure dA < substTaskMeasure (symTm d du dA)
substMeasure-symTm-ty< d du dA =
  suc-≤-suc (≤SumRight {derivSize dA} {derivSize d + derivSize du})

substMeasure-transTy-left< : {gamma : Ctx} {A B C : RawType}
  -> (d₁ : Derivable (typeEq gamma A B)) -> (d₂ : Derivable (typeEq gamma B C))
  -> substTaskMeasure d₁ < substTaskMeasure (transTy d₁ d₂)
substMeasure-transTy-left< d₁ d₂ =
  suc-≤-suc (≤SumLeft {derivSize d₁} {derivSize d₂})

substMeasure-transTy-right< : {gamma : Ctx} {A B C : RawType}
  -> (d₁ : Derivable (typeEq gamma A B)) -> (d₂ : Derivable (typeEq gamma B C))
  -> substTaskMeasure d₂ < substTaskMeasure (transTy d₁ d₂)
substMeasure-transTy-right< d₁ d₂ =
  suc-≤-suc (≤SumRight {derivSize d₂} {derivSize d₁})

substMeasure-transTm-left< : {gamma : Ctx} {t u v : RawTerm} {A : RawType}
  -> (d₁ : Derivable (termEq gamma t u A)) -> (d₂ : Derivable (termEq gamma u v A))
  -> substTaskMeasure d₁ < substTaskMeasure (transTm d₁ d₂)
substMeasure-transTm-left< d₁ d₂ =
  suc-≤-suc (≤SumLeft {derivSize d₁} {derivSize d₂})

substMeasure-transTm-right< : {gamma : Ctx} {t u v : RawTerm} {A : RawType}
  -> (d₁ : Derivable (termEq gamma t u A)) -> (d₂ : Derivable (termEq gamma u v A))
  -> substTaskMeasure d₂ < substTaskMeasure (transTm d₁ d₂)
substMeasure-transTm-right< d₁ d₂ =
  suc-≤-suc (≤SumRight {derivSize d₂} {derivSize d₁})

-- convEq premises:
substMeasure-convEq-tmEq< : {gamma : Ctx} {t u : RawTerm} {A B : RawType}
  -> (d : Derivable (termEq gamma t u A)) -> (dAB : Derivable (typeEq gamma A B))
  -> substTaskMeasure d < substTaskMeasure (convEq d dAB)
substMeasure-convEq-tmEq< d dAB =
  suc-≤-suc (≤SumLeft {derivSize d} {derivSize dAB})

substMeasure-convEq-tyEq2< : {gamma : Ctx} {t u : RawTerm} {A B : RawType}
  -> (d : Derivable (termEq gamma t u A)) -> (dAB : Derivable (typeEq gamma A B))
  -> substTaskMeasure dAB < substTaskMeasure (convEq d dAB)
substMeasure-convEq-tyEq2< d dAB =
  suc-≤-suc (≤SumRight {derivSize dAB} {derivSize d})

-- Introduction rule premises (all sub-derivations strictly smaller):
-- derivSize (iSigma da db dSigma) = suc (derivSize da + derivSize db + derivSize dSigma)
-- Left-associated: (a + b) + c

iSigmaLeft-size≤ : {gamma : Ctx} {A B : RawType} {a b : RawTerm}
  -> (da : Derivable (hasTy gamma a A)) -> (db : Derivable (hasTy gamma b (subTy (singleSubst a) B)))
  -> (dSigma : Derivable (isType gamma (tySigma A B)))
  -> derivSize da + derivSize db ≤ derivSize da + derivSize db + derivSize dSigma
iSigmaLeft-size≤ da db dSigma = ≤SumLeft {derivSize da + derivSize db} {derivSize dSigma}

substMeasure-iSigma-a< : {gamma : Ctx} {A B : RawType} {a b : RawTerm}
  -> (da : Derivable (hasTy gamma a A)) -> (db : Derivable (hasTy gamma b (subTy (singleSubst a) B)))
  -> (dSigma : Derivable (isType gamma (tySigma A B)))
  -> substTaskMeasure da < substTaskMeasure (iSigma da db dSigma)
substMeasure-iSigma-a< da db dSigma =
  suc-≤-suc (≤-trans (≤SumLeft {derivSize da} {derivSize db}) (iSigmaLeft-size≤ da db dSigma))

substMeasure-iSigma-b< : {gamma : Ctx} {A B : RawType} {a b : RawTerm}
  -> (da : Derivable (hasTy gamma a A)) -> (db : Derivable (hasTy gamma b (subTy (singleSubst a) B)))
  -> (dSigma : Derivable (isType gamma (tySigma A B)))
  -> substTaskMeasure db < substTaskMeasure (iSigma da db dSigma)
substMeasure-iSigma-b< da db dSigma =
  suc-≤-suc (≤-trans (≤SumRight {derivSize db} {derivSize da}) (iSigmaLeft-size≤ da db dSigma))

substMeasure-iSigma-Sigma< : {gamma : Ctx} {A B : RawType} {a b : RawTerm}
  -> (da : Derivable (hasTy gamma a A)) -> (db : Derivable (hasTy gamma b (subTy (singleSubst a) B)))
  -> (dSigma : Derivable (isType gamma (tySigma A B)))
  -> substTaskMeasure dSigma < substTaskMeasure (iSigma da db dSigma)
substMeasure-iSigma-Sigma< da db dSigma =
  suc-≤-suc (≤SumRight {derivSize dSigma} {derivSize da + derivSize db})

substMeasure-iEq< : {gamma : Ctx} {A : RawType} {a : RawTerm}
  -> (da : Derivable (hasTy gamma a A))
  -> substTaskMeasure da < substTaskMeasure (iEq da)
substMeasure-iEq< da = ≤-refl

substMeasure-iQtr< : {gamma : Ctx} {A : RawType} {a : RawTerm}
  -> (da : Derivable (hasTy gamma a A))
  -> substTaskMeasure da < substTaskMeasure (iQtr da)
substMeasure-iQtr< da = ≤-refl

substMeasure-cTop< : {gamma : Ctx} {a : RawTerm}
  -> (d : Derivable (hasTy gamma a tyTop))
  -> substTaskMeasure d < substTaskMeasure (cTop d)
substMeasure-cTop< d = ≤-refl

-- eSigma dM dd dm : derivSize = suc ((derivSize dM + derivSize dd) + derivSize dm)
eSigmaLeft-size≤ : {gamma : Ctx} {A B M : RawType} {d m : RawTerm}
  -> (dM : Derivable (isType (tySigma A B ∷ gamma) M))
  -> (dd : Derivable (hasTy gamma d (tySigma A B)))
  -> (dm : Derivable (hasTy (B ∷ A ∷ gamma) m (sigmaBranchTy M)))
  -> derivSize dM + derivSize dd ≤ derivSize dM + derivSize dd + derivSize dm
eSigmaLeft-size≤ dM dd dm = ≤SumLeft {derivSize dM + derivSize dd} {derivSize dm}

substMeasure-eSigma-dM< : {gamma : Ctx} {A B M : RawType} {d m : RawTerm}
  -> (dM : Derivable (isType (tySigma A B ∷ gamma) M))
  -> (dd : Derivable (hasTy gamma d (tySigma A B)))
  -> (dm : Derivable (hasTy (B ∷ A ∷ gamma) m (sigmaBranchTy M)))
  -> substTaskMeasure dM < substTaskMeasure (eSigma dM dd dm)
substMeasure-eSigma-dM< dM dd dm =
  suc-≤-suc (≤-trans (≤SumLeft {derivSize dM} {derivSize dd}) (eSigmaLeft-size≤ dM dd dm))

substMeasure-eSigma-dd< : {gamma : Ctx} {A B M : RawType} {d m : RawTerm}
  -> (dM : Derivable (isType (tySigma A B ∷ gamma) M))
  -> (dd : Derivable (hasTy gamma d (tySigma A B)))
  -> (dm : Derivable (hasTy (B ∷ A ∷ gamma) m (sigmaBranchTy M)))
  -> substTaskMeasure dd < substTaskMeasure (eSigma dM dd dm)
substMeasure-eSigma-dd< dM dd dm =
  suc-≤-suc (≤-trans (≤SumRight {derivSize dd} {derivSize dM}) (eSigmaLeft-size≤ dM dd dm))

substMeasure-eSigma-dm< : {gamma : Ctx} {A B M : RawType} {d m : RawTerm}
  -> (dM : Derivable (isType (tySigma A B ∷ gamma) M))
  -> (dd : Derivable (hasTy gamma d (tySigma A B)))
  -> (dm : Derivable (hasTy (B ∷ A ∷ gamma) m (sigmaBranchTy M)))
  -> substTaskMeasure dm < substTaskMeasure (eSigma dM dd dm)
substMeasure-eSigma-dm< dM dd dm =
  suc-≤-suc (≤SumRight {derivSize dm} {derivSize dM + derivSize dd})

substMeasure-fSigmaEq-left< : {gamma : Ctx} {A B C D : RawType}
  -> (dAC : Derivable (typeEq gamma A C))
  -> (dB : Derivable (isType (A ∷ gamma) B))
  -> (dBD : Derivable (typeEq (A ∷ gamma) B D))
  -> substTaskMeasure dAC < substTaskMeasure (fSigmaEq dAC dB dBD)
substMeasure-fSigmaEq-left< dAC dB dBD =
  suc-≤-suc (≤-trans (≤SumLeft {derivSize dAC} {derivSize dB}) (≤SumLeft {derivSize dAC + derivSize dB} {derivSize dBD}))

substMeasure-fSigmaEq-middle< : {gamma : Ctx} {A B C D : RawType}
  -> (dAC : Derivable (typeEq gamma A C))
  -> (dB : Derivable (isType (A ∷ gamma) B))
  -> (dBD : Derivable (typeEq (A ∷ gamma) B D))
  -> substTaskMeasure dB < substTaskMeasure (fSigmaEq dAC dB dBD)
substMeasure-fSigmaEq-middle< dAC dB dBD =
  suc-≤-suc (≤-trans (≤SumRight {derivSize dB} {derivSize dAC}) (≤SumLeft {derivSize dAC + derivSize dB} {derivSize dBD}))

substMeasure-fSigmaEq-right< : {gamma : Ctx} {A B C D : RawType}
  -> (dAC : Derivable (typeEq gamma A C))
  -> (dB : Derivable (isType (A ∷ gamma) B))
  -> (dBD : Derivable (typeEq (A ∷ gamma) B D))
  -> substTaskMeasure dBD < substTaskMeasure (fSigmaEq dAC dB dBD)
substMeasure-fSigmaEq-right< dAC dB dBD =
  suc-≤-suc (≤SumRight {derivSize dBD} {derivSize dAC + derivSize dB})

substMeasure-fEqEq-left< : {gamma : Ctx} {A C : RawType} {a b c d : RawTerm}
  -> (dAC : Derivable (typeEq gamma A C))
  -> (dac : Derivable (termEq gamma a c A))
  -> (dbd : Derivable (termEq gamma b d A))
  -> substTaskMeasure dAC < substTaskMeasure (fEqEq dAC dac dbd)
substMeasure-fEqEq-left< dAC dac dbd =
  suc-≤-suc (≤-trans (≤SumLeft {derivSize dAC} {derivSize dac}) (≤SumLeft {derivSize dAC + derivSize dac} {derivSize dbd}))

substMeasure-fEqEq-middleTm< : {gamma : Ctx} {A C : RawType} {a b c d : RawTerm}
  -> (dAC : Derivable (typeEq gamma A C))
  -> (dac : Derivable (termEq gamma a c A))
  -> (dbd : Derivable (termEq gamma b d A))
  -> substTaskMeasure dac < substTaskMeasure (fEqEq dAC dac dbd)
substMeasure-fEqEq-middleTm< dAC dac dbd =
  suc-≤-suc (≤-trans (≤SumRight {derivSize dac} {derivSize dAC}) (≤SumLeft {derivSize dAC + derivSize dac} {derivSize dbd}))

substMeasure-fEqEq-rightTm< : {gamma : Ctx} {A C : RawType} {a b c d : RawTerm}
  -> (dAC : Derivable (typeEq gamma A C))
  -> (dac : Derivable (termEq gamma a c A))
  -> (dbd : Derivable (termEq gamma b d A))
  -> substTaskMeasure dbd < substTaskMeasure (fEqEq dAC dac dbd)
substMeasure-fEqEq-rightTm< dAC dac dbd =
  suc-≤-suc (≤SumRight {derivSize dbd} {derivSize dAC + derivSize dac})

substMeasure-fQtrEq-base< : {gamma : Ctx} {A B : RawType}
  -> (dAB : Derivable (typeEq gamma A B))
  -> substTaskMeasure dAB < substTaskMeasure (fQtrEq dAB)
substMeasure-fQtrEq-base< dAB = ≤-refl

substMeasure-iSigmaEq-ac< : {gamma : Ctx} {a b c d : RawTerm} {A B : RawType}
  -> (dac : Derivable (termEq gamma a c A))
  -> (dbd : Derivable (termEq gamma b d (subTy (singleSubst a) B)))
  -> (dA : Derivable (isType gamma A))
  -> (dB : Derivable (isType (A ∷ gamma) B))
  -> substTaskMeasure dac < substTaskMeasure (iSigmaEq dac dbd dA dB)
substMeasure-iSigmaEq-ac< dac dbd dA dB =
  suc-≤-suc
    (≤-trans
      (≤-trans
        (≤SumLeft {derivSize dac} {derivSize dbd})
        (≤SumLeft {derivSize dac + derivSize dbd} {derivSize dA}))
      (≤SumLeft {derivSize dac + derivSize dbd + derivSize dA} {derivSize dB}))

substMeasure-iSigmaEq-bd< : {gamma : Ctx} {a b c d : RawTerm} {A B : RawType}
  -> (dac : Derivable (termEq gamma a c A))
  -> (dbd : Derivable (termEq gamma b d (subTy (singleSubst a) B)))
  -> (dA : Derivable (isType gamma A))
  -> (dB : Derivable (isType (A ∷ gamma) B))
  -> substTaskMeasure dbd < substTaskMeasure (iSigmaEq dac dbd dA dB)
substMeasure-iSigmaEq-bd< dac dbd dA dB =
  suc-≤-suc
    (≤-trans
      (≤-trans
        (≤SumRight {derivSize dbd} {derivSize dac})
        (≤SumLeft {derivSize dac + derivSize dbd} {derivSize dA}))
      (≤SumLeft {derivSize dac + derivSize dbd + derivSize dA} {derivSize dB}))

substMeasure-iSigmaEq-A< : {gamma : Ctx} {a b c d : RawTerm} {A B : RawType}
  -> (dac : Derivable (termEq gamma a c A))
  -> (dbd : Derivable (termEq gamma b d (subTy (singleSubst a) B)))
  -> (dA : Derivable (isType gamma A))
  -> (dB : Derivable (isType (A ∷ gamma) B))
  -> substTaskMeasure dA < substTaskMeasure (iSigmaEq dac dbd dA dB)
substMeasure-iSigmaEq-A< dac dbd dA dB =
  suc-≤-suc
    (≤-trans
      (≤SumRight {derivSize dA} {derivSize dac + derivSize dbd})
      (≤SumLeft {derivSize dac + derivSize dbd + derivSize dA} {derivSize dB}))

substMeasure-iSigmaEq-B< : {gamma : Ctx} {a b c d : RawTerm} {A B : RawType}
  -> (dac : Derivable (termEq gamma a c A))
  -> (dbd : Derivable (termEq gamma b d (subTy (singleSubst a) B)))
  -> (dA : Derivable (isType gamma A))
  -> (dB : Derivable (isType (A ∷ gamma) B))
  -> substTaskMeasure dB < substTaskMeasure (iSigmaEq dac dbd dA dB)
substMeasure-iSigmaEq-B< dac dbd dA dB =
  suc-≤-suc (≤SumRight {derivSize dB} {derivSize dac + derivSize dbd + derivSize dA})

substMeasure-iEqEq< : {gamma : Ctx} {A : RawType} {a b : RawTerm}
  -> (dab : Derivable (termEq gamma a b A))
  -> substTaskMeasure dab < substTaskMeasure (iEqEq dab)
substMeasure-iEqEq< dab = ≤-refl

substMeasure-iQtrEq-left< : {gamma : Ctx} {A : RawType} {a b : RawTerm}
  -> (da : Derivable (hasTy gamma a A))
  -> (db : Derivable (hasTy gamma b A))
  -> substTaskMeasure da < substTaskMeasure (iQtrEq da db)
substMeasure-iQtrEq-left< da db =
  suc-≤-suc (≤SumLeft {derivSize da} {derivSize db})

substMeasure-iQtrEq-right< : {gamma : Ctx} {A : RawType} {a b : RawTerm}
  -> (da : Derivable (hasTy gamma a A))
  -> (db : Derivable (hasTy gamma b A))
  -> substTaskMeasure db < substTaskMeasure (iQtrEq da db)
substMeasure-iQtrEq-right< da db =
  suc-≤-suc (≤SumRight {derivSize db} {derivSize da})

substMeasure-eSigmaEq-dd< : {gamma : Ctx} {A B M : RawType} {d d' m m' : RawTerm}
  -> (dM : Derivable (isType ((tySigma A B) ∷ gamma) M))
  -> (dd : Derivable (termEq gamma d d' (tySigma A B)))
  -> (dm : Derivable (hasTy (B ∷ A ∷ gamma) m (sigmaBranchTy M)))
  -> (dm' : Derivable (termEq (B ∷ A ∷ gamma) m m' (sigmaBranchTy M)))
  -> substTaskMeasure dd < substTaskMeasure (eSigmaEq dM dd dm dm')
substMeasure-eSigmaEq-dd< dM dd dm dm' =
  suc-≤-suc
    (≤-trans
      (≤-trans
        (≤SumRight {derivSize dd} {derivSize dM})
        (≤SumLeft {derivSize dM + derivSize dd} {derivSize dm}))
      (≤SumLeft {derivSize dM + derivSize dd + derivSize dm} {derivSize dm'}))

substMeasure-cSigma-Sigma< : {gamma : Ctx} {A B M : RawType} {b c m : RawTerm}
  -> (dM : Derivable (isType ((tySigma A B) ∷ gamma) M))
  -> (dSigma : Derivable (isType gamma (tySigma A B)))
  -> (db : Derivable (hasTy gamma b A))
  -> (dc : Derivable (hasTy gamma c (subTy (singleSubst b) B)))
  -> (dm : Derivable (hasTy (B ∷ A ∷ gamma) m (sigmaBranchTy M)))
  -> substTaskMeasure dSigma < substTaskMeasure (cSigma dM dSigma db dc dm)
substMeasure-cSigma-Sigma< dM dSigma db dc dm =
  suc-≤-suc
    (≤-trans
      (≤-trans
        (≤-trans
          (≤SumRight {derivSize dSigma} {derivSize dM})
          (≤SumLeft {derivSize dM + derivSize dSigma} {derivSize db}))
        (≤SumLeft {derivSize dM + derivSize dSigma + derivSize db} {derivSize dc}))
      (≤SumLeft {derivSize dM + derivSize dSigma + derivSize db + derivSize dc} {derivSize dm}))

substMeasure-cSigma-b< : {gamma : Ctx} {A B M : RawType} {b c m : RawTerm}
  -> (dM : Derivable (isType ((tySigma A B) ∷ gamma) M))
  -> (dSigma : Derivable (isType gamma (tySigma A B)))
  -> (db : Derivable (hasTy gamma b A))
  -> (dc : Derivable (hasTy gamma c (subTy (singleSubst b) B)))
  -> (dm : Derivable (hasTy (B ∷ A ∷ gamma) m (sigmaBranchTy M)))
  -> substTaskMeasure db < substTaskMeasure (cSigma dM dSigma db dc dm)
substMeasure-cSigma-b< dM dSigma db dc dm =
  suc-≤-suc
    (≤-trans
      (≤-trans
        (≤SumRight {derivSize db} {derivSize dM + derivSize dSigma})
        (≤SumLeft {derivSize dM + derivSize dSigma + derivSize db} {derivSize dc}))
      (≤SumLeft {derivSize dM + derivSize dSigma + derivSize db + derivSize dc} {derivSize dm}))

substMeasure-cSigma-c< : {gamma : Ctx} {A B M : RawType} {b c m : RawTerm}
  -> (dM : Derivable (isType ((tySigma A B) ∷ gamma) M))
  -> (dSigma : Derivable (isType gamma (tySigma A B)))
  -> (db : Derivable (hasTy gamma b A))
  -> (dc : Derivable (hasTy gamma c (subTy (singleSubst b) B)))
  -> (dm : Derivable (hasTy (B ∷ A ∷ gamma) m (sigmaBranchTy M)))
  -> substTaskMeasure dc < substTaskMeasure (cSigma dM dSigma db dc dm)
substMeasure-cSigma-c< dM dSigma db dc dm =
  suc-≤-suc
    (≤-trans
      (≤SumRight {derivSize dc} {derivSize dM + derivSize dSigma + derivSize db})
      (≤SumLeft {derivSize dM + derivSize dSigma + derivSize db + derivSize dc} {derivSize dm}))

substMeasure-cSigma-m< : {gamma : Ctx} {A B M : RawType} {b c m : RawTerm}
  -> (dM : Derivable (isType ((tySigma A B) ∷ gamma) M))
  -> (dSigma : Derivable (isType gamma (tySigma A B)))
  -> (db : Derivable (hasTy gamma b A))
  -> (dc : Derivable (hasTy gamma c (subTy (singleSubst b) B)))
  -> (dm : Derivable (hasTy (B ∷ A ∷ gamma) m (sigmaBranchTy M)))
  -> substTaskMeasure dm < substTaskMeasure (cSigma dM dSigma db dc dm)
substMeasure-cSigma-m< dM dSigma db dc dm =
  suc-≤-suc (≤SumRight {derivSize dm} {derivSize dM + derivSize dSigma + derivSize db + derivSize dc})

substMeasure-cSigma-M< : {gamma : Ctx} {A B M : RawType} {b c m : RawTerm}
  -> (dM : Derivable (isType ((tySigma A B) ∷ gamma) M))
  -> (dSigma : Derivable (isType gamma (tySigma A B)))
  -> (db : Derivable (hasTy gamma b A))
  -> (dc : Derivable (hasTy gamma c (subTy (singleSubst b) B)))
  -> (dm : Derivable (hasTy (B ∷ A ∷ gamma) m (sigmaBranchTy M)))
  -> substTaskMeasure dM < substTaskMeasure (cSigma dM dSigma db dc dm)
substMeasure-cSigma-M< dM dSigma db dc dm =
  suc-≤-suc
    (≤-trans
      (≤-trans
        (≤-trans
          (≤SumLeft {derivSize dM} {derivSize dSigma})
          (≤SumLeft {derivSize dM + derivSize dSigma} {derivSize db}))
        (≤SumLeft {derivSize dM + derivSize dSigma + derivSize db} {derivSize dc}))
      (≤SumLeft {derivSize dM + derivSize dSigma + derivSize db + derivSize dc} {derivSize dm}))

substMeasure-eEqStar-p< : {gamma : Ctx} {A : RawType} {a b p : RawTerm}
  -> (dp : Derivable (hasTy gamma p (tyEq A a b)))
  -> (dA : Derivable (isType gamma A))
  -> (da : Derivable (hasTy gamma a A))
  -> (db : Derivable (hasTy gamma b A))
  -> substTaskMeasure dp < substTaskMeasure (eEqStar dp dA da db)
substMeasure-eEqStar-p< dp dA da db =
  suc-≤-suc
    (≤-trans
      (≤-trans
        (≤SumLeft {derivSize dp} {derivSize dA})
        (≤SumLeft {derivSize dp + derivSize dA} {derivSize da}))
      (≤SumLeft {derivSize dp + derivSize dA + derivSize da} {derivSize db}))

substMeasure-cEq-p< : {gamma : Ctx} {A : RawType} {a b p : RawTerm}
  -> (dp : Derivable (hasTy gamma p (tyEq A a b)))
  -> (dA : Derivable (isType gamma A))
  -> (da : Derivable (hasTy gamma a A))
  -> (db : Derivable (hasTy gamma b A))
  -> substTaskMeasure dp < substTaskMeasure (cEq dp dA da db)
substMeasure-cEq-p< dp dA da db =
  suc-≤-suc
    (≤-trans
      (≤-trans
        (≤SumLeft {derivSize dp} {derivSize dA})
        (≤SumLeft {derivSize dp + derivSize dA} {derivSize da}))
      (≤SumLeft {derivSize dp + derivSize dA + derivSize da} {derivSize db}))

substMeasure-eEqStar-b< : {gamma : Ctx} {A : RawType} {a b p : RawTerm}
  -> (dp : Derivable (hasTy gamma p (tyEq A a b)))
  -> (dA : Derivable (isType gamma A))
  -> (da : Derivable (hasTy gamma a A))
  -> (db : Derivable (hasTy gamma b A))
  -> substTaskMeasure db < substTaskMeasure (eEqStar dp dA da db)
substMeasure-eEqStar-b< dp dA da db =
  suc-≤-suc (≤SumRight {derivSize db} {derivSize dp + derivSize dA + derivSize da})

substMeasure-eQtr-p< : {gamma : Ctx} {A L : RawType} {l p : RawTerm}
  -> (dL : Derivable (isType (tyQtr A ∷ gamma) L))
  -> (dp : Derivable (hasTy gamma p (tyQtr A)))
  -> (dBranchTy : Derivable (isType (A ∷ gamma) (qtrBranchTy L)))
  -> (dl : Derivable (hasTy (A ∷ gamma) l (qtrBranchTy L)))
  -> (dcoh : Derivable (termEq (wkTyBy 1 A ∷ A ∷ gamma) (wkTmBy 1 l) (renTm qtrSecondBranchRen l) (qtrCohTy L)))
  -> substTaskMeasure dp < substTaskMeasure (eQtr dL dp dBranchTy dl dcoh)
substMeasure-eQtr-p< dL dp dBranchTy dl dcoh =
  suc-≤-suc
    (≤-trans
      (≤-trans
        (≤-trans
          (≤SumRight {derivSize dp} {derivSize dL})
          (≤SumLeft {derivSize dL + derivSize dp} {derivSize dBranchTy}))
        (≤SumLeft {derivSize dL + derivSize dp + derivSize dBranchTy} {derivSize dl}))
      (≤SumLeft {derivSize dL + derivSize dp + derivSize dBranchTy + derivSize dl} {derivSize dcoh}))

substMeasure-eQtrEq-p< : {gamma : Ctx} {A L : RawType} {l l' p p' : RawTerm}
  -> (dL : Derivable (isType (tyQtr A ∷ gamma) L))
  -> (dp : Derivable (termEq gamma p p' (tyQtr A)))
  -> (dBranchTy : Derivable (isType (A ∷ gamma) (qtrBranchTy L)))
  -> (dl : Derivable (hasTy (A ∷ gamma) l (qtrBranchTy L)))
  -> (dl' : Derivable (hasTy (A ∷ gamma) l' (qtrBranchTy L)))
  -> (dll' : Derivable (termEq (A ∷ gamma) l l' (qtrBranchTy L)))
  -> (dcoh : Derivable (termEq (wkTyBy 1 A ∷ A ∷ gamma) (wkTmBy 1 l) (renTm qtrSecondBranchRen l) (qtrCohTy L)))
  -> (dcoh' : Derivable (termEq (wkTyBy 1 A ∷ A ∷ gamma) (wkTmBy 1 l') (renTm qtrSecondBranchRen l') (qtrCohTy L)))
  -> substTaskMeasure dp < substTaskMeasure (eQtrEq dL dp dBranchTy dl dl' dll' dcoh dcoh')
substMeasure-eQtrEq-p< dL dp dBranchTy dl dl' dll' dcoh dcoh' =
  suc-≤-suc
    (≤-trans
      (≤-trans
        (≤-trans
          (≤-trans
            (≤-trans
              (≤-trans
                (≤SumRight {derivSize dp} {derivSize dL})
                (≤SumLeft {derivSize dL + derivSize dp} {derivSize dBranchTy}))
              (≤SumLeft {derivSize dL + derivSize dp + derivSize dBranchTy} {derivSize dl}))
            (≤SumLeft {derivSize dL + derivSize dp + derivSize dBranchTy + derivSize dl} {derivSize dl'}))
          (≤SumLeft {derivSize dL + derivSize dp + derivSize dBranchTy + derivSize dl + derivSize dl'} {derivSize dll'}))
        (≤SumLeft {derivSize dL + derivSize dp + derivSize dBranchTy + derivSize dl + derivSize dl' + derivSize dll'} {derivSize dcoh}))
      (≤SumLeft {derivSize dL + derivSize dp + derivSize dBranchTy + derivSize dl + derivSize dl' + derivSize dll' + derivSize dcoh} {derivSize dcoh'}))

substMeasure-cQtr-a< : {gamma : Ctx} {A L : RawType} {a l : RawTerm}
  -> (dL : Derivable (isType (tyQtr A ∷ gamma) L))
  -> (da : Derivable (hasTy gamma a A))
  -> (dBranchTy : Derivable (isType (A ∷ gamma) (qtrBranchTy L)))
  -> (dl : Derivable (hasTy (A ∷ gamma) l (qtrBranchTy L)))
  -> (dcoh : Derivable (termEq (wkTyBy 1 A ∷ A ∷ gamma) (wkTmBy 1 l) (renTm qtrSecondBranchRen l) (qtrCohTy L)))
  -> substTaskMeasure da < substTaskMeasure (cQtr dL da dBranchTy dl dcoh)
substMeasure-cQtr-a< dL da dBranchTy dl dcoh =
  suc-≤-suc
    (≤-trans
      (≤-trans
        (≤-trans
          (≤SumRight {derivSize da} {derivSize dL})
          (≤SumLeft {derivSize dL + derivSize da} {derivSize dBranchTy}))
        (≤SumLeft {derivSize dL + derivSize da + derivSize dBranchTy} {derivSize dl}))
      (≤SumLeft {derivSize dL + derivSize da + derivSize dBranchTy + derivSize dl} {derivSize dcoh}))

substMeasure-cQtr-l< : {gamma : Ctx} {A L : RawType} {a l : RawTerm}
  -> (dL : Derivable (isType (tyQtr A ∷ gamma) L))
  -> (da : Derivable (hasTy gamma a A))
  -> (dBranchTy : Derivable (isType (A ∷ gamma) (qtrBranchTy L)))
  -> (dl : Derivable (hasTy (A ∷ gamma) l (qtrBranchTy L)))
  -> (dcoh : Derivable (termEq (wkTyBy 1 A ∷ A ∷ gamma) (wkTmBy 1 l) (renTm qtrSecondBranchRen l) (qtrCohTy L)))
  -> substTaskMeasure dl < substTaskMeasure (cQtr dL da dBranchTy dl dcoh)
substMeasure-cQtr-l< dL da dBranchTy dl dcoh =
  suc-≤-suc
    (≤-trans
      (≤SumRight {derivSize dl} {derivSize dL + derivSize da + derivSize dBranchTy})
      (≤SumLeft {derivSize dL + derivSize da + derivSize dBranchTy + derivSize dl} {derivSize dcoh}))

substMeasure-cQtr-L< : {gamma : Ctx} {A L : RawType} {a l : RawTerm}
  -> (dL : Derivable (isType (tyQtr A ∷ gamma) L))
  -> (da : Derivable (hasTy gamma a A))
  -> (dBranchTy : Derivable (isType (A ∷ gamma) (qtrBranchTy L)))
  -> (dl : Derivable (hasTy (A ∷ gamma) l (qtrBranchTy L)))
  -> (dcoh : Derivable (termEq (wkTyBy 1 A ∷ A ∷ gamma) (wkTmBy 1 l) (renTm qtrSecondBranchRen l) (qtrCohTy L)))
  -> substTaskMeasure dL < substTaskMeasure (cQtr dL da dBranchTy dl dcoh)
substMeasure-cQtr-L< dL da dBranchTy dl dcoh =
  suc-≤-suc
    (≤-trans
      (≤-trans
        (≤-trans
          (≤SumLeft {derivSize dL} {derivSize da})
          (≤SumLeft {derivSize dL + derivSize da} {derivSize dBranchTy}))
        (≤SumLeft {derivSize dL + derivSize da + derivSize dBranchTy} {derivSize dl}))
      (≤SumLeft {derivSize dL + derivSize da + derivSize dBranchTy + derivSize dl} {derivSize dcoh}))
