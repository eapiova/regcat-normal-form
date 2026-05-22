{-# OPTIONS --safe #-}

module Tait.Fundamental where

open import Tait.Prelude
open import Data.List.Base using ([] ; _∷_ ; _++_ ; length)
open import Data.Nat using (ℕ ; zero ; suc ; _+_ ; _<_ ; _≤_)
open import Data.Nat.Induction using () renaming (<-wellFounded to <-wf)
import Data.Nat.Properties as NatProps
open import Data.Nat.Properties using (≤-refl ; ≤-trans ; <⇒≤ ; +-mono-≤ ; +-mono-<-≤)
open import Data.Product using (Σ-syntax ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit using (tt)
open import Induction.WellFounded using (Acc ; acc)

open import Tait.Syntax
open import Tait.Context
open import Tait.Substitution
open import Tait.Evaluation
open import Tait.Derivability
open import Tait.Measure
open import Tait.Computable
open import Tait.CompLemmas
open import Tait.Env
open import Tait.Presupposition
open import Tait.FundMeasure

≤-sum-1-of-3 : {a b c : ℕ} -> a ≤ a + b + c
≤-sum-1-of-3 {a = a} {b = b} {c = c} =
  ≤-sum-extend-r {k = c} (≤-sum-l {m = a} {n = b})

≤-sum-2-of-3 : {a b c : ℕ} -> b ≤ a + b + c
≤-sum-2-of-3 {a = a} {b = b} {c = c} =
  ≤-sum-extend-r {k = c} (≤-sum-r {m = b} {n = a})

≤-sum-3-of-3 : {a b c : ℕ} -> c ≤ a + b + c
≤-sum-3-of-3 {a = a} {b = b} {c = c} =
  ≤-sum-r {m = c} {n = a + b}

≤-sum-1-of-4 : {a b c d : ℕ} -> a ≤ a + b + c + d
≤-sum-1-of-4 {a = a} {b = b} {c = c} {d = d} =
  ≤-sum-extend-r {k = d} (≤-sum-1-of-3 {a = a} {b = b} {c = c})

≤-sum-2-of-4 : {a b c d : ℕ} -> b ≤ a + b + c + d
≤-sum-2-of-4 {a = a} {b = b} {c = c} {d = d} =
  ≤-sum-extend-r {k = d} (≤-sum-2-of-3 {a = a} {b = b} {c = c})

≤-sum-3-of-4 : {a b c d : ℕ} -> c ≤ a + b + c + d
≤-sum-3-of-4 {a = a} {b = b} {c = c} {d = d} =
  ≤-sum-extend-r {k = d} (≤-sum-3-of-3 {a = a} {b = b} {c = c})

≤-sum-4-of-4 : {a b c d : ℕ} -> d ≤ a + b + c + d
≤-sum-4-of-4 {a = a} {b = b} {c = c} {d = d} =
  ≤-sum-r {m = d} {n = a + b + c}

≤-sum-1-of-5 : {a b c d e : ℕ} -> a ≤ a + b + c + d + e
≤-sum-1-of-5 {a = a} {b = b} {c = c} {d = d} {e = e} =
  ≤-sum-extend-r {k = e} (≤-sum-1-of-4 {a = a} {b = b} {c = c} {d = d})

≤-sum-2-of-5 : {a b c d e : ℕ} -> b ≤ a + b + c + d + e
≤-sum-2-of-5 {a = a} {b = b} {c = c} {d = d} {e = e} =
  ≤-sum-extend-r {k = e} (≤-sum-2-of-4 {a = a} {b = b} {c = c} {d = d})

≤-sum-3-of-5 : {a b c d e : ℕ} -> c ≤ a + b + c + d + e
≤-sum-3-of-5 {a = a} {b = b} {c = c} {d = d} {e = e} =
  ≤-sum-extend-r {k = e} (≤-sum-3-of-4 {a = a} {b = b} {c = c} {d = d})

≤-sum-4-of-5 : {a b c d e : ℕ} -> d ≤ a + b + c + d + e
≤-sum-4-of-5 {a = a} {b = b} {c = c} {d = d} {e = e} =
  ≤-sum-extend-r {k = e} (≤-sum-4-of-4 {a = a} {b = b} {c = c} {d = d})

≤-sum-5-of-5 : {a b c d e : ℕ} -> e ≤ a + b + c + d + e
≤-sum-5-of-5 {a = a} {b = b} {c = c} {d = d} {e = e} =
  ≤-sum-r {m = e} {n = a + b + c + d}

≤-sum-1-of-8 : {a b c d e f g h : ℕ} -> a ≤ a + b + c + d + e + f + g + h
≤-sum-1-of-8 {a = a} {b = b} {c = c} {d = d} {e = e} {f = f} {g = g} {h = h} =
  ≤-sum-extend-r {k = h}
    (≤-sum-extend-r {k = g}
      (≤-sum-extend-r {k = f}
        (≤-sum-1-of-5 {a = a} {b = b} {c = c} {d = d} {e = e})))

≤-sum-2-of-8 : {a b c d e f g h : ℕ} -> b ≤ a + b + c + d + e + f + g + h
≤-sum-2-of-8 {a = a} {b = b} {c = c} {d = d} {e = e} {f = f} {g = g} {h = h} =
  ≤-sum-extend-r {k = h}
    (≤-sum-extend-r {k = g}
      (≤-sum-extend-r {k = f}
        (≤-sum-2-of-5 {a = a} {b = b} {c = c} {d = d} {e = e})))

≤-sum-3-of-8 : {a b c d e f g h : ℕ} -> c ≤ a + b + c + d + e + f + g + h
≤-sum-3-of-8 {a = a} {b = b} {c = c} {d = d} {e = e} {f = f} {g = g} {h = h} =
  ≤-sum-extend-r {k = h}
    (≤-sum-extend-r {k = g}
      (≤-sum-extend-r {k = f}
        (≤-sum-3-of-5 {a = a} {b = b} {c = c} {d = d} {e = e})))

≤-sum-4-of-8 : {a b c d e f g h : ℕ} -> d ≤ a + b + c + d + e + f + g + h
≤-sum-4-of-8 {a = a} {b = b} {c = c} {d = d} {e = e} {f = f} {g = g} {h = h} =
  ≤-sum-extend-r {k = h}
    (≤-sum-extend-r {k = g}
      (≤-sum-extend-r {k = f}
        (≤-sum-4-of-5 {a = a} {b = b} {c = c} {d = d} {e = e})))

≤-sum-5-of-8 : {a b c d e f g h : ℕ} -> e ≤ a + b + c + d + e + f + g + h
≤-sum-5-of-8 {a = a} {b = b} {c = c} {d = d} {e = e} {f = f} {g = g} {h = h} =
  ≤-sum-extend-r {k = h}
    (≤-sum-extend-r {k = g}
      (≤-sum-extend-r {k = f}
        (≤-sum-5-of-5 {a = a} {b = b} {c = c} {d = d} {e = e})))

≤-sum-6-of-8 : {a b c d e f g h : ℕ} -> f ≤ a + b + c + d + e + f + g + h
≤-sum-6-of-8 {a = a} {b = b} {c = c} {d = d} {e = e} {f = f} {g = g} {h = h} =
  ≤-sum-extend-r {k = h}
    (≤-sum-extend-r {k = g}
      (≤-sum-r {m = f} {n = a + b + c + d + e}))

≤-sum-7-of-8 : {a b c d e f g h : ℕ} -> g ≤ a + b + c + d + e + f + g + h
≤-sum-7-of-8 {a = a} {b = b} {c = c} {d = d} {e = e} {f = f} {g = g} {h = h} =
  ≤-sum-extend-r {k = h}
    (≤-sum-r {m = g} {n = a + b + c + d + e + f})

≤-sum-8-of-8 : {a b c d e f g h : ℕ} -> h ≤ a + b + c + d + e + f + g + h
≤-sum-8-of-8 {a = a} {b = b} {c = c} {d = d} {e = e} {f = f} {g = g} {h = h} =
  ≤-sum-r {m = h} {n = a + b + c + d + e + f + g}

≤-sum1-3 : (a b c : ℕ) -> a ≤ a + b + c
≤-sum1-3 a b c = ≤-sum-1-of-3 {a = a} {b = b} {c = c}

≤-sum2-3 : (a b c : ℕ) -> b ≤ a + b + c
≤-sum2-3 a b c = ≤-sum-2-of-3 {a = a} {b = b} {c = c}

≤-sum3-3 : (a b c : ℕ) -> c ≤ a + b + c
≤-sum3-3 a b c = ≤-sum-3-of-3 {a = a} {b = b} {c = c}

≤-sum1-4 : (a b c d : ℕ) -> a ≤ a + b + c + d
≤-sum1-4 a b c d = ≤-sum-1-of-4 {a = a} {b = b} {c = c} {d = d}

≤-sum2-4 : (a b c d : ℕ) -> b ≤ a + b + c + d
≤-sum2-4 a b c d = ≤-sum-2-of-4 {a = a} {b = b} {c = c} {d = d}

≤-sum3-4 : (a b c d : ℕ) -> c ≤ a + b + c + d
≤-sum3-4 a b c d = ≤-sum-3-of-4 {a = a} {b = b} {c = c} {d = d}

≤-sum4-4 : (a b c d : ℕ) -> d ≤ a + b + c + d
≤-sum4-4 a b c d = ≤-sum-4-of-4 {a = a} {b = b} {c = c} {d = d}

≤-sum1-5 : (a b c d e : ℕ) -> a ≤ a + b + c + d + e
≤-sum1-5 a b c d e = ≤-sum-1-of-5 {a = a} {b = b} {c = c} {d = d} {e = e}

≤-sum2-5 : (a b c d e : ℕ) -> b ≤ a + b + c + d + e
≤-sum2-5 a b c d e = ≤-sum-2-of-5 {a = a} {b = b} {c = c} {d = d} {e = e}

≤-sum3-5 : (a b c d e : ℕ) -> c ≤ a + b + c + d + e
≤-sum3-5 a b c d e = ≤-sum-3-of-5 {a = a} {b = b} {c = c} {d = d} {e = e}

≤-sum4-5 : (a b c d e : ℕ) -> d ≤ a + b + c + d + e
≤-sum4-5 a b c d e = ≤-sum-4-of-5 {a = a} {b = b} {c = c} {d = d} {e = e}

≤-sum5-5 : (a b c d e : ℕ) -> e ≤ a + b + c + d + e
≤-sum5-5 a b c d e = ≤-sum-5-of-5 {a = a} {b = b} {c = c} {d = d} {e = e}

≤-sum1-8 : (a b c d e f g h : ℕ) -> a ≤ a + b + c + d + e + f + g + h
≤-sum1-8 a b c d e f g h =
  ≤-sum-1-of-8 {a = a} {b = b} {c = c} {d = d} {e = e} {f = f} {g = g} {h = h}

≤-sum2-8 : (a b c d e f g h : ℕ) -> b ≤ a + b + c + d + e + f + g + h
≤-sum2-8 a b c d e f g h =
  ≤-sum-2-of-8 {a = a} {b = b} {c = c} {d = d} {e = e} {f = f} {g = g} {h = h}

≤-sum6-8 : (a b c d e f g h : ℕ) -> f ≤ a + b + c + d + e + f + g + h
≤-sum6-8 a b c d e f g h =
  ≤-sum-6-of-8 {a = a} {b = b} {c = c} {d = d} {e = e} {f = f} {g = g} {h = h}

≤-sum8-8 : (a b c d e f g h : ℕ) -> h ≤ a + b + c + d + e + f + g + h
≤-sum8-8 a b c d e f g h =
  ≤-sum-8-of-8 {a = a} {b = b} {c = c} {d = d} {e = e} {f = f} {g = g} {h = h}

≤-via-< : {a b c : ℕ} -> a ≤ b -> b < c -> a ≤ c
≤-via-< a≤b b<c = ≤-trans a≤b (<⇒≤ b<c)

compTy-subst : {A B : RawType} -> A ≡ B -> ComputableTy A -> ComputableTy B
compTy-subst refl c = c

compTm-subst : {A B : RawType} {t u : RawTerm}
  -> A ≡ B -> t ≡ u -> Computable A t -> Computable B u
compTm-subst refl refl c = c

compTyEq-subst : {A A' B B' : RawType}
  -> A ≡ A' -> B ≡ B' -> ComputableTyEq A B -> ComputableTyEq A' B'
compTyEq-subst refl refl c = c

compTmEq-subst : {A B : RawType} {t t' u u' : RawTerm}
  -> A ≡ B -> t ≡ t' -> u ≡ u'
  -> ComputableTmEq A t u -> ComputableTmEq B t' u'
compTmEq-subst refl refl refl c = c

envDrop : {gamma delta : Ctx} {sigma : Subst}
  -> Env (delta ++ gamma) sigma -> Env gamma (dropSub (length delta) sigma)
envDrop {delta = []} rho = rho
envDrop {delta = A ∷ delta} (envCons rho ca) = envDrop {delta = delta} rho

data EqEnv : Ctx -> Subst -> Subst -> Type where
  eqEnvNil : {sigma tau : Subst} -> EqEnv [] sigma tau
  eqEnvCons : {gamma : Ctx} {A : RawType} {sigma tau : Subst} {a b : RawTerm}
    -> EqEnv gamma sigma tau
    -> ComputableTyEq (subTy sigma A) (subTy tau A)
    -> ComputableTmEq (subTy sigma A) a b
    -> EqEnv (A ∷ gamma) (consSubst a sigma) (consSubst b tau)

eqEnvLeft : {gamma : Ctx} {sigma tau : Subst}
  -> EqEnv gamma sigma tau -> Env gamma sigma
eqEnvLeft eqEnvNil = envNil
eqEnvLeft (eqEnvCons {A = A} {sigma = sigma} {tau = tau} ee ctyEq eq) =
  envCons (eqEnvLeft ee)
    (proj₁ (compTmEq-sides {A = subTy sigma A} eq))

eqEnvRight : {gamma : Ctx} {sigma tau : Subst}
  -> EqEnv gamma sigma tau -> Env gamma tau
eqEnvRight eqEnvNil = envNil
eqEnvRight (eqEnvCons {A = A} {sigma = sigma} {tau = tau} ee ctyEq eq) =
  envCons (eqEnvRight ee)
    (compTm-conv ctyEq (proj₂ (compTmEq-sides eq)))

eqEnvReflLeft : {gamma : Ctx} {sigma tau : Subst}
  -> EqEnv gamma sigma tau -> EqEnv gamma sigma sigma
eqEnvReflLeft eqEnvNil = eqEnvNil
eqEnvReflLeft (eqEnvCons {A = A} {sigma = sigma} {tau = tau} ee ctyEq eq) =
  let
    ctyA = proj₁ (compTyEq-sides {A = subTy sigma A} {B = subTy tau A} ctyEq)
    ca = proj₁ (compTmEq-sides {A = subTy sigma A} eq)
  in
  eqEnvCons (eqEnvReflLeft ee)
    (compTyEq-refl {A = subTy sigma A} ctyA)
    (compTmEq-refl {A = subTy sigma A} ctyA ca)

eqEnvReflRight : {gamma : Ctx} {sigma tau : Subst}
  -> EqEnv gamma sigma tau -> EqEnv gamma tau tau
eqEnvReflRight eqEnvNil = eqEnvNil
eqEnvReflRight (eqEnvCons {A = A} {sigma = sigma} {tau = tau} ee ctyEq eq) =
  let
    ctyA = proj₂ (compTyEq-sides {A = subTy sigma A} {B = subTy tau A} ctyEq)
    ca = compTm-conv ctyEq (proj₂ (compTmEq-sides {A = subTy sigma A} eq))
  in
  eqEnvCons (eqEnvReflRight ee)
    (compTyEq-refl {A = subTy tau A} ctyA)
    (compTmEq-refl {A = subTy tau A} ctyA ca)

eqEnvDrop : {gamma delta : Ctx} {sigma tau : Subst}
  -> EqEnv (delta ++ gamma) sigma tau
  -> EqEnv gamma (dropSub (length delta) sigma) (dropSub (length delta) tau)
eqEnvDrop {delta = []} ee = ee
eqEnvDrop {delta = A ∷ delta} (eqEnvCons ee ctyEq eq) = eqEnvDrop {delta = delta} ee

eqEnvLookup : {gamma delta : Ctx} {A : RawType} {sigma tau : Subst}
  -> EqEnv (delta ++ (A ∷ gamma)) sigma tau
  -> ComputableTmEq (subTy sigma (wkTyBy (suc (length delta)) A))
       (applySubst sigma (length delta)) (applySubst tau (length delta))
eqEnvLookup {delta = []} {A = A} (eqEnvCons {sigma = sigma} {a = a} ee ctyEq eq) =
  compTmEq-subst (sym (lookupHereTy sigma a A)) refl refl eq
eqEnvLookup {delta = D ∷ delta} {A = A}
  (eqEnvCons {sigma = sigma} {a = a} ee ctyEq eq) =
  compTmEq-subst
    (sym (lookupWkCancel sigma a (suc (length delta)) A))
    refl refl
    (eqEnvLookup {delta = delta} ee)

eqEnvLookupTy : {gamma delta : Ctx} {A : RawType} {sigma tau : Subst}
  -> EqEnv (delta ++ (A ∷ gamma)) sigma tau
  -> ComputableTyEq (subTy sigma (wkTyBy (suc (length delta)) A))
       (subTy tau (wkTyBy (suc (length delta)) A))
eqEnvLookupTy {delta = []} {A = A}
  (eqEnvCons {sigma = sigma} {tau = tau} {a = a} {b = b} ee ctyEq eq) =
  compTyEq-subst (sym (lookupHereTy sigma a A)) (sym (lookupHereTy tau b A)) ctyEq
eqEnvLookupTy {delta = D ∷ delta} {A = A}
  (eqEnvCons {sigma = sigma} {tau = tau} {a = a} {b = b} ee ctyEq eq) =
  compTyEq-subst
    (sym (lookupWkCancel sigma a (suc (length delta)) A))
    (sym (lookupWkCancel tau b (suc (length delta)) A))
    (eqEnvLookupTy {delta = delta} ee)

singleSubstWkCancel : (a t : RawTerm)
  -> subTm (singleSubst a) (renTm sucRen t) ≡ t
singleSubstWkCancel a t =
  subTmRen (singleSubst a) sucRen t ∙ subTmId t

singleLift-apply : (a : RawTerm) (sigma : Subst) (n : ℕ)
  -> applySubst (consSubst a sigma) n
       ≡ applySubst (compSub (singleSubst a) (liftSubst sigma)) n
singleLift-apply a sigma zero = refl
singleLift-apply a sigma (suc n) =
  sym (singleSubstWkCancel a (applySubst sigma n))
  ∙ cong (subTm (singleSubst a)) (sym (liftSubst-apply-suc sigma n))
  ∙ sym (applySubst-compSub (singleSubst a) (liftSubst sigma) (suc n))

singleLiftTy : (a : RawTerm) (sigma : Subst) (B : RawType)
  -> subTy (consSubst a sigma) B
       ≡ subTy (singleSubst a) (subTy (liftSubst sigma) B)
singleLiftTy a sigma B =
  subTyEq (singleLift-apply a sigma) B
  ∙ sym (subTyComp (singleSubst a) (liftSubst sigma) B)

singleLiftTm : (a : RawTerm) (sigma : Subst) (t : RawTerm)
  -> subTm (consSubst a sigma) t
       ≡ subTm (singleSubst a) (subTm (liftSubst sigma) t)
singleLiftTm a sigma t =
  subTmEq (singleLift-apply a sigma) t
  ∙ sym (subTmComp (singleSubst a) (liftSubst sigma) t)

sigmaBranchTarget-apply : (b c : RawTerm) (sigma : Subst)
  -> (n : ℕ)
  -> applySubst (compSub (consSubst c (consSubst b sigma)) sigmaMotSub) n
       ≡ applySubst (consSubst (tmPair b c) sigma) n
sigmaBranchTarget-apply b c sigma zero = refl
sigmaBranchTarget-apply b c sigma (suc n) = refl

sigmaBranchTargetTy : (b c : RawTerm) (sigma : Subst) (M : RawType)
  -> subTy (consSubst c (consSubst b sigma)) (sigmaBranchTy M)
       ≡ subTy (consSubst (tmPair b c) sigma) M
sigmaBranchTargetTy b c sigma M =
  subTyComp (consSubst c (consSubst b sigma)) sigmaMotSub M
  ∙ subTyEq (sigmaBranchTarget-apply b c sigma) M

twoLiftCancelTm : (b c t : RawTerm)
  -> subTm (sigmaCompSub b c) (renTm sucRen (renTm sucRen t)) ≡ t
twoLiftCancelTm b c t =
  subTmRen (sigmaCompSub b c) sucRen (renTm sucRen t)
  ∙ subTmRen (consSubst b idSubst) sucRen t
  ∙ subTmId t

sigmaCompLift-apply : (b c : RawTerm) (sigma : Subst) (n : ℕ)
  -> applySubst (compSub (sigmaCompSub b c) (liftSubst (liftSubst sigma))) n
       ≡ applySubst (consSubst c (consSubst b sigma)) n
sigmaCompLift-apply b c sigma zero = refl
sigmaCompLift-apply b c sigma (suc zero) = refl
sigmaCompLift-apply b c sigma (suc (suc n)) =
  applySubst-compSub (sigmaCompSub b c) (liftSubst (liftSubst sigma)) (suc (suc n))
  ∙ cong (subTm (sigmaCompSub b c))
      (liftSubst-apply-suc (liftSubst sigma) (suc n)
       ∙ cong (renTm sucRen) (liftSubst-apply-suc sigma n))
  ∙ twoLiftCancelTm b c (applySubst sigma n)

sigmaCompLiftTm : (b c : RawTerm) (sigma : Subst) (m : RawTerm)
  -> subTm (sigmaCompSub b c) (subTm (liftSubst (liftSubst sigma)) m)
       ≡ subTm (consSubst c (consSubst b sigma)) m
sigmaCompLiftTm b c sigma m =
  subTmComp (sigmaCompSub b c) (liftSubst (liftSubst sigma)) m
  ∙ subTmEq (sigmaCompLift-apply b c sigma) m

qtrBranchTarget-apply : (a : RawTerm) (sigma : Subst) (n : ℕ)
  -> applySubst (compSub (consSubst a sigma) qtrBranchSub) n
       ≡ applySubst (consSubst (tmClass a) sigma) n
qtrBranchTarget-apply a sigma zero = refl
qtrBranchTarget-apply a sigma (suc n) = refl

qtrBranchTargetTy : (a : RawTerm) (sigma : Subst) (L : RawType)
  -> subTy (consSubst a sigma) (qtrBranchTy L)
       ≡ subTy (consSubst (tmClass a) sigma) L
qtrBranchTargetTy a sigma L =
  subTyComp (consSubst a sigma) qtrBranchSub L
  ∙ subTyEq (qtrBranchTarget-apply a sigma) L

qtrCompLiftTm : (a : RawTerm) (sigma : Subst) (l : RawTerm)
  -> subTm (qtrCompSub a) (subTm (liftSubst sigma) l)
       ≡ subTm (consSubst a sigma) l
qtrCompLiftTm a sigma l = sym (singleLiftTm a sigma l)

qtrCohTarget-apply : (a b : RawTerm) (sigma : Subst) (n : ℕ)
  -> applySubst (compSub (consSubst b (consSubst a sigma)) qtrCohSub) n
       ≡ applySubst (consSubst (tmClass a) sigma) n
qtrCohTarget-apply a b sigma zero = refl
qtrCohTarget-apply a b sigma (suc n) = refl

qtrCohTargetTy : (a b : RawTerm) (sigma : Subst) (L : RawType)
  -> subTy (consSubst b (consSubst a sigma)) (qtrCohTy L)
       ≡ subTy (consSubst (tmClass a) sigma) L
qtrCohTargetTy a b sigma L =
  subTyComp (consSubst b (consSubst a sigma)) qtrCohSub L
  ∙ subTyEq (qtrCohTarget-apply a b sigma) L

qtrCohLeftTm : (a b : RawTerm) (sigma : Subst) (l : RawTerm)
  -> subTm (consSubst b (consSubst a sigma)) (wkTmBy 1 l)
       ≡ subTm (consSubst a sigma) l
qtrCohLeftTm a b sigma l =
  subTmRen (consSubst b (consSubst a sigma)) (addRen 1) l ∙ refl

qtrCohRightTm : (a b : RawTerm) (sigma : Subst) (l : RawTerm)
  -> subTm (consSubst b (consSubst a sigma)) (renTm qtrSecondBranchRen l)
       ≡ subTm (consSubst b sigma) l
qtrCohRightTm a b sigma l =
  subTmRen (consSubst b (consSubst a sigma)) qtrSecondBranchRen l ∙ refl

computableResult : {A : RawType} {t : RawTerm}
  -> Computable A t -> Σ[ g ∈ RawTerm ] (t =>e g) × Computable A g
computableResult {A = tyTop} ct = tmStar , ct , evalStar
computableResult {A = tySigma A B} ct =
  let a , b , ev , ca , cb = computableSigma-elim ct in
  tmPair a b , ev , computableSigma-intro (a , b , evalPair , ca , cb)
computableResult {A = tyEq A a b} ct =
  let ev , eqab = computableEq-elim ct in
  tmR , ev , computableEq-intro (evalR , eqab)
computableResult {A = tyQtr A} ct =
  let a , ev , ca = computableQtr-elim ct in
  tmClass a , ev , computableQtr-intro (a , evalClass , ca)

computableTySigma-introAcc : {A B : RawType}
  -> (p : Acc _<_ (tyDepth (tySigma A B)))
  -> ComputableTy A
  -> ((a c : RawTerm) -> ComputableTmEq A a c
        -> ComputableTyEq (subTy (singleSubst a) B) (subTy (singleSubst c) B))
  -> ComputableTyAcc (tySigma A B) p
computableTySigma-introAcc {A} {B} (acc rs) cA fam =
  ComputableTyAcc-cast A
    (<-wf (tyDepth A)) (rs (tyDepth-fst<Sigma A B)) cA ,
  λ a c eq ->
    ComputableTyEqAcc-cast (subTy (singleSubst a) B) (subTy (singleSubst c) B)
      (<-wf (tyDepth (subTy (singleSubst a) B))) (rs (subTy-snd< A B a))
      (<-wf (tyDepth (subTy (singleSubst c) B))) (rs (subTy-snd< A B c))
      (fam a c
        (ComputableTmEqAcc-cast A
          (rs (tyDepth-fst<Sigma A B)) (<-wf (tyDepth A)) a c eq))

computableTySigma-intro : {A B : RawType}
  -> ComputableTy A
  -> ((a c : RawTerm) -> ComputableTmEq A a c
        -> ComputableTyEq (subTy (singleSubst a) B) (subTy (singleSubst c) B))
  -> ComputableTy (tySigma A B)
computableTySigma-intro {A} {B} =
  computableTySigma-introAcc (<-wf (tyDepth (tySigma A B)))

computableTyEqSigma-introAcc : {A B C D : RawType}
  -> (p : Acc _<_ (tyDepth (tySigma A B)))
  -> (q : Acc _<_ (tyDepth (tySigma C D)))
  -> ComputableTyEq A C
  -> ((a c : RawTerm) -> ComputableTmEq A a c
        -> ComputableTyEq (subTy (singleSubst a) B) (subTy (singleSubst c) D))
  -> ComputableTyEqAcc (tySigma A B) (tySigma C D) p q
computableTyEqSigma-introAcc {A} {B} {C} {D} (acc rsAB) (acc rsCD) eqAC fam =
  ComputableTyEqAcc-cast A C
    (<-wf (tyDepth A)) (rsAB (tyDepth-fst<Sigma A B))
    (<-wf (tyDepth C)) (rsCD (tyDepth-fst<Sigma C D))
    eqAC ,
  λ a c eq ->
    ComputableTyEqAcc-cast (subTy (singleSubst a) B) (subTy (singleSubst c) D)
      (<-wf (tyDepth (subTy (singleSubst a) B))) (rsAB (subTy-snd< A B a))
      (<-wf (tyDepth (subTy (singleSubst c) D))) (rsCD (subTy-snd< C D c))
      (fam a c
        (ComputableTmEqAcc-cast A
          (rsAB (tyDepth-fst<Sigma A B)) (<-wf (tyDepth A)) a c eq))

computableTyEqSigma-intro : {A B C D : RawType}
  -> ComputableTyEq A C
  -> ((a c : RawTerm) -> ComputableTmEq A a c
        -> ComputableTyEq (subTy (singleSubst a) B) (subTy (singleSubst c) D))
  -> ComputableTyEq (tySigma A B) (tySigma C D)
computableTyEqSigma-intro {A} {B} {C} {D} =
  computableTyEqSigma-introAcc
    (<-wf (tyDepth (tySigma A B))) (<-wf (tyDepth (tySigma C D)))

computableTmEqSigma-introAcc : {A B : RawType} {a b c d : RawTerm}
  -> (p : Acc _<_ (tyDepth (tySigma A B)))
  -> ComputableTmEq A a c
  -> ComputableTmEq (subTy (singleSubst a) B) b d
  -> ComputableTyEq (subTy (singleSubst a) B) (subTy (singleSubst c) B)
  -> ComputableTmEqAcc (tySigma A B) p (tmPair a b) (tmPair c d)
computableTmEqSigma-introAcc {A} {B} {a} {b} {c} {d} (acc rs) eqA eqB tyB =
  a , b , c , d , evalPair , evalPair ,
  ComputableTmEqAcc-cast A
    (<-wf (tyDepth A)) (rs (tyDepth-fst<Sigma A B)) a c eqA ,
  ComputableTmEqAcc-cast (subTy (singleSubst a) B)
    (<-wf (tyDepth (subTy (singleSubst a) B))) (rs (subTy-snd< A B a)) b d eqB ,
  ComputableTyEqAcc-cast (subTy (singleSubst a) B) (subTy (singleSubst c) B)
    (<-wf (tyDepth (subTy (singleSubst a) B))) (rs (subTy-snd< A B a))
    (<-wf (tyDepth (subTy (singleSubst c) B))) (rs (subTy-snd< A B c))
    tyB

computableTmEqSigma-intro : {A B : RawType} {a b c d : RawTerm}
  -> ComputableTmEq A a c
  -> ComputableTmEq (subTy (singleSubst a) B) b d
  -> ComputableTyEq (subTy (singleSubst a) B) (subTy (singleSubst c) B)
  -> ComputableTmEq (tySigma A B) (tmPair a b) (tmPair c d)
computableTmEqSigma-intro {A} {B} =
  computableTmEqSigma-introAcc (<-wf (tyDepth (tySigma A B)))

computableTmEqSigma-eval-introAcc : {A B : RawType} {t u a b c d : RawTerm}
  -> (p : Acc _<_ (tyDepth (tySigma A B)))
  -> t =>e tmPair a b
  -> u =>e tmPair c d
  -> ComputableTmEq A a c
  -> ComputableTmEq (subTy (singleSubst a) B) b d
  -> ComputableTyEq (subTy (singleSubst a) B) (subTy (singleSubst c) B)
  -> ComputableTmEqAcc (tySigma A B) p t u
computableTmEqSigma-eval-introAcc {A} {B} {a = a} {b} {c} {d} (acc rs) evt evu eqA eqB tyB =
  a , b , c , d , evt , evu ,
  ComputableTmEqAcc-cast A
    (<-wf (tyDepth A)) (rs (tyDepth-fst<Sigma A B)) a c eqA ,
  ComputableTmEqAcc-cast (subTy (singleSubst a) B)
    (<-wf (tyDepth (subTy (singleSubst a) B))) (rs (subTy-snd< A B a)) b d eqB ,
  ComputableTyEqAcc-cast (subTy (singleSubst a) B) (subTy (singleSubst c) B)
    (<-wf (tyDepth (subTy (singleSubst a) B))) (rs (subTy-snd< A B a))
    (<-wf (tyDepth (subTy (singleSubst c) B))) (rs (subTy-snd< A B c))
    tyB

computableTmEqSigma-eval-intro : {A B : RawType} {t u a b c d : RawTerm}
  -> t =>e tmPair a b
  -> u =>e tmPair c d
  -> ComputableTmEq A a c
  -> ComputableTmEq (subTy (singleSubst a) B) b d
  -> ComputableTyEq (subTy (singleSubst a) B) (subTy (singleSubst c) B)
  -> ComputableTmEq (tySigma A B) t u
computableTmEqSigma-eval-intro {A} {B} =
  computableTmEqSigma-eval-introAcc (<-wf (tyDepth (tySigma A B)))

SigmaComputableTmEq : RawType -> RawType -> RawTerm -> RawTerm -> Type
SigmaComputableTmEq A B t u =
  Σ[ a ∈ RawTerm ] Σ[ b ∈ RawTerm ] Σ[ c ∈ RawTerm ] Σ[ d ∈ RawTerm ]
      (t =>e tmPair a b)
    × (u =>e tmPair c d)
    × ComputableTmEq A a c
    × ComputableTmEq (subTy (singleSubst a) B) b d
    × ComputableTyEq (subTy (singleSubst a) B) (subTy (singleSubst c) B)

computableTmEqSigma-elimAcc : (A B : RawType)
  -> (p : Acc _<_ (tyDepth (tySigma A B))) (t u : RawTerm)
  -> ComputableTmEqAcc (tySigma A B) p t u
  -> SigmaComputableTmEq A B t u
computableTmEqSigma-elimAcc A B (acc rs) t u
  (a , b , c , d , evt , evu , eqA , eqB , tyB) =
  a , b , c , d , evt , evu ,
  ComputableTmEqAcc-cast A
    (rs (tyDepth-fst<Sigma A B)) (<-wf (tyDepth A)) a c eqA ,
  ComputableTmEqAcc-cast (subTy (singleSubst a) B)
    (rs (subTy-snd< A B a)) (<-wf (tyDepth (subTy (singleSubst a) B))) b d eqB ,
  ComputableTyEqAcc-cast (subTy (singleSubst a) B) (subTy (singleSubst c) B)
    (rs (subTy-snd< A B a)) (<-wf (tyDepth (subTy (singleSubst a) B)))
    (rs (subTy-snd< A B c)) (<-wf (tyDepth (subTy (singleSubst c) B)))
    tyB

computableTmEqSigma-elim : {A B : RawType} {t u : RawTerm}
  -> ComputableTmEq (tySigma A B) t u
  -> SigmaComputableTmEq A B t u
computableTmEqSigma-elim {A} {B} {t} {u} =
  computableTmEqSigma-elimAcc A B (<-wf (tyDepth (tySigma A B))) t u

SigmaComputableTy : RawType -> RawType -> Type
SigmaComputableTy A B =
    ComputableTy A
  × ((a c : RawTerm) -> ComputableTmEq A a c
      -> ComputableTyEq (subTy (singleSubst a) B) (subTy (singleSubst c) B))

computableTySigma-elimAcc : (A B : RawType)
  -> (p : Acc _<_ (tyDepth (tySigma A B)))
  -> ComputableTyAcc (tySigma A B) p
  -> SigmaComputableTy A B
computableTySigma-elimAcc A B (acc rs) (ctA , fam) =
  ComputableTyAcc-cast A
    (rs (tyDepth-fst<Sigma A B)) (<-wf (tyDepth A)) ctA ,
  λ a c eq ->
    ComputableTyEqAcc-cast (subTy (singleSubst a) B) (subTy (singleSubst c) B)
      (rs (subTy-snd< A B a)) (<-wf (tyDepth (subTy (singleSubst a) B)))
      (rs (subTy-snd< A B c)) (<-wf (tyDepth (subTy (singleSubst c) B)))
      (fam a c
        (ComputableTmEqAcc-cast A
          (<-wf (tyDepth A)) (rs (tyDepth-fst<Sigma A B)) a c eq))

computableTySigma-elim : {A B : RawType}
  -> ComputableTy (tySigma A B)
  -> SigmaComputableTy A B
computableTySigma-elim {A} {B} =
  computableTySigma-elimAcc A B (<-wf (tyDepth (tySigma A B)))

SigmaComputableTyEq : RawType -> RawType -> RawType -> RawType -> Type
SigmaComputableTyEq A B C D =
    ComputableTyEq A C
  × ((a c : RawTerm) -> ComputableTmEq A a c
      -> ComputableTyEq (subTy (singleSubst a) B) (subTy (singleSubst c) D))

computableTyEqSigma-elimAcc : (A B C D : RawType)
  -> (p : Acc _<_ (tyDepth (tySigma A B)))
  -> (q : Acc _<_ (tyDepth (tySigma C D)))
  -> ComputableTyEqAcc (tySigma A B) (tySigma C D) p q
  -> SigmaComputableTyEq A B C D
computableTyEqSigma-elimAcc A B C D (acc rsAB) (acc rsCD) (tyAC , fam) =
  ComputableTyEqAcc-cast A C
    (rsAB (tyDepth-fst<Sigma A B)) (<-wf (tyDepth A))
    (rsCD (tyDepth-fst<Sigma C D)) (<-wf (tyDepth C))
    tyAC ,
  λ a c eq ->
    ComputableTyEqAcc-cast (subTy (singleSubst a) B) (subTy (singleSubst c) D)
      (rsAB (subTy-snd< A B a)) (<-wf (tyDepth (subTy (singleSubst a) B)))
      (rsCD (subTy-snd< C D c)) (<-wf (tyDepth (subTy (singleSubst c) D)))
      (fam a c
        (ComputableTmEqAcc-cast A
          (<-wf (tyDepth A)) (rsAB (tyDepth-fst<Sigma A B)) a c eq))

computableTyEqSigma-elim : {A B C D : RawType}
  -> ComputableTyEq (tySigma A B) (tySigma C D)
  -> SigmaComputableTyEq A B C D
computableTyEqSigma-elim {A} {B} {C} {D} =
  computableTyEqSigma-elimAcc A B C D
    (<-wf (tyDepth (tySigma A B))) (<-wf (tyDepth (tySigma C D)))

computableTyEqForm-introAcc : {A : RawType} {a b : RawTerm}
  -> (p : Acc _<_ (tyDepth (tyEq A a b)))
  -> ComputableTy A
  -> Computable A a
  -> Computable A b
  -> ComputableTyAcc (tyEq A a b) p
computableTyEqForm-introAcc {A} {a} {b} (acc rs) cA ca cb =
  ComputableTyAcc-cast A
    (<-wf (tyDepth A)) (rs (tyDepth-base<Eq A a b)) cA ,
  ca ,
  cb

computableTyEqForm-intro : {A : RawType} {a b : RawTerm}
  -> ComputableTy A
  -> Computable A a
  -> Computable A b
  -> ComputableTy (tyEq A a b)
computableTyEqForm-intro {A} {a} {b} =
  computableTyEqForm-introAcc (<-wf (tyDepth (tyEq A a b)))

computableTyQtr-introAcc : {A : RawType}
  -> (p : Acc _<_ (tyDepth (tyQtr A)))
  -> ComputableTy A
  -> ComputableTyAcc (tyQtr A) p
computableTyQtr-introAcc {A} (acc rs) cA =
  ComputableTyAcc-cast A
    (<-wf (tyDepth A)) (rs (tyDepth-base<Qtr A)) cA

computableTyQtr-intro : {A : RawType}
  -> ComputableTy A
  -> ComputableTy (tyQtr A)
computableTyQtr-intro {A} =
  computableTyQtr-introAcc (<-wf (tyDepth (tyQtr A)))

computableTyQtr-elimAcc : (A : RawType)
  -> (p : Acc _<_ (tyDepth (tyQtr A)))
  -> ComputableTyAcc (tyQtr A) p
  -> ComputableTy A
computableTyQtr-elimAcc A (acc rs) cA =
  ComputableTyAcc-cast A
    (rs (tyDepth-base<Qtr A)) (<-wf (tyDepth A)) cA

computableTyQtr-elim : {A : RawType}
  -> ComputableTy (tyQtr A)
  -> ComputableTy A
computableTyQtr-elim {A} =
  computableTyQtr-elimAcc A (<-wf (tyDepth (tyQtr A)))

computableTyEqEqForm-introAcc : {A C : RawType} {a b c d : RawTerm}
  -> (p : Acc _<_ (tyDepth (tyEq A a b)))
  -> (q : Acc _<_ (tyDepth (tyEq C c d)))
  -> ComputableTyEq A C
  -> ComputableTmEq A a c
  -> ComputableTmEq A b d
  -> ComputableTyEqAcc (tyEq A a b) (tyEq C c d) p q
computableTyEqEqForm-introAcc {A} {C} {a} {b} {c} {d} (acc rsL) (acc rsR) tyAC eqac eqbd =
  ComputableTyEqAcc-cast A C
    (<-wf (tyDepth A)) (rsL (tyDepth-base<Eq A a b))
    (<-wf (tyDepth C)) (rsR (tyDepth-base<Eq C c d))
    tyAC ,
  ComputableTmEqAcc-cast A
    (<-wf (tyDepth A)) (rsL (tyDepth-base<Eq A a b)) a c eqac ,
  ComputableTmEqAcc-cast A
    (<-wf (tyDepth A)) (rsL (tyDepth-base<Eq A a b)) b d eqbd

computableTyEqEqForm-intro : {A C : RawType} {a b c d : RawTerm}
  -> ComputableTyEq A C
  -> ComputableTmEq A a c
  -> ComputableTmEq A b d
  -> ComputableTyEq (tyEq A a b) (tyEq C c d)
computableTyEqEqForm-intro {A} {C} {a} {b} {c} {d} =
  computableTyEqEqForm-introAcc
    (<-wf (tyDepth (tyEq A a b))) (<-wf (tyDepth (tyEq C c d)))

computableTyEqQtr-introAcc : {A C : RawType}
  -> (p : Acc _<_ (tyDepth (tyQtr A)))
  -> (q : Acc _<_ (tyDepth (tyQtr C)))
  -> ComputableTyEq A C
  -> ComputableTyEqAcc (tyQtr A) (tyQtr C) p q
computableTyEqQtr-introAcc {A} {C} (acc rsL) (acc rsR) tyAC =
  ComputableTyEqAcc-cast A C
    (<-wf (tyDepth A)) (rsL (tyDepth-base<Qtr A))
    (<-wf (tyDepth C)) (rsR (tyDepth-base<Qtr C))
    tyAC

computableTyEqQtr-intro : {A C : RawType}
  -> ComputableTyEq A C
  -> ComputableTyEq (tyQtr A) (tyQtr C)
computableTyEqQtr-intro {A} {C} =
  computableTyEqQtr-introAcc (<-wf (tyDepth (tyQtr A))) (<-wf (tyDepth (tyQtr C)))

computableTyEqQtr-elimAcc : (A C : RawType)
  -> (p : Acc _<_ (tyDepth (tyQtr A)))
  -> (q : Acc _<_ (tyDepth (tyQtr C)))
  -> ComputableTyEqAcc (tyQtr A) (tyQtr C) p q
  -> ComputableTyEq A C
computableTyEqQtr-elimAcc A C (acc rsA) (acc rsC) tyAC =
  ComputableTyEqAcc-cast A C
    (rsA (tyDepth-base<Qtr A)) (<-wf (tyDepth A))
    (rsC (tyDepth-base<Qtr C)) (<-wf (tyDepth C))
    tyAC

computableTyEqQtr-elim : {A C : RawType}
  -> ComputableTyEq (tyQtr A) (tyQtr C)
  -> ComputableTyEq A C
computableTyEqQtr-elim {A} {C} =
  computableTyEqQtr-elimAcc A C (<-wf (tyDepth (tyQtr A))) (<-wf (tyDepth (tyQtr C)))

computableTmEqEqForm-introAcc : {A : RawType} {a b t u : RawTerm}
  -> (p : Acc _<_ (tyDepth (tyEq A a b)))
  -> t =>e tmR
  -> u =>e tmR
  -> ComputableTmEq A a b
  -> ComputableTmEqAcc (tyEq A a b) p t u
computableTmEqEqForm-introAcc {A} {a} {b} (acc rs) evt evu eqab =
  evt , evu ,
  ComputableTmEqAcc-cast A
    (<-wf (tyDepth A)) (rs (tyDepth-base<Eq A a b)) a b eqab

computableTmEqEqForm-intro : {A : RawType} {a b t u : RawTerm}
  -> t =>e tmR
  -> u =>e tmR
  -> ComputableTmEq A a b
  -> ComputableTmEq (tyEq A a b) t u
computableTmEqEqForm-intro {A} {a} {b} =
  computableTmEqEqForm-introAcc (<-wf (tyDepth (tyEq A a b)))

EqFormComputableTmEq : RawType -> RawTerm -> RawTerm -> RawTerm -> RawTerm -> Type
EqFormComputableTmEq A a b t u =
  (t =>e tmR) × (u =>e tmR) × ComputableTmEq A a b

computableTmEqEqForm-elimAcc : (A : RawType) (a b : RawTerm)
  -> (p : Acc _<_ (tyDepth (tyEq A a b))) (t u : RawTerm)
  -> ComputableTmEqAcc (tyEq A a b) p t u
  -> EqFormComputableTmEq A a b t u
computableTmEqEqForm-elimAcc A a b (acc rs) t u (evt , evu , eqab) =
  evt , evu ,
  ComputableTmEqAcc-cast A
    (rs (tyDepth-base<Eq A a b)) (<-wf (tyDepth A)) a b eqab

computableTmEqEqForm-elim : {A : RawType} {a b t u : RawTerm}
  -> ComputableTmEq (tyEq A a b) t u
  -> EqFormComputableTmEq A a b t u
computableTmEqEqForm-elim {A} {a} {b} {t} {u} =
  computableTmEqEqForm-elimAcc A a b (<-wf (tyDepth (tyEq A a b))) t u

computableTmEqQtr-introAcc : {A : RawType} {t u p q : RawTerm}
  -> (accQ : Acc _<_ (tyDepth (tyQtr A)))
  -> t =>e tmClass p
  -> u =>e tmClass q
  -> ComputableTmEq A p p
  -> ComputableTmEq A q q
  -> ComputableTmEqAcc (tyQtr A) accQ t u
computableTmEqQtr-introAcc {A} {p = p} {q = q} (acc rs) evt evu epp eqq =
  p , q , evt , evu ,
  ComputableTmEqAcc-cast A
    (<-wf (tyDepth A)) (rs (tyDepth-base<Qtr A)) p p epp ,
  ComputableTmEqAcc-cast A
    (<-wf (tyDepth A)) (rs (tyDepth-base<Qtr A)) q q eqq

computableTmEqQtr-intro : {A : RawType} {t u p q : RawTerm}
  -> t =>e tmClass p
  -> u =>e tmClass q
  -> ComputableTmEq A p p
  -> ComputableTmEq A q q
  -> ComputableTmEq (tyQtr A) t u
computableTmEqQtr-intro {A} =
  computableTmEqQtr-introAcc (<-wf (tyDepth (tyQtr A)))

QtrComputableTmEq : RawType -> RawTerm -> RawTerm -> Type
QtrComputableTmEq A t u =
  Σ[ p ∈ RawTerm ] Σ[ q ∈ RawTerm ]
      (t =>e tmClass p) × (u =>e tmClass q)
    × ComputableTmEq A p p
    × ComputableTmEq A q q

computableTmEqQtr-elimAcc : (A : RawType)
  -> (accQ : Acc _<_ (tyDepth (tyQtr A))) (t u : RawTerm)
  -> ComputableTmEqAcc (tyQtr A) accQ t u
  -> QtrComputableTmEq A t u
computableTmEqQtr-elimAcc A (acc rs) t u (p , q , evt , evu , epp , eqq) =
  p , q , evt , evu ,
  ComputableTmEqAcc-cast A
    (rs (tyDepth-base<Qtr A)) (<-wf (tyDepth A)) p p epp ,
  ComputableTmEqAcc-cast A
    (rs (tyDepth-base<Qtr A)) (<-wf (tyDepth A)) q q eqq

computableTmEqQtr-elim : {A : RawType} {t u : RawTerm}
  -> ComputableTmEq (tyQtr A) t u
  -> QtrComputableTmEq A t u
computableTmEqQtr-elim {A} {t} {u} =
  computableTmEqQtr-elimAcc A (<-wf (tyDepth (tyQtr A))) t u

compTmEqElimLeft : {A : RawType} {d m u b c : RawTerm}
  -> d =>e tmPair b c
  -> ComputableTmEq A (subTm (sigmaCompSub b c) m) u
  -> ComputableTmEq A (tmElSigma d m) u
compTmEqElimLeft {A = tyTop} evd (evm , evu) =
  evalElSigma evd evm , evu
compTmEqElimLeft {A = tySigma A B} evd eq =
  let a , b , c , d , evm , evu , eqA , eqB , tyB = eq in
  a , b , c , d , evalElSigma evd evm , evu , eqA , eqB , tyB
compTmEqElimLeft {A = tyEq A a b} evd (evm , evu , eqab) =
  evalElSigma evd evm , evu , eqab
compTmEqElimLeft {A = tyQtr A} evd (a , b , evm , evu , caa , cbb) =
  a , b , evalElSigma evd evm , evu , caa , cbb

compTmEqElimRight : {A : RawType} {t d m b c : RawTerm}
  -> d =>e tmPair b c
  -> ComputableTmEq A t (subTm (sigmaCompSub b c) m)
  -> ComputableTmEq A t (tmElSigma d m)
compTmEqElimRight {A = tyTop} evd (evt , evm) =
  evt , evalElSigma evd evm
compTmEqElimRight {A = tySigma A B} evd eq =
  let a , b , c , d , evt , evm , eqA , eqB , tyB = eq in
  a , b , c , d , evt , evalElSigma evd evm , eqA , eqB , tyB
compTmEqElimRight {A = tyEq A a b} evd (evt , evm , eqab) =
  evt , evalElSigma evd evm , eqab
compTmEqElimRight {A = tyQtr A} evd (a , b , evt , evm , caa , cbb) =
  a , b , evt , evalElSigma evd evm , caa , cbb

compTmEqQtrElimLeft : {A : RawType} {p l u a : RawTerm}
  -> p =>e tmClass a
  -> ComputableTmEq A (subTm (qtrCompSub a) l) u
  -> ComputableTmEq A (tmElQtr l p) u
compTmEqQtrElimLeft {A = tyTop} evp (evl , evu) =
  evalElQtr evp evl , evu
compTmEqQtrElimLeft {A = tySigma A B} evp eq =
  let a , b , c , d , evl , evu , eqA , eqB , tyB = eq in
  a , b , c , d , evalElQtr evp evl , evu , eqA , eqB , tyB
compTmEqQtrElimLeft {A = tyEq A a b} evp (evl , evu , eqab) =
  evalElQtr evp evl , evu , eqab
compTmEqQtrElimLeft {A = tyQtr A} evp (a , b , evl , evu , caa , cbb) =
  a , b , evalElQtr evp evl , evu , caa , cbb

compTmEqQtrElimRight : {A : RawType} {t p l a : RawTerm}
  -> p =>e tmClass a
  -> ComputableTmEq A t (subTm (qtrCompSub a) l)
  -> ComputableTmEq A t (tmElQtr l p)
compTmEqQtrElimRight {A = tyTop} evp (evt , evl) =
  evt , evalElQtr evp evl
compTmEqQtrElimRight {A = tySigma A B} evp eq =
  let a , b , c , d , evt , evl , eqA , eqB , tyB = eq in
  a , b , c , d , evt , evalElQtr evp evl , eqA , eqB , tyB
compTmEqQtrElimRight {A = tyEq A a b} evp (evt , evl , eqab) =
  evt , evalElQtr evp evl , eqab
compTmEqQtrElimRight {A = tyQtr A} evp (a , b , evt , evl , caa , cbb) =
  a , b , evt , evalElQtr evp evl , caa , cbb

mutual
  mDeriv-ctxWF≤ : {J : JForm} -> (d : Derivable J)
    -> mCtxWF (derivToCtxWF d) ≤ mDeriv d
  mDeriv-ctxWF≤ d@(varStar wf _) =
    <⇒≤ (mDeriv-summand< d ≤-sum-l)
  mDeriv-ctxWF≤ d@(weakenTy _ wf) =
    <⇒≤ (mDeriv-summand< d ≤-sum-r)
  mDeriv-ctxWF≤ d@(weakenTyEq _ wf) =
    <⇒≤ (mDeriv-summand< d ≤-sum-r)
  mDeriv-ctxWF≤ d@(weakenTm _ wf) =
    <⇒≤ (mDeriv-summand< d ≤-sum-r)
  mDeriv-ctxWF≤ d@(weakenTmEq _ wf) =
    <⇒≤ (mDeriv-summand< d ≤-sum-r)
  mDeriv-ctxWF≤ d@(reflTy dA) =
    ≤-via-< (mDeriv-ctxWF≤ dA) (mDeriv-summand< d ≤-refl)
  mDeriv-ctxWF≤ d@(reflTm dt) =
    ≤-via-< (mDeriv-ctxWF≤ dt) (mDeriv-summand< d ≤-refl)
  mDeriv-ctxWF≤ d@(symTy dAB dB) =
    ≤-via-< (mDeriv-ctxWF≤ dAB) (mDeriv-summand< d ≤-sum-l)
  mDeriv-ctxWF≤ d@(symTm dtu du dA) =
    ≤-via-< (mDeriv-ctxWF≤ dtu)
      (mDeriv-summand< d (≤-sum1-3 (mDeriv dtu) (mDeriv du) (mDeriv dA)))
  mDeriv-ctxWF≤ d@(transTy dAB dBC) =
    ≤-via-< (mDeriv-ctxWF≤ dAB) (mDeriv-summand< d ≤-sum-l)
  mDeriv-ctxWF≤ d@(transTm dtu duv) =
    ≤-via-< (mDeriv-ctxWF≤ dtu) (mDeriv-summand< d ≤-sum-l)
  mDeriv-ctxWF≤ d@(conv dt dAB) =
    ≤-via-< (mDeriv-ctxWF≤ dt) (mDeriv-summand< d ≤-sum-l)
  mDeriv-ctxWF≤ d@(convEq dtu dAB) =
    ≤-via-< (mDeriv-ctxWF≤ dtu) (mDeriv-summand< d ≤-sum-l)
  mDeriv-ctxWF≤ d@(substTyRule dA fits) =
    ≤-via-< (mFits-ctxWF≤ fits) (mDeriv-summand< d ≤-sum-r)
  mDeriv-ctxWF≤ d@(substTyEqRule dAB fits) =
    ≤-via-< (mFits-ctxWF≤ fits) (mDeriv-summand< d ≤-sum-r)
  mDeriv-ctxWF≤ d@(substTmRule dt fits) =
    ≤-via-< (mFits-ctxWF≤ fits) (mDeriv-summand< d ≤-sum-r)
  mDeriv-ctxWF≤ d@(substTmEqRule dtu fits) =
    ≤-via-< (mFits-ctxWF≤ fits) (mDeriv-summand< d ≤-sum-r)
  mDeriv-ctxWF≤ d@(eqSubTyRule dA fitsEq) =
    ≤-via-< (mFitsEq-ctxWF≤ fitsEq) (mDeriv-summand< d ≤-sum-r)
  mDeriv-ctxWF≤ d@(eqSubTyEqRule dAB fitsEq) =
    ≤-via-< (mFitsEq-ctxWF≤ fitsEq) (mDeriv-summand< d ≤-sum-r)
  mDeriv-ctxWF≤ d@(eqSubTmRule dt fitsEq) =
    ≤-via-< (mFitsEq-ctxWF≤ fitsEq) (mDeriv-summand< d ≤-sum-r)
  mDeriv-ctxWF≤ d@(eqSubTmEqRule dtu fitsEq) =
    ≤-via-< (mFitsEq-ctxWF≤ fitsEq) (mDeriv-summand< d ≤-sum-r)
  mDeriv-ctxWF≤ d@(fTop wf) =
    <⇒≤ (mDeriv-summand< d ≤-refl)
  mDeriv-ctxWF≤ d@(iTop wf) =
    <⇒≤ (mDeriv-summand< d ≤-refl)
  mDeriv-ctxWF≤ d@(cTop dt) =
    ≤-via-< (mDeriv-ctxWF≤ dt) (mDeriv-summand< d ≤-refl)
  mDeriv-ctxWF≤ d@(fSigma dA dB) =
    ≤-via-< (mDeriv-ctxWF≤ dA) (mDeriv-summand< d ≤-sum-l)
  mDeriv-ctxWF≤ d@(fSigmaEq dAC dB dBD) =
    ≤-via-< (mDeriv-ctxWF≤ dAC)
      (mDeriv-summand< d (≤-sum1-3 (mDeriv dAC) (mDeriv dB) (mDeriv dBD)))
  mDeriv-ctxWF≤ d@(iSigma da db dSigma) =
    ≤-via-< (mDeriv-ctxWF≤ da)
      (mDeriv-summand< d (≤-sum1-3 (mDeriv da) (mDeriv db) (mDeriv dSigma)))
  mDeriv-ctxWF≤ d@(iSigmaEq dac dbd dA dB) =
    ≤-via-< (mDeriv-ctxWF≤ dac)
      (mDeriv-summand< d (≤-sum1-4 (mDeriv dac) (mDeriv dbd) (mDeriv dA) (mDeriv dB)))
  mDeriv-ctxWF≤ d@(eSigma dM dd dm) =
    ≤-via-< (mDeriv-ctxWF≤ dd)
      (mDeriv-summand< d (≤-sum2-3 (mDeriv dM) (mDeriv dd) (mDeriv dm)))
  mDeriv-ctxWF≤ d@(eSigmaEq dM dd dm dmEq) =
    ≤-via-< (mDeriv-ctxWF≤ dd)
      (mDeriv-summand< d (≤-sum2-4 (mDeriv dM) (mDeriv dd) (mDeriv dm) (mDeriv dmEq)))
  mDeriv-ctxWF≤ d@(cSigma dM dSigma db dc dm) =
    ≤-via-< (mDeriv-ctxWF≤ db)
      (mDeriv-summand< d
        (≤-sum3-5 (mDeriv dM) (mDeriv dSigma) (mDeriv db) (mDeriv dc) (mDeriv dm)))
  mDeriv-ctxWF≤ d@(fEq dA da db) =
    ≤-via-< (mDeriv-ctxWF≤ dA)
      (mDeriv-summand< d (≤-sum1-3 (mDeriv dA) (mDeriv da) (mDeriv db)))
  mDeriv-ctxWF≤ d@(fEqEq dAC dac dbd) =
    ≤-via-< (mDeriv-ctxWF≤ dAC)
      (mDeriv-summand< d (≤-sum1-3 (mDeriv dAC) (mDeriv dac) (mDeriv dbd)))
  mDeriv-ctxWF≤ d@(iEq da) =
    ≤-via-< (mDeriv-ctxWF≤ da) (mDeriv-summand< d ≤-refl)
  mDeriv-ctxWF≤ d@(iEqEq dab) =
    ≤-via-< (mDeriv-ctxWF≤ dab) (mDeriv-summand< d ≤-refl)
  mDeriv-ctxWF≤ d@(eEqStar dp dA da db) =
    ≤-via-< (mDeriv-ctxWF≤ dp)
      (mDeriv-summand< d (≤-sum1-4 (mDeriv dp) (mDeriv dA) (mDeriv da) (mDeriv db)))
  mDeriv-ctxWF≤ d@(cEq dp dA da db) =
    ≤-via-< (mDeriv-ctxWF≤ dp)
      (mDeriv-summand< d (≤-sum1-4 (mDeriv dp) (mDeriv dA) (mDeriv da) (mDeriv db)))
  mDeriv-ctxWF≤ d@(fQtr dA) =
    ≤-via-< (mDeriv-ctxWF≤ dA) (mDeriv-summand< d ≤-refl)
  mDeriv-ctxWF≤ d@(fQtrEq dAB) =
    ≤-via-< (mDeriv-ctxWF≤ dAB) (mDeriv-summand< d ≤-refl)
  mDeriv-ctxWF≤ d@(iQtr da) =
    ≤-via-< (mDeriv-ctxWF≤ da) (mDeriv-summand< d ≤-refl)
  mDeriv-ctxWF≤ d@(iQtrEq da db) =
    ≤-via-< (mDeriv-ctxWF≤ da) (mDeriv-summand< d ≤-sum-l)
  mDeriv-ctxWF≤ d@(eQtr dL dp dBranch dl dcoh) =
    ≤-via-< (mDeriv-ctxWF≤ dp)
      (mDeriv-summand< d
        (≤-sum2-5 (mDeriv dL) (mDeriv dp) (mDeriv dBranch) (mDeriv dl) (mDeriv dcoh)))
  mDeriv-ctxWF≤ d@(eQtrEq dL dp dBranch dl dl' dll' dcoh dcoh') =
    ≤-via-< (mDeriv-ctxWF≤ dp)
      (mDeriv-summand< d
        (≤-sum2-8 (mDeriv dL) (mDeriv dp) (mDeriv dBranch) (mDeriv dl)
          (mDeriv dl') (mDeriv dll') (mDeriv dcoh) (mDeriv dcoh')))
  mDeriv-ctxWF≤ d@(cQtr dL da dBranch dl dcoh) =
    ≤-via-< (mDeriv-ctxWF≤ da)
      (mDeriv-summand< d
        (≤-sum2-5 (mDeriv dL) (mDeriv da) (mDeriv dBranch) (mDeriv dl) (mDeriv dcoh)))

  mFits-ctxWF≤ : {gamma delta : Ctx} {sigma : Subst}
    -> (fits : FitsSubst gamma delta sigma)
    -> mCtxWF (fitsSubstCtxWF fits) ≤ mFits fits
  mFits-ctxWF≤ (fitsNil {delta = delta} {sigma = sigma} wf) =
    <⇒≤ (mFits-fitsNil-wf< {delta = delta} {sigma = sigma} wf)
  mFits-ctxWF≤ (fitsCons fits dt) =
    ≤-via-< (mFits-ctxWF≤ fits) (mFits-fitsCons-fits< fits dt)

  mFitsEq-ctxWF≤ : {gamma delta : Ctx} {sigma tau : Subst}
    -> (fitsEq : FitsEqSubst gamma delta sigma tau)
    -> mCtxWF (fitsEqSubstCtxWF fitsEq) ≤ mFitsEq fitsEq
  mFitsEq-ctxWF≤ (fitsEqNil {delta = delta} {sigma = sigma} {tau = tau} wf) =
    <⇒≤ (mFitsEq-fitsEqNil-wf< {delta = delta} {sigma = sigma} {tau = tau} wf)
  mFitsEq-ctxWF≤ (fitsEqCons fitsEq dtu) =
    ≤-via-< (mFitsEq-ctxWF≤ fitsEq) (mFitsEq-fitsEqCons-fitsEq< fitsEq dtu)

fitsEqCtxMeasure<Deriv : {J : JForm} {gamma delta : Ctx} {sigma tau : Subst}
  -> (d : Derivable J)
  -> (fitsEq : FitsEqSubst gamma delta sigma tau)
  -> mFitsEq fitsEq + mCtxWF (derivToCtxWF d) < suc (mDeriv d + mFitsEq fitsEq)
fitsEqCtxMeasure<Deriv d fitsEq =
  <-suc-of-≤
    (≤-trans
      (+-mono-≤ ≤-refl (mDeriv-ctxWF≤ d))
      (NatProps.≤-reflexive (NatProps.+-comm (mFitsEq fitsEq) (mDeriv d))))

fitsEqCtx-tail< : {gamma delta : Ctx} {sigma tau : Subst}
    {A : RawType} {t u : RawTerm}
  -> (fitsEq : FitsEqSubst gamma delta sigma tau)
  -> (dtu : Derivable (termEq gamma t u (subTy sigma A)))
  -> (wfΔ : CtxWF delta)
  -> (dA : Derivable (isType delta A))
  -> mFitsEq fitsEq + mCtxWF wfΔ
     < mFitsEq (fitsEqCons fitsEq dtu) + mCtxWF (wfCons wfΔ dA)
fitsEqCtx-tail< fitsEq dtu wfΔ dA =
  +-mono-<-≤
    (mFitsEq-fitsEqCons-fitsEq< fitsEq dtu)
    (<⇒≤ (mCtxWF-wfCons-wf< wfΔ dA))

fitsEqCtx-headDeriv< : {gamma delta : Ctx} {sigma tau : Subst}
    {A : RawType} {t u : RawTerm}
  -> (fitsEq : FitsEqSubst gamma delta sigma tau)
  -> (dtu : Derivable (termEq gamma t u (subTy sigma A)))
  -> (wfΔ : CtxWF delta)
  -> (dA : Derivable (isType delta A))
  -> mDeriv dA
     < mFitsEq (fitsEqCons fitsEq dtu) + mCtxWF (wfCons wfΔ dA)
fitsEqCtx-headDeriv< fitsEq dtu wfΔ dA =
  ≤-trans (mCtxWF-wfCons-deriv< wfΔ dA)
    (≤-sum-r {m = mCtxWF (wfCons wfΔ dA)} {n = mFitsEq (fitsEqCons fitsEq dtu)})

mutual
  fundTyEqEnv : {gamma : Ctx} {A : RawType} {sigma tau : Subst}
    -> (d : Derivable (isType gamma A)) -> Acc _<_ (mDeriv d) -> EqEnv gamma sigma tau
    -> ComputableTyEq (subTy sigma A) (subTy tau A)
  fundTyEqEnv {sigma = sigma} {tau = tau}
    d@(weakenTy {delta = delta} {A = A} dA wf) (acc rec) ee =
    compTyEq-subst
      (sym (subTyRen sigma (addRen (length delta)) A))
      (sym (subTyRen tau (addRen (length delta)) A))
      (fundTyEqEnv dA
        (rec {y = mDeriv dA} (mDeriv-summand< d ≤-sum-l))
        (eqEnvDrop {delta = delta} ee))
  fundTyEqEnv {sigma = sigma} {tau = tau}
    d@(substTyRule {sigma = theta} {A = A} dA fits) (acc rec) ee =
    compTyEq-subst
      (sym (subTyComp sigma theta A))
      (sym (subTyComp tau theta A))
      (fundTyEqEnv dA
        (rec {y = mDeriv dA} (mDeriv-summand< d ≤-sum-l))
        (fundFitsSameEq fits
          (rec {y = mFits fits} (mDeriv-summand< d ≤-sum-r))
          ee))
  fundTyEqEnv (fTop wf) _ ee = tt
  fundTyEqEnv {sigma = sigma} {tau = tau} d@(fSigma {A = A} {B = B} dA dB) (acc rec) ee =
    let tyA = fundTyEqEnv dA (rec {y = mDeriv dA} (mDeriv-summand< d ≤-sum-l)) ee in
    computableTyEqSigma-intro
      {A = subTy sigma A} {B = subTy (liftSubst sigma) B}
      {C = subTy tau A} {D = subTy (liftSubst tau) B}
      tyA
    λ a c eq ->
      compTyEq-subst
        (singleLiftTy a sigma B)
        (singleLiftTy c tau B)
        (fundTyEqEnv dB
          (rec {y = mDeriv dB} (mDeriv-summand< d ≤-sum-r))
          (eqEnvCons ee tyA eq))
  fundTyEqEnv {sigma = sigma} {tau = tau} d@(fEq {A = A} {a = a} {b = b} dA da db) (acc rec) ee =
    computableTyEqEqForm-intro
      {A = subTy sigma A} {C = subTy tau A}
      {a = subTm sigma a} {b = subTm sigma b}
      {c = subTm tau a} {d = subTm tau b}
      (fundTyEqEnv dA
        (rec {y = mDeriv dA}
          (mDeriv-summand< d (≤-sum1-3 (mDeriv dA) (mDeriv da) (mDeriv db))))
        ee)
      (proj₁
        (fundTmEqEnv da
          (rec {y = mDeriv da}
            (mDeriv-summand< d (≤-sum2-3 (mDeriv dA) (mDeriv da) (mDeriv db))))
          ee))
      (proj₁
        (fundTmEqEnv db
          (rec {y = mDeriv db}
            (mDeriv-summand< d (≤-sum3-3 (mDeriv dA) (mDeriv da) (mDeriv db))))
          ee))
  fundTyEqEnv {sigma = sigma} {tau = tau} d@(fQtr {A = A} dA) (acc rec) ee =
    computableTyEqQtr-intro
      {A = subTy sigma A} {C = subTy tau A}
      (fundTyEqEnv dA (rec {y = mDeriv dA} (mDeriv-summand< d ≤-refl)) ee)

  fundTyEqEqEnv : {gamma : Ctx} {A B : RawType} {sigma tau : Subst}
    -> (d : Derivable (typeEq gamma A B)) -> Acc _<_ (mDeriv d) -> EqEnv gamma sigma tau
    -> ComputableTyEq (subTy sigma A) (subTy tau B)
  fundTyEqEqEnv {sigma = sigma} {tau = tau}
    d@(weakenTyEq {delta = delta} {A = A} {B = B} dAB wf) (acc rec) ee =
    compTyEq-subst
      (sym (subTyRen sigma (addRen (length delta)) A))
      (sym (subTyRen tau (addRen (length delta)) B))
      (fundTyEqEqEnv dAB
        (rec {y = mDeriv dAB} (mDeriv-summand< d ≤-sum-l))
        (eqEnvDrop {delta = delta} ee))
  fundTyEqEqEnv d@(reflTy dA) (acc rec) ee =
    fundTyEqEnv dA (rec {y = mDeriv dA} (mDeriv-summand< d ≤-refl)) ee
  fundTyEqEqEnv {sigma = sigma} {tau = tau} d@(symTy {A = A} {B = B} dAB dB) (acc rec) ee =
    compTyEq-trans
      {A = subTy sigma B} {B = subTy tau B} {C = subTy tau A}
      (fundTyEqEnv dB (rec {y = mDeriv dB} (mDeriv-summand< d ≤-sum-r)) ee)
      (compTyEq-sym {A = subTy tau A} {B = subTy tau B}
        (fundTyEqEqEnv dAB
          (rec {y = mDeriv dAB} (mDeriv-summand< d ≤-sum-l))
          (eqEnvReflRight ee)))
  fundTyEqEqEnv {sigma = sigma} {tau = tau} d@(transTy {A = A} {B = B} {C = C} dAB dBC) (acc rec) ee =
    compTyEq-trans
      {A = subTy sigma A} {B = subTy tau B} {C = subTy tau C}
      (fundTyEqEqEnv dAB (rec {y = mDeriv dAB} (mDeriv-summand< d ≤-sum-l)) ee)
      (fundTyEqEqEnv dBC
        (rec {y = mDeriv dBC} (mDeriv-summand< d ≤-sum-r))
        (eqEnvReflRight ee))
  fundTyEqEqEnv {sigma = sigma} {tau = tau}
    d@(substTyEqRule {sigma = theta} {A = A} {B = B} dAB fits) (acc rec) ee =
    compTyEq-subst
      (sym (subTyComp sigma theta A))
      (sym (subTyComp tau theta B))
      (fundTyEqEqEnv dAB
        (rec {y = mDeriv dAB} (mDeriv-summand< d ≤-sum-l))
        (fundFitsSameEq fits
          (rec {y = mFits fits} (mDeriv-summand< d ≤-sum-r))
          ee))
  fundTyEqEqEnv {sigma = sigma} {tau = tau}
    dAll@(eqSubTyRule {sigma = theta} {tau = eta} {A = A} d fitsEq) (acc rec) ee =
    compTyEq-subst
      (sym (subTyComp sigma theta A))
      (sym (subTyComp tau eta A))
      (fundTyEqEnv d
        (rec {y = mDeriv d} (mDeriv-summand< dAll ≤-sum-l))
        (fundFitsEqEnv fitsEq (derivToCtxWF d)
          (rec {y = mFitsEq fitsEq + mCtxWF (derivToCtxWF d)}
            (fitsEqCtxMeasure<Deriv d fitsEq))
          ee))
  fundTyEqEqEnv {sigma = sigma} {tau = tau}
    dAll@(eqSubTyEqRule {sigma = theta} {tau = eta} {A = A} {B = B} d fitsEq) (acc rec) ee =
    compTyEq-subst
      (sym (subTyComp sigma theta A))
      (sym (subTyComp tau eta B))
      (fundTyEqEqEnv d
        (rec {y = mDeriv d} (mDeriv-summand< dAll ≤-sum-l))
        (fundFitsEqEnv fitsEq (derivToCtxWF d)
          (rec {y = mFitsEq fitsEq + mCtxWF (derivToCtxWF d)}
            (fitsEqCtxMeasure<Deriv d fitsEq))
          ee))
  fundTyEqEqEnv {sigma = sigma} {tau = tau}
    d@(fSigmaEq {A = A} {B = B} {C = C} {D = D} dAC dB dBD) (acc rec) ee =
    let
      accAC =
        rec {y = mDeriv dAC}
          (mDeriv-summand< d (≤-sum1-3 (mDeriv dAC) (mDeriv dB) (mDeriv dBD)))
      tyAC = fundTyEqEqEnv dAC accAC ee
      tyACτ = fundTyEqEqEnv dAC accAC (eqEnvReflRight ee)
      tyA =
        compTyEq-trans
          {A = subTy sigma A} {B = subTy tau C} {C = subTy tau A}
          tyAC
          (compTyEq-sym {A = subTy tau A} {B = subTy tau C} tyACτ)
    in
    computableTyEqSigma-intro
      {A = subTy sigma A} {B = subTy (liftSubst sigma) B}
      {C = subTy tau C} {D = subTy (liftSubst tau) D}
      tyAC
    λ a c eq ->
      compTyEq-subst
        (singleLiftTy a sigma B)
        (singleLiftTy c tau D)
        (fundTyEqEqEnv dBD
          (rec {y = mDeriv dBD}
            (mDeriv-summand< d (≤-sum3-3 (mDeriv dAC) (mDeriv dB) (mDeriv dBD))))
          (eqEnvCons ee tyA eq))
  fundTyEqEqEnv {sigma = sigma} {tau = tau}
    d@(fEqEq {A = A} {C = C} {a = a} {b = b} {c = c} {d = d0} dAC daeq dbeq) (acc rec) ee =
    computableTyEqEqForm-intro
      {A = subTy sigma A} {C = subTy tau C}
      {a = subTm sigma a} {b = subTm sigma b}
      {c = subTm tau c} {d = subTm tau d0}
      (fundTyEqEqEnv dAC
        (rec {y = mDeriv dAC}
          (mDeriv-summand< d (≤-sum1-3 (mDeriv dAC) (mDeriv daeq) (mDeriv dbeq))))
        ee)
      (proj₁
        (fundTmEqEqEnv daeq
          (rec {y = mDeriv daeq}
            (mDeriv-summand< d (≤-sum2-3 (mDeriv dAC) (mDeriv daeq) (mDeriv dbeq))))
          ee))
      (proj₁
        (fundTmEqEqEnv dbeq
          (rec {y = mDeriv dbeq}
            (mDeriv-summand< d (≤-sum3-3 (mDeriv dAC) (mDeriv daeq) (mDeriv dbeq))))
          ee))
  fundTyEqEqEnv {sigma = sigma} {tau = tau} d@(fQtrEq {A = A} {B = B} dAB) (acc rec) ee =
    computableTyEqQtr-intro
      {A = subTy sigma A} {C = subTy tau B}
      (fundTyEqEqEnv dAB (rec {y = mDeriv dAB} (mDeriv-summand< d ≤-refl)) ee)

  fundTmEqEnv : {gamma : Ctx} {t : RawTerm} {A : RawType} {sigma tau : Subst}
    -> (d : Derivable (hasTy gamma t A)) -> Acc _<_ (mDeriv d) -> EqEnv gamma sigma tau
    -> ComputableTmEq (subTy sigma A) (subTm sigma t) (subTm tau t)
       × ComputableTyEq (subTy sigma A) (subTy tau A)
  fundTmEqEnv (varStar wf dA) _ ee =
    eqEnvLookup ee , eqEnvLookupTy ee
  fundTmEqEnv {sigma = sigma} {tau = tau}
    d@(weakenTm {delta = delta} {t = t} {A = A} dt wf) (acc rec) ee =
    let tm , ty = fundTmEqEnv dt
          (rec {y = mDeriv dt} (mDeriv-summand< d ≤-sum-l))
          (eqEnvDrop {delta = delta} ee)
    in
    compTmEq-subst
      (sym (subTyRen sigma (addRen (length delta)) A))
      (sym (subTmRen sigma (addRen (length delta)) t))
      (sym (subTmRen tau (addRen (length delta)) t))
      tm ,
    compTyEq-subst
      (sym (subTyRen sigma (addRen (length delta)) A))
      (sym (subTyRen tau (addRen (length delta)) A))
      ty
  fundTmEqEnv {A = B} {sigma = sigma} {tau = tau}
    d@(conv {A = A} {B = B} dt dAB) (acc rec) ee =
    let
      tm , tyA = fundTmEqEnv dt
        (rec {y = mDeriv dt} (mDeriv-summand< d ≤-sum-l))
        ee
      accAB = rec {y = mDeriv dAB} (mDeriv-summand< d ≤-sum-r)
      tyABσ = fundTyEqEqEnv dAB accAB (eqEnvReflLeft ee)
      tyABστ = fundTyEqEqEnv dAB accAB ee
      tyB =
        compTyEq-trans
          {A = subTy sigma B} {B = subTy sigma A} {C = subTy tau B}
          (compTyEq-sym {A = subTy sigma A} {B = subTy sigma B} tyABσ)
          tyABστ
    in
    compTmEq-conv {A = subTy sigma A} {B = subTy sigma B} tyABσ tm , tyB
  fundTmEqEnv {sigma = sigma} {tau = tau}
    d@(substTmRule {sigma = theta} {t = t} {A = A} dt fits) (acc rec) ee =
    let tm , ty = fundTmEqEnv dt
          (rec {y = mDeriv dt} (mDeriv-summand< d ≤-sum-l))
          (fundFitsSameEq fits
            (rec {y = mFits fits} (mDeriv-summand< d ≤-sum-r))
            ee)
    in
    compTmEq-subst
      (sym (subTyComp sigma theta A))
      (sym (subTmComp sigma theta t))
      (sym (subTmComp tau theta t))
      tm ,
    compTyEq-subst
      (sym (subTyComp sigma theta A))
      (sym (subTyComp tau theta A))
      ty
  fundTmEqEnv (iTop wf) _ ee = (evalStar , evalStar) , tt
  fundTmEqEnv {sigma = sigma} {tau = tau}
    d@(iSigma {a = a} {b = b} {A = A} {B = B} da db dSig) (acc rec) ee =
    let
      caeq , tyA =
        fundTmEqEnv da
          (rec {y = mDeriv da}
            (mDeriv-summand< d (≤-sum1-3 (mDeriv da) (mDeriv db) (mDeriv dSig))))
          ee
      tySig =
        fundTyEqEnv dSig
          (rec {y = mDeriv dSig}
            (mDeriv-summand< d (≤-sum3-3 (mDeriv da) (mDeriv db) (mDeriv dSig))))
          ee
      _ , famB =
        computableTySigma-elim
          {A = subTy sigma A} {B = subTy (liftSubst sigma) B}
          (proj₁
            (compTyEq-sides
              {A = tySigma (subTy sigma A) (subTy (liftSubst sigma) B)}
              {B = tySigma (subTy tau A) (subTy (liftSubst tau) B)}
              tySig))
      tyB = famB (subTm sigma a) (subTm tau a) caeq
      cbeq =
        compTmEq-subst
          (subTyComp sigma (singleSubst a) B
           ∙ singleLiftTy (subTm sigma a) sigma B)
          refl refl
          (proj₁
            (fundTmEqEnv db
              (rec {y = mDeriv db}
                (mDeriv-summand< d (≤-sum2-3 (mDeriv da) (mDeriv db) (mDeriv dSig))))
              ee))
    in
    computableTmEqSigma-intro
      {A = subTy sigma A} {B = subTy (liftSubst sigma) B}
      {a = subTm sigma a} {b = subTm sigma b}
      {c = subTm tau a} {d = subTm tau b}
      caeq cbeq tyB ,
    tySig
  fundTmEqEnv {sigma = sigma} {tau = tau}
    d@(eSigma {A = A} {B = B} {M = M} {d = d0} {m = m} dM dd dm) (acc rec) ee =
    let
      accM =
        rec {y = mDeriv dM}
          (mDeriv-summand< d (≤-sum1-3 (mDeriv dM) (mDeriv dd) (mDeriv dm)))
      accd =
        rec {y = mDeriv dd}
          (mDeriv-summand< d (≤-sum2-3 (mDeriv dM) (mDeriv dd) (mDeriv dm)))
      accm =
        rec {y = mDeriv dm}
          (mDeriv-summand< d (≤-sum3-3 (mDeriv dM) (mDeriv dd) (mDeriv dm)))
      ddEq , tySig = fundTmEqEnv dd accd ee
      tyA , famB =
        computableTyEqSigma-elim
          {A = subTy sigma A} {B = subTy (liftSubst sigma) B}
          {C = subTy tau A} {D = subTy (liftSubst tau) B}
          tySig
      cSig =
        proj₁
          (compTyEq-sides
            {A = tySigma (subTy sigma A) (subTy (liftSubst sigma) B)}
            {B = tySigma (subTy tau A) (subTy (liftSubst tau) B)}
            tySig)
      ctyA , famLeft =
        computableTySigma-elim
          {A = subTy sigma A} {B = subTy (liftSubst sigma) B}
          cSig
      b , c , e , f , evd , eve , eqB , eqCraw , tyCraw =
        computableTmEqSigma-elim
          {A = subTy sigma A} {B = subTy (liftSubst sigma) B}
          {t = subTm sigma d0} {u = subTm tau d0}
          ddEq
      cb = proj₁ (compTmEq-sides {A = subTy sigma A} eqB)
      ccRaw =
        proj₁
          (compTmEq-sides
            {A = subTy (singleSubst b) (subTy (liftSubst sigma) B)}
            eqCraw)
      eqBB = compTmEq-refl {A = subTy sigma A} ctyA cb
      tyBB = famLeft b b eqBB
      ctyB =
        proj₁
          (compTyEq-sides
            {A = subTy (singleSubst b) (subTy (liftSubst sigma) B)}
            {B = subTy (singleSubst b) (subTy (liftSubst sigma) B)}
            tyBB)
      eqCC =
        compTmEq-refl
          {A = subTy (singleSubst b) (subTy (liftSubst sigma) B)}
          ctyB ccRaw
      eqDPair =
        computableTmEqSigma-eval-intro
          {A = subTy sigma A} {B = subTy (liftSubst sigma) B}
          {t = subTm sigma d0} {u = tmPair b c}
          {a = b} {b = c} {c = b} {d = c}
          evd evalPair eqBB eqCC tyBB
      tyDPairRaw =
        fundTyEqEnv dM accM
          (eqEnvCons
            (eqEnvReflLeft ee)
            (compTyEq-refl {A = tySigma (subTy sigma A) (subTy (liftSubst sigma) B)} cSig)
            eqDPair)
      tyDPair =
        compTyEq-subst
          (sym (subTyComp sigma (singleSubst d0) M))
          refl
          tyDPairRaw
      tyResult =
        compTyEq-subst
          (sym (subTyComp sigma (singleSubst d0) M))
          (sym (subTyComp tau (singleSubst d0) M))
          (fundTyEqEnv dM accM (eqEnvCons ee tySig ddEq))
      tyC =
        compTyEq-subst
          (sym (singleLiftTy b sigma B))
          (sym (singleLiftTy e tau B))
          (famB b e eqB)
      eqC =
        compTmEq-subst (sym (singleLiftTy b sigma B)) refl refl eqCraw
      branchEq =
        proj₁ (fundTmEqEnv dm accm (eqEnvCons (eqEnvCons ee tyA eqB) tyC eqC))
      eqSources =
        compTmEq-subst
          (sigmaBranchTargetTy b c sigma M)
          (sym (sigmaCompLiftTm b c sigma m))
          (sym (sigmaCompLiftTm e f tau m))
          branchEq
    in
    compTmEq-conv
      {A = subTy (consSubst (tmPair b c) sigma) M}
      {B = subTy sigma (subTy (singleSubst d0) M)}
      (compTyEq-sym
        {A = subTy sigma (subTy (singleSubst d0) M)}
        {B = subTy (consSubst (tmPair b c) sigma) M}
        tyDPair)
      (compTmEqElimRight eve (compTmEqElimLeft evd eqSources)) ,
    tyResult
  fundTmEqEnv {sigma = sigma} {tau = tau} d@(iEq {A = A} {a = a} da) (acc rec) ee =
    let
      eqA , tyA =
        fundTmEqEnv da (rec {y = mDeriv da} (mDeriv-summand< d ≤-refl)) ee
      ctyA = proj₁ (compTyEq-sides {A = subTy sigma A} {B = subTy tau A} tyA)
      ca = proj₁ (compTmEq-sides {A = subTy sigma A} eqA)
    in
    computableTmEqEqForm-intro
      {A = subTy sigma A} {a = subTm sigma a} {b = subTm sigma a}
      {t = tmR} {u = tmR}
      evalR evalR (compTmEq-refl {A = subTy sigma A} ctyA ca) ,
    computableTyEqEqForm-intro
      {A = subTy sigma A} {C = subTy tau A}
      {a = subTm sigma a} {b = subTm sigma a}
      {c = subTm tau a} {d = subTm tau a}
      tyA eqA eqA
  fundTmEqEnv {sigma = sigma} {tau = tau} d@(iQtr {A = A} {a = a} da) (acc rec) ee =
    let
      eqA , tyA =
        fundTmEqEnv da (rec {y = mDeriv da} (mDeriv-summand< d ≤-refl)) ee
      ctyA = proj₁ (compTyEq-sides {A = subTy sigma A} {B = subTy tau A} tyA)
      ca , ca' = compTmEq-sides {A = subTy sigma A} eqA
    in
    computableTmEqQtr-intro
      {A = subTy sigma A}
      {t = tmClass (subTm sigma a)} {u = tmClass (subTm tau a)}
      {p = subTm sigma a} {q = subTm tau a}
      evalClass evalClass
      (compTmEq-refl {A = subTy sigma A} ctyA ca)
      (compTmEq-refl {A = subTy sigma A} ctyA ca') ,
    computableTyEqQtr-intro {A = subTy sigma A} {C = subTy tau A} tyA
  fundTmEqEnv {sigma = sigma} {tau = tau}
    d@(eQtr {A = A} {L = L} {l = l} {p = p} dL dp dBranch dl coh) (acc rec) ee =
    let
      accL =
        rec {y = mDeriv dL}
          (mDeriv-summand< d
            (≤-sum1-5 (mDeriv dL) (mDeriv dp) (mDeriv dBranch) (mDeriv dl) (mDeriv coh)))
      accp =
        rec {y = mDeriv dp}
          (mDeriv-summand< d
            (≤-sum2-5 (mDeriv dL) (mDeriv dp) (mDeriv dBranch) (mDeriv dl) (mDeriv coh)))
      accCoh =
        rec {y = mDeriv coh}
          (mDeriv-summand< d
            (≤-sum5-5 (mDeriv dL) (mDeriv dp) (mDeriv dBranch) (mDeriv dl) (mDeriv coh)))
      dpEq , tyQtrEq = fundTmEqEnv dp accp ee
      cQtr =
        proj₁
          (compTyEq-sides
            {A = tyQtr (subTy sigma A)} {B = tyQtr (subTy tau A)}
            tyQtrEq)
      tyQ = computableTyEqQtr-elim {A = subTy sigma A} {C = subTy tau A} tyQtrEq
      cQ = proj₁ (compTyEq-sides {A = subTy sigma A} {B = subTy tau A} tyQ)
      a , b , evp , evp' , caa , cbb =
        computableTmEqQtr-elim
          {A = subTy sigma A} {t = subTm sigma p} {u = subTm tau p}
          dpEq
      ca = proj₁ (compTmEq-sides {A = subTy sigma A} caa)
      eqAA = compTmEq-refl {A = subTy sigma A} cQ ca
      eqPClass =
        computableTmEqQtr-intro
          {A = subTy sigma A}
          {t = subTm sigma p} {u = tmClass a}
          {p = a} {q = a}
          evp evalClass eqAA eqAA
      tyPClassRaw =
        fundTyEqEnv dL accL
          (eqEnvCons
            (eqEnvReflLeft ee)
            (compTyEq-refl {A = tyQtr (subTy sigma A)} cQtr)
            eqPClass)
      tyPClass =
        compTyEq-subst
          (sym (subTyComp sigma (singleSubst p) L))
          refl
          tyPClassRaw
      tyResult =
        compTyEq-subst
          (sym (subTyComp sigma (singleSubst p) L))
          (sym (subTyComp tau (singleSubst p) L))
          (fundTyEqEnv dL accL (eqEnvCons ee tyQtrEq dpEq))
      tyHead =
        compTyEq-subst
          (sym (lookupHereTy sigma a A))
          (sym (lookupHereTy tau a A))
          tyQ
      headEq =
        compTmEq-subst
          (sym (lookupHereTy sigma a A))
          refl refl
          cbb
      branchEq =
        proj₁ (fundTmEqEqEnv coh accCoh
          (eqEnvCons
            (eqEnvCons ee tyQ caa)
            tyHead
            headEq))
      eqSources =
        compTmEq-subst
          (qtrCohTargetTy a b sigma L)
          (qtrCohLeftTm a b sigma l ∙ sym (qtrCompLiftTm a sigma l))
          (qtrCohRightTm a b tau l ∙ sym (qtrCompLiftTm b tau l))
          branchEq
    in
    compTmEq-conv
      {A = subTy (consSubst (tmClass a) sigma) L}
      {B = subTy sigma (subTy (singleSubst p) L)}
      (compTyEq-sym
        {A = subTy sigma (subTy (singleSubst p) L)}
        {B = subTy (consSubst (tmClass a) sigma) L}
        tyPClass)
      (compTmEqQtrElimRight evp' (compTmEqQtrElimLeft evp eqSources)) ,
    tyResult

  fundTmEqEqEnv : {gamma : Ctx} {t u : RawTerm} {A : RawType} {sigma tau : Subst}
    -> (d : Derivable (termEq gamma t u A)) -> Acc _<_ (mDeriv d) -> EqEnv gamma sigma tau
    -> ComputableTmEq (subTy sigma A) (subTm sigma t) (subTm tau u)
       × ComputableTyEq (subTy sigma A) (subTy tau A)
  fundTmEqEqEnv {sigma = sigma} {tau = tau}
    d@(weakenTmEq {delta = delta} {t = t} {u = u} {A = A} dtu wf) (acc rec) ee =
    let tm , ty =
          fundTmEqEqEnv dtu
            (rec {y = mDeriv dtu} (mDeriv-summand< d ≤-sum-l))
            (eqEnvDrop {delta = delta} ee)
    in
    compTmEq-subst
      (sym (subTyRen sigma (addRen (length delta)) A))
      (sym (subTmRen sigma (addRen (length delta)) t))
      (sym (subTmRen tau (addRen (length delta)) u))
      tm ,
    compTyEq-subst
      (sym (subTyRen sigma (addRen (length delta)) A))
      (sym (subTyRen tau (addRen (length delta)) A))
      ty
  fundTmEqEqEnv d@(reflTm dt) (acc rec) ee =
    fundTmEqEnv dt (rec {y = mDeriv dt} (mDeriv-summand< d ≤-refl)) ee
  fundTmEqEqEnv {A = A} {sigma = sigma} {tau = tau}
    d@(symTm {t = t} {u = u} dtu du dA) (acc rec) ee =
    let
      duEq , tyστ =
        fundTmEqEnv du
          (rec {y = mDeriv du}
            (mDeriv-summand< d (≤-sum2-3 (mDeriv dtu) (mDeriv du) (mDeriv dA))))
          ee
      eqRight =
        proj₁
          (fundTmEqEqEnv dtu
            (rec {y = mDeriv dtu}
              (mDeriv-summand< d (≤-sum1-3 (mDeriv dtu) (mDeriv du) (mDeriv dA))))
            (eqEnvReflRight ee))
    in
    compTmEq-trans
      {A = subTy sigma A} {t = subTm sigma u} {u = subTm tau u} {v = subTm tau t}
      duEq
      (compTmEq-conv
        {A = subTy tau A} {B = subTy sigma A}
        (compTyEq-sym {A = subTy sigma A} {B = subTy tau A} tyστ)
        (compTmEq-sym {A = subTy tau A} eqRight)) ,
    tyστ
  fundTmEqEqEnv {A = A} {sigma = sigma} {tau = tau}
    d@(transTm {t = t} {u = u} {v = v} dtu duv) (acc rec) ee =
    let
      dtuEq , tyστ =
        fundTmEqEqEnv dtu (rec {y = mDeriv dtu} (mDeriv-summand< d ≤-sum-l)) ee
      eqRight =
        proj₁
          (fundTmEqEqEnv duv
            (rec {y = mDeriv duv} (mDeriv-summand< d ≤-sum-r))
            (eqEnvReflRight ee))
    in
    compTmEq-trans
      {A = subTy sigma A} {t = subTm sigma t} {u = subTm tau u} {v = subTm tau v}
      dtuEq
      (compTmEq-conv
        {A = subTy tau A} {B = subTy sigma A}
        (compTyEq-sym {A = subTy sigma A} {B = subTy tau A} tyστ)
        eqRight) ,
    tyστ
  fundTmEqEqEnv {sigma = sigma} {tau = tau}
    d@(convEq {t = t} {u = u} {A = A} {B = B} dtu dAB) (acc rec) ee =
    let
      tm , tyA =
        fundTmEqEqEnv dtu (rec {y = mDeriv dtu} (mDeriv-summand< d ≤-sum-l)) ee
      accAB = rec {y = mDeriv dAB} (mDeriv-summand< d ≤-sum-r)
      tyABσ = fundTyEqEqEnv dAB accAB (eqEnvReflLeft ee)
      tyABστ = fundTyEqEqEnv dAB accAB ee
      tyB =
        compTyEq-trans
          {A = subTy sigma B} {B = subTy sigma A} {C = subTy tau B}
          (compTyEq-sym {A = subTy sigma A} {B = subTy sigma B} tyABσ)
          tyABστ
    in
    compTmEq-conv {A = subTy sigma A} {B = subTy sigma B} tyABσ tm , tyB
  fundTmEqEqEnv {sigma = sigma} {tau = tau}
    d@(substTmEqRule {sigma = theta} {t = t} {u = u} {A = A} dtu fits) (acc rec) ee =
    let tm , ty =
          fundTmEqEqEnv dtu
            (rec {y = mDeriv dtu} (mDeriv-summand< d ≤-sum-l))
            (fundFitsSameEq fits
              (rec {y = mFits fits} (mDeriv-summand< d ≤-sum-r))
              ee)
    in
    compTmEq-subst
      (sym (subTyComp sigma theta A))
      (sym (subTmComp sigma theta t))
      (sym (subTmComp tau theta u))
      tm ,
    compTyEq-subst
      (sym (subTyComp sigma theta A))
      (sym (subTyComp tau theta A))
      ty
  fundTmEqEqEnv {sigma = sigma} {tau = tau}
    dAll@(eqSubTmRule {sigma = theta} {tau = eta} {t = t} {A = A} d fitsEq) (acc rec) ee =
    let
      accD = rec {y = mDeriv d} (mDeriv-summand< dAll ≤-sum-l)
      tm , ty =
        fundTmEqEnv d accD
          (fundFitsEqEnv fitsEq (derivToCtxWF d)
            (rec {y = mFitsEq fitsEq + mCtxWF (derivToCtxWF d)}
              (fitsEqCtxMeasure<Deriv d fitsEq))
            ee)
      tmLeft , tyLeft =
        fundTmEqEnv d accD
          (fundFitsEqLeftEnv fitsEq
            (rec {y = mFitsEq fitsEq} (mDeriv-summand< dAll ≤-sum-r))
            ee)
    in
    compTmEq-subst
      (sym (subTyComp sigma theta A))
      (sym (subTmComp sigma theta t))
      (sym (subTmComp tau eta t))
      tm ,
    compTyEq-subst
      (sym (subTyComp sigma theta A))
      (sym (subTyComp tau theta A))
      tyLeft
  fundTmEqEqEnv {sigma = sigma} {tau = tau}
    dAll@(eqSubTmEqRule {sigma = theta} {tau = eta} {t = t} {u = u} {A = A} d fitsEq) (acc rec) ee =
    let
      accD = rec {y = mDeriv d} (mDeriv-summand< dAll ≤-sum-l)
      tm , ty =
        fundTmEqEqEnv d accD
          (fundFitsEqEnv fitsEq (derivToCtxWF d)
            (rec {y = mFitsEq fitsEq + mCtxWF (derivToCtxWF d)}
              (fitsEqCtxMeasure<Deriv d fitsEq))
            ee)
      tmLeft , tyLeft =
        fundTmEqEqEnv d accD
          (fundFitsEqLeftEnv fitsEq
            (rec {y = mFitsEq fitsEq} (mDeriv-summand< dAll ≤-sum-r))
            ee)
    in
    compTmEq-subst
      (sym (subTyComp sigma theta A))
      (sym (subTmComp sigma theta t))
      (sym (subTmComp tau eta u))
      tm ,
    compTyEq-subst
      (sym (subTyComp sigma theta A))
      (sym (subTyComp tau theta A))
      tyLeft
  fundTmEqEqEnv d@(cTop dt) (acc rec) ee =
    let tm , ty = fundTmEqEnv dt (rec {y = mDeriv dt} (mDeriv-summand< d ≤-refl)) ee in
    (proj₁ tm , evalStar) , tt
  fundTmEqEqEnv {sigma = sigma} {tau = tau}
    d@(iSigmaEq {a = a} {b = b} {c = c} {d = d0} {A = A} {B = B} daeq dbeq dA dB) (acc rec) ee =
    let
      caeq , tyA =
        fundTmEqEqEnv daeq
          (rec {y = mDeriv daeq}
            (mDeriv-summand< d
              (≤-sum1-4 (mDeriv daeq) (mDeriv dbeq) (mDeriv dA) (mDeriv dB))))
          ee
      tySig =
        computableTyEqSigma-intro
        {A = subTy sigma A} {B = subTy (liftSubst sigma) B}
        {C = subTy tau A} {D = subTy (liftSubst tau) B}
        tyA
        λ x y eq ->
          compTyEq-subst
            (singleLiftTy x sigma B)
            (singleLiftTy y tau B)
            (fundTyEqEnv dB
              (rec {y = mDeriv dB}
                (mDeriv-summand< d
                  (≤-sum4-4 (mDeriv daeq) (mDeriv dbeq) (mDeriv dA) (mDeriv dB))))
              (eqEnvCons ee tyA eq))
      tyB =
        let _ , famB =
              computableTySigma-elim
                {A = subTy sigma A} {B = subTy (liftSubst sigma) B}
                (proj₁
                  (compTyEq-sides
                    {A = tySigma (subTy sigma A) (subTy (liftSubst sigma) B)}
                    {B = tySigma (subTy tau A) (subTy (liftSubst tau) B)}
                    tySig))
        in
        famB (subTm sigma a) (subTm tau c) caeq
      cbeq =
        compTmEq-subst
          (subTyComp sigma (singleSubst a) B
           ∙ singleLiftTy (subTm sigma a) sigma B)
          refl refl
          (proj₁
            (fundTmEqEqEnv dbeq
              (rec {y = mDeriv dbeq}
                (mDeriv-summand< d
                  (≤-sum2-4 (mDeriv daeq) (mDeriv dbeq) (mDeriv dA) (mDeriv dB))))
              ee))
    in
    computableTmEqSigma-intro
      {A = subTy sigma A} {B = subTy (liftSubst sigma) B}
      {a = subTm sigma a} {b = subTm sigma b}
      {c = subTm tau c} {d = subTm tau d0}
      caeq cbeq tyB ,
    tySig
  fundTmEqEqEnv {sigma = sigma} {tau = tau}
    dAll@(eSigmaEq {A = A} {B = B} {M = M} {d = d0} {d' = d1} {m = m} {m' = m'} dM dd dm dmEq) (acc rec) ee =
    let
      accM =
        rec {y = mDeriv dM}
          (mDeriv-summand< dAll (≤-sum1-4 (mDeriv dM) (mDeriv dd) (mDeriv dm) (mDeriv dmEq)))
      accd =
        rec {y = mDeriv dd}
          (mDeriv-summand< dAll (≤-sum2-4 (mDeriv dM) (mDeriv dd) (mDeriv dm) (mDeriv dmEq)))
      accmEq =
        rec {y = mDeriv dmEq}
          (mDeriv-summand< dAll (≤-sum4-4 (mDeriv dM) (mDeriv dd) (mDeriv dm) (mDeriv dmEq)))
      ddEq , tySig = fundTmEqEqEnv dd accd ee
      ddRight = proj₁ (fundTmEqEqEnv dd accd (eqEnvReflRight ee))
      ddSelf =
        compTmEq-trans
          {A = tySigma (subTy sigma A) (subTy (liftSubst sigma) B)}
          {t = subTm sigma d0} {u = subTm tau d1} {v = subTm tau d0}
          ddEq
          (compTmEq-conv
            {A = tySigma (subTy tau A) (subTy (liftSubst tau) B)}
            {B = tySigma (subTy sigma A) (subTy (liftSubst sigma) B)}
            (compTyEq-sym
              {A = tySigma (subTy sigma A) (subTy (liftSubst sigma) B)}
              {B = tySigma (subTy tau A) (subTy (liftSubst tau) B)}
              tySig)
            (compTmEq-sym
              {A = tySigma (subTy tau A) (subTy (liftSubst tau) B)}
              ddRight))
      tyA , famB =
        computableTyEqSigma-elim
          {A = subTy sigma A} {B = subTy (liftSubst sigma) B}
          {C = subTy tau A} {D = subTy (liftSubst tau) B}
          tySig
      cSig =
        proj₁
          (compTyEq-sides
            {A = tySigma (subTy sigma A) (subTy (liftSubst sigma) B)}
            {B = tySigma (subTy tau A) (subTy (liftSubst tau) B)}
            tySig)
      ctyA , famLeft =
        computableTySigma-elim
          {A = subTy sigma A} {B = subTy (liftSubst sigma) B}
          cSig
      b , c , e , f , evd , eve , eqB , eqCraw , tyCraw =
        computableTmEqSigma-elim
          {A = subTy sigma A} {B = subTy (liftSubst sigma) B}
          {t = subTm sigma d0} {u = subTm tau d1}
          ddEq
      cb = proj₁ (compTmEq-sides {A = subTy sigma A} eqB)
      ccRaw =
        proj₁
          (compTmEq-sides
            {A = subTy (singleSubst b) (subTy (liftSubst sigma) B)}
            eqCraw)
      eqBB = compTmEq-refl {A = subTy sigma A} ctyA cb
      tyBB = famLeft b b eqBB
      ctyB =
        proj₁
          (compTyEq-sides
            {A = subTy (singleSubst b) (subTy (liftSubst sigma) B)}
            {B = subTy (singleSubst b) (subTy (liftSubst sigma) B)}
            tyBB)
      eqCC =
        compTmEq-refl
          {A = subTy (singleSubst b) (subTy (liftSubst sigma) B)}
          ctyB ccRaw
      eqDPair =
        computableTmEqSigma-eval-intro
          {A = subTy sigma A} {B = subTy (liftSubst sigma) B}
          {t = subTm sigma d0} {u = tmPair b c}
          {a = b} {b = c} {c = b} {d = c}
          evd evalPair eqBB eqCC tyBB
      tyDPairRaw =
        fundTyEqEnv dM accM
          (eqEnvCons
            (eqEnvReflLeft ee)
            (compTyEq-refl {A = tySigma (subTy sigma A) (subTy (liftSubst sigma) B)} cSig)
            eqDPair)
      tyDPair =
        compTyEq-subst
          (sym (subTyComp sigma (singleSubst d0) M))
          refl
          tyDPairRaw
      tyResult =
        compTyEq-subst
          (sym (subTyComp sigma (singleSubst d0) M))
          (sym (subTyComp tau (singleSubst d0) M))
          (fundTyEqEnv dM accM (eqEnvCons ee tySig ddSelf))
      tyC =
        compTyEq-subst
          (sym (singleLiftTy b sigma B))
          (sym (singleLiftTy e tau B))
          (famB b e eqB)
      eqC =
        compTmEq-subst (sym (singleLiftTy b sigma B)) refl refl eqCraw
      branchEq =
        proj₁ (fundTmEqEqEnv dmEq accmEq (eqEnvCons (eqEnvCons ee tyA eqB) tyC eqC))
      eqSources =
        compTmEq-subst
          (sigmaBranchTargetTy b c sigma M)
          (sym (sigmaCompLiftTm b c sigma m))
          (sym (sigmaCompLiftTm e f tau m'))
          branchEq
    in
    compTmEq-conv
      {A = subTy (consSubst (tmPair b c) sigma) M}
      {B = subTy sigma (subTy (singleSubst d0) M)}
      (compTyEq-sym
        {A = subTy sigma (subTy (singleSubst d0) M)}
        {B = subTy (consSubst (tmPair b c) sigma) M}
        tyDPair)
      (compTmEqElimRight eve (compTmEqElimLeft evd eqSources)) ,
    tyResult
  fundTmEqEqEnv {sigma = sigma} {tau = tau}
    d@(cSigma {A = A} {B = B} {M = M} {b = b} {c = c} {m = m} dM dSig db dc dm) (acc rec) ee =
    let
      bσ = subTm sigma b
      cσ = subTm sigma c
      bτ = subTm tau b
      cτ = subTm tau c
      accM =
        rec {y = mDeriv dM}
          (mDeriv-summand< d
            (≤-sum1-5 (mDeriv dM) (mDeriv dSig) (mDeriv db) (mDeriv dc) (mDeriv dm)))
      accSig =
        rec {y = mDeriv dSig}
          (mDeriv-summand< d
            (≤-sum2-5 (mDeriv dM) (mDeriv dSig) (mDeriv db) (mDeriv dc) (mDeriv dm)))
      accb =
        rec {y = mDeriv db}
          (mDeriv-summand< d
            (≤-sum3-5 (mDeriv dM) (mDeriv dSig) (mDeriv db) (mDeriv dc) (mDeriv dm)))
      accc =
        rec {y = mDeriv dc}
          (mDeriv-summand< d
            (≤-sum4-5 (mDeriv dM) (mDeriv dSig) (mDeriv db) (mDeriv dc) (mDeriv dm)))
      accm =
        rec {y = mDeriv dm}
          (mDeriv-summand< d
            (≤-sum5-5 (mDeriv dM) (mDeriv dSig) (mDeriv db) (mDeriv dc) (mDeriv dm)))
      tySig = fundTyEqEnv dSig accSig ee
      tyA , famB =
        computableTyEqSigma-elim
          {A = subTy sigma A} {B = subTy (liftSubst sigma) B}
          {C = subTy tau A} {D = subTy (liftSubst tau) B}
          tySig
      cSig =
        proj₁
          (compTyEq-sides
            {A = tySigma (subTy sigma A) (subTy (liftSubst sigma) B)}
            {B = tySigma (subTy tau A) (subTy (liftSubst tau) B)}
            tySig)
      ctyA , famLeft =
        computableTySigma-elim
          {A = subTy sigma A} {B = subTy (liftSubst sigma) B}
          cSig
      eqB , tyA' = fundTmEqEnv db accb ee
      tyC =
        compTyEq-subst
          (sym (singleLiftTy bσ sigma B))
          (sym (singleLiftTy bτ tau B))
          (famB bσ bτ eqB)
      tyCpair = famLeft bσ bτ eqB
      eqC =
        compTmEq-subst
          (subTyComp sigma (singleSubst b) B)
          refl refl
          (proj₁ (fundTmEqEnv dc accc ee))
      eqCpair =
        compTmEq-subst
          (subTyComp sigma (singleSubst b) B
           ∙ singleLiftTy bσ sigma B)
          refl refl
          (proj₁ (fundTmEqEnv dc accc ee))
      pairEq =
        computableTmEqSigma-intro
          {A = subTy sigma A} {B = subTy (liftSubst sigma) B}
          {a = bσ} {b = cσ} {c = bτ} {d = cτ}
          eqB eqCpair tyCpair
      tyResult =
        compTyEq-subst
          (sym (subTyComp sigma (singleSubst (tmPair b c)) M))
          (sym (subTyComp tau (singleSubst (tmPair b c)) M))
          (fundTyEqEnv dM accM (eqEnvCons ee tySig pairEq))
      branchEq =
        proj₁ (fundTmEqEnv dm accm (eqEnvCons (eqEnvCons ee tyA eqB) tyC eqC))
      eqSources =
        compTmEq-subst
          (sigmaBranchTargetTy bσ cσ sigma M
           ∙ sym (subTyComp sigma (singleSubst (tmPair b c)) M))
          (sym (sigmaCompLiftTm bσ cσ sigma m))
          (sym (subTmComp tau (sigmaCompSub b c) m))
          branchEq
    in
    compTmEqElimLeft evalPair eqSources , tyResult
  fundTmEqEqEnv {sigma = sigma} {tau = tau}
    d@(iEqEq {A = A} {a = a} {b = b} daeq) (acc rec) ee =
    let
      accA = rec {y = mDeriv daeq} (mDeriv-summand< d ≤-refl)
      eqA , tyA = fundTmEqEqEnv daeq accA ee
      eqARight = proj₁ (fundTmEqEqEnv daeq accA (eqEnvReflRight ee))
      eqAAcross =
        compTmEq-trans
          {A = subTy sigma A} {t = subTm sigma a} {u = subTm tau b} {v = subTm tau a}
          eqA
          (compTmEq-conv
            {A = subTy tau A} {B = subTy sigma A}
            (compTyEq-sym {A = subTy sigma A} {B = subTy tau A} tyA)
            (compTmEq-sym {A = subTy tau A} eqARight))
      ctyA = proj₁ (compTyEq-sides {A = subTy sigma A} {B = subTy tau A} tyA)
      ca = proj₁ (compTmEq-sides {A = subTy sigma A} eqA)
    in
    computableTmEqEqForm-intro
      {A = subTy sigma A} {a = subTm sigma a} {b = subTm sigma a}
      {t = tmR} {u = tmR}
      evalR evalR (compTmEq-refl {A = subTy sigma A} ctyA ca) ,
    computableTyEqEqForm-intro
      {A = subTy sigma A} {C = subTy tau A}
      {a = subTm sigma a} {b = subTm sigma a}
      {c = subTm tau a} {d = subTm tau a}
      tyA eqAAcross eqAAcross
  fundTmEqEqEnv {sigma = sigma} {tau = tau}
    d@(eEqStar {A = A} {a = a} {b = b} {p = p} dp dA da db) (acc rec) ee =
    let
      dpEq , tyEqAB =
        fundTmEqEnv dp
          (rec {y = mDeriv dp}
            (mDeriv-summand< d (≤-sum1-4 (mDeriv dp) (mDeriv dA) (mDeriv da) (mDeriv db))))
          ee
      _ , _ , eqab =
        computableTmEqEqForm-elim
          {A = subTy sigma A}
          {a = subTm sigma a} {b = subTm sigma b}
          {t = subTm sigma p} {u = subTm tau p}
          dpEq
      eqb , tyA =
        fundTmEqEnv db
          (rec {y = mDeriv db}
            (mDeriv-summand< d (≤-sum4-4 (mDeriv dp) (mDeriv dA) (mDeriv da) (mDeriv db))))
          ee
    in
    compTmEq-trans
      {A = subTy sigma A} {t = subTm sigma a} {u = subTm sigma b} {v = subTm tau b}
      eqab eqb ,
    tyA
  fundTmEqEqEnv {sigma = sigma} {tau = tau}
    d@(cEq {A = A} {a = a} {b = b} {p = p} dp dA da db) (acc rec) ee =
    let
      dpEq , tyEqAB =
        fundTmEqEnv dp
          (rec {y = mDeriv dp}
            (mDeriv-summand< d (≤-sum1-4 (mDeriv dp) (mDeriv dA) (mDeriv da) (mDeriv db))))
          ee
      evp , eqab =
        computableEq-elim
          {A = subTy sigma A}
          {a = subTm sigma a} {b = subTm sigma b}
          {t = subTm sigma p}
          (proj₁
            (compTmEq-sides
              {A = tyEq (subTy sigma A) (subTm sigma a) (subTm sigma b)}
              dpEq))
      eqa , tyA =
        fundTmEqEnv da
          (rec {y = mDeriv da}
            (mDeriv-summand< d (≤-sum3-4 (mDeriv dp) (mDeriv dA) (mDeriv da) (mDeriv db))))
          ee
      eqb , tyA' =
        fundTmEqEnv db
          (rec {y = mDeriv db}
            (mDeriv-summand< d (≤-sum4-4 (mDeriv dp) (mDeriv dA) (mDeriv da) (mDeriv db))))
          ee
    in
    computableTmEqEqForm-intro
      {A = subTy sigma A} {a = subTm sigma a} {b = subTm sigma b}
      {t = subTm sigma p} {u = tmR}
      evp evalR eqab ,
    computableTyEqEqForm-intro
      {A = subTy sigma A} {C = subTy tau A}
      {a = subTm sigma a} {b = subTm sigma b}
      {c = subTm tau a} {d = subTm tau b}
      tyA eqa eqb
  fundTmEqEqEnv {sigma = sigma} {tau = tau} d@(iQtrEq {A = A} {a = a} {b = b} da db) (acc rec) ee =
    let
      eqa , tyA =
        fundTmEqEnv da (rec {y = mDeriv da} (mDeriv-summand< d ≤-sum-l)) ee
      ctyA = proj₁ (compTyEq-sides {A = subTy sigma A} {B = subTy tau A} tyA)
      ca = proj₁ (compTmEq-sides {A = subTy sigma A} eqa)
      eqb , tyA' =
        fundTmEqEnv db (rec {y = mDeriv db} (mDeriv-summand< d ≤-sum-r)) ee
      cb = proj₂ (compTmEq-sides {A = subTy sigma A} eqb)
    in
    computableTmEqQtr-intro
      {A = subTy sigma A}
      {t = tmClass (subTm sigma a)} {u = tmClass (subTm tau b)}
      {p = subTm sigma a} {q = subTm tau b}
      evalClass evalClass
      (compTmEq-refl {A = subTy sigma A} ctyA ca)
      (compTmEq-refl {A = subTy sigma A} ctyA cb) ,
    computableTyEqQtr-intro {A = subTy sigma A} {C = subTy tau A} tyA
  fundTmEqEqEnv {sigma = sigma} {tau = tau}
    d@(eQtrEq {A = A} {L = L} {l = l} {l' = l'} {p = p} {p' = p'} dL dpEq dBranch dl dl' dlEq coh coh') (acc rec) ee =
    let
      accL =
        rec {y = mDeriv dL}
          (mDeriv-summand< d
            (≤-sum1-8 (mDeriv dL) (mDeriv dpEq) (mDeriv dBranch) (mDeriv dl)
              (mDeriv dl') (mDeriv dlEq) (mDeriv coh) (mDeriv coh')))
      accp =
        rec {y = mDeriv dpEq}
          (mDeriv-summand< d
            (≤-sum2-8 (mDeriv dL) (mDeriv dpEq) (mDeriv dBranch) (mDeriv dl)
              (mDeriv dl') (mDeriv dlEq) (mDeriv coh) (mDeriv coh')))
      accDlEq =
        rec {y = mDeriv dlEq}
          (mDeriv-summand< d
            (≤-sum6-8 (mDeriv dL) (mDeriv dpEq) (mDeriv dBranch) (mDeriv dl)
              (mDeriv dl') (mDeriv dlEq) (mDeriv coh) (mDeriv coh')))
      accCoh' =
        rec {y = mDeriv coh'}
          (mDeriv-summand< d
            (≤-sum8-8 (mDeriv dL) (mDeriv dpEq) (mDeriv dBranch) (mDeriv dl)
              (mDeriv dl') (mDeriv dlEq) (mDeriv coh) (mDeriv coh')))
      dpMain , tyQtrEq = fundTmEqEqEnv dpEq accp ee
      dpRight = proj₁ (fundTmEqEqEnv dpEq accp (eqEnvReflRight ee))
      dpSelf =
        compTmEq-trans
          {A = tyQtr (subTy sigma A)}
          {t = subTm sigma p} {u = subTm tau p'} {v = subTm tau p}
          dpMain
          (compTmEq-conv
            {A = tyQtr (subTy tau A)} {B = tyQtr (subTy sigma A)}
            (compTyEq-sym
              {A = tyQtr (subTy sigma A)} {B = tyQtr (subTy tau A)}
              tyQtrEq)
            (compTmEq-sym {A = tyQtr (subTy tau A)} dpRight))
      cQtr =
        proj₁
          (compTyEq-sides
            {A = tyQtr (subTy sigma A)} {B = tyQtr (subTy tau A)}
            tyQtrEq)
      tyQ = computableTyEqQtr-elim {A = subTy sigma A} {C = subTy tau A} tyQtrEq
      cQ = proj₁ (compTyEq-sides {A = subTy sigma A} {B = subTy tau A} tyQ)
      a , b , evp , evp' , caa , cbb =
        computableTmEqQtr-elim
          {A = subTy sigma A} {t = subTm sigma p} {u = subTm tau p'}
          dpMain
      ca = proj₁ (compTmEq-sides {A = subTy sigma A} caa)
      eqAA = compTmEq-refl {A = subTy sigma A} cQ ca
      eqPClass =
        computableTmEqQtr-intro
          {A = subTy sigma A}
          {t = subTm sigma p} {u = tmClass a}
          {p = a} {q = a}
          evp evalClass eqAA eqAA
      tyPClassRaw =
        fundTyEqEnv dL accL
          (eqEnvCons
            (eqEnvReflLeft ee)
            (compTyEq-refl {A = tyQtr (subTy sigma A)} cQtr)
            eqPClass)
      tyPClass =
        compTyEq-subst
          (sym (subTyComp sigma (singleSubst p) L))
          refl
          tyPClassRaw
      tyResult =
        compTyEq-subst
          (sym (subTyComp sigma (singleSubst p) L))
          (sym (subTyComp tau (singleSubst p) L))
          (fundTyEqEnv dL accL (eqEnvCons ee tyQtrEq dpSelf))
      eeLeft =
        eqEnvReflLeft ee
      branchLeft =
        proj₁
          (fundTmEqEqEnv dlEq accDlEq
            (eqEnvCons eeLeft (compTyEq-refl {A = subTy sigma A} cQ) caa))
      branchLeftSource =
        compTmEq-subst
          (qtrBranchTargetTy a sigma L)
          (sym (qtrCompLiftTm a sigma l))
          (sym (qtrCompLiftTm a sigma l'))
          branchLeft
      tyHead =
        compTyEq-subst
          (sym (lookupHereTy sigma a A))
          (sym (lookupHereTy tau a A))
          tyQ
      headEq =
        compTmEq-subst
          (sym (lookupHereTy sigma a A))
          refl refl
          cbb
      branchCoh =
        proj₁ (fundTmEqEqEnv coh' accCoh'
          (eqEnvCons
            (eqEnvCons ee tyQ caa)
            tyHead
            headEq))
      branchCohSource =
        compTmEq-subst
          (qtrCohTargetTy a b sigma L)
          (qtrCohLeftTm a b sigma l' ∙ sym (qtrCompLiftTm a sigma l'))
          (qtrCohRightTm a b tau l' ∙ sym (qtrCompLiftTm b tau l'))
          branchCoh
      eqSources =
        compTmEq-trans
          {A = subTy (consSubst (tmClass a) sigma) L}
          {t = subTm (qtrCompSub a) (subTm (liftSubst sigma) l)}
          {u = subTm (qtrCompSub a) (subTm (liftSubst sigma) l')}
          {v = subTm (qtrCompSub b) (subTm (liftSubst tau) l')}
          branchLeftSource branchCohSource
    in
    compTmEq-conv
      {A = subTy (consSubst (tmClass a) sigma) L}
      {B = subTy sigma (subTy (singleSubst p) L)}
      (compTyEq-sym
        {A = subTy sigma (subTy (singleSubst p) L)}
        {B = subTy (consSubst (tmClass a) sigma) L}
        tyPClass)
      (compTmEqQtrElimRight evp' (compTmEqQtrElimLeft evp eqSources)) ,
    tyResult
  fundTmEqEqEnv {sigma = sigma} {tau = tau}
    d@(cQtr {A = A} {L = L} {a = a} {l = l} dL da dBranch dl coh) (acc rec) ee =
    let
      aσ = subTm sigma a
      aτ = subTm tau a
      accL =
        rec {y = mDeriv dL}
          (mDeriv-summand< d
            (≤-sum1-5 (mDeriv dL) (mDeriv da) (mDeriv dBranch) (mDeriv dl) (mDeriv coh)))
      acca =
        rec {y = mDeriv da}
          (mDeriv-summand< d
            (≤-sum2-5 (mDeriv dL) (mDeriv da) (mDeriv dBranch) (mDeriv dl) (mDeriv coh)))
      accl =
        rec {y = mDeriv dl}
          (mDeriv-summand< d
            (≤-sum4-5 (mDeriv dL) (mDeriv da) (mDeriv dBranch) (mDeriv dl) (mDeriv coh)))
      eqA , tyA = fundTmEqEnv da acca ee
      cA = proj₁ (compTyEq-sides {A = subTy sigma A} {B = subTy tau A} tyA)
      caσ = proj₁ (compTmEq-sides {A = subTy sigma A} eqA)
      caτ = proj₂ (compTmEq-sides {A = subTy sigma A} eqA)
      tyQtrEq = computableTyEqQtr-intro {A = subTy sigma A} {C = subTy tau A} tyA
      classEq =
        computableTmEqQtr-intro
          {A = subTy sigma A}
          {t = tmClass aσ} {u = tmClass aτ}
          {p = aσ} {q = aτ}
          evalClass evalClass
          (compTmEq-refl {A = subTy sigma A} cA caσ)
          (compTmEq-refl {A = subTy sigma A} cA caτ)
      tyResult =
        compTyEq-subst
          (sym (subTyComp sigma (singleSubst (tmClass a)) L))
          (sym (subTyComp tau (singleSubst (tmClass a)) L))
          (fundTyEqEnv dL accL (eqEnvCons ee tyQtrEq classEq))
      branchEq =
        proj₁ (fundTmEqEnv dl accl (eqEnvCons ee tyA eqA))
      eqSources =
        compTmEq-subst
          (qtrBranchTargetTy aσ sigma L
           ∙ sym (subTyComp sigma (singleSubst (tmClass a)) L))
          (sym (qtrCompLiftTm aσ sigma l))
          (sym (subTmComp tau (qtrCompSub a) l))
          branchEq
    in
    compTmEqQtrElimLeft evalClass eqSources , tyResult

  fundFitsSameEq : {gamma delta : Ctx} {theta sigma tau : Subst}
    -> (fits : FitsSubst gamma delta theta) -> Acc _<_ (mFits fits) -> EqEnv gamma sigma tau
    -> EqEnv delta (compSub sigma theta) (compSub tau theta)
  fundFitsSameEq (fitsNil wf) _ ee = eqEnvNil
  fundFitsSameEq {sigma = sigma} {tau = tau}
    fs@(fitsCons {sigma = theta} {A = A} fits dt) (acc rec) ee =
    let
      eeΔ =
        fundFitsSameEq fits
          (rec {y = mFits fits} (mFits-fitsCons-fits< fits dt))
          ee
      tm , ty =
        fundTmEqEnv dt
          (rec {y = mDeriv dt} (mFits-fitsCons-deriv< fits dt))
          ee
    in
    eqEnvCons eeΔ
      (compTyEq-subst
        (subTyComp sigma theta A)
        (subTyComp tau theta A)
        ty)
      (compTmEq-subst
        (subTyComp sigma theta A)
        refl refl
        tm)

  fundFitsEqLeftEnv : {gamma delta : Ctx} {theta eta sigma tau : Subst}
    -> (fitsEq : FitsEqSubst gamma delta theta eta) -> Acc _<_ (mFitsEq fitsEq)
    -> EqEnv gamma sigma tau
    -> EqEnv delta (compSub sigma theta) (compSub tau theta)
  fundFitsEqLeftEnv (fitsEqNil wf) _ ee = eqEnvNil
  fundFitsEqLeftEnv {sigma = sigma} {tau = tau}
    fs@(fitsEqCons {sigma = theta} {tau = eta} {A = A} {t = t} {u = u} fitsEq dtu) (acc rec) ee =
    let
      eeΔ =
        fundFitsEqLeftEnv fitsEq
          (rec {y = mFitsEq fitsEq} (mFitsEq-fitsEqCons-fitsEq< fitsEq dtu))
          ee
      accDtu = rec {y = mDeriv dtu} (mFitsEq-fitsEqCons-deriv< fitsEq dtu)
      tm , ty = fundTmEqEqEnv dtu accDtu ee
      tmRight = proj₁ (fundTmEqEqEnv dtu accDtu (eqEnvReflRight ee))
      tmSelf =
        compTmEq-trans
          {A = subTy sigma (subTy theta A)}
          {t = subTm sigma t} {u = subTm tau u} {v = subTm tau t}
          tm
          (compTmEq-conv
            {A = subTy tau (subTy theta A)}
            {B = subTy sigma (subTy theta A)}
            (compTyEq-sym
              {A = subTy sigma (subTy theta A)}
              {B = subTy tau (subTy theta A)}
              ty)
            (compTmEq-sym {A = subTy tau (subTy theta A)} tmRight))
    in
    eqEnvCons eeΔ
      (compTyEq-subst
        (subTyComp sigma theta A)
        (subTyComp tau theta A)
        ty)
      (compTmEq-subst
        (subTyComp sigma theta A)
        refl refl
        tmSelf)

  fundFitsEqEnv : {gamma delta : Ctx} {theta eta sigma tau : Subst}
    -> (fitsEq : FitsEqSubst gamma delta theta eta) -> (wfΔ : CtxWF delta)
    -> Acc _<_ (mFitsEq fitsEq + mCtxWF wfΔ) -> EqEnv gamma sigma tau
    -> EqEnv delta (compSub sigma theta) (compSub tau eta)
  fundFitsEqEnv (fitsEqNil wf) wfΔ _ ee = eqEnvNil
  fundFitsEqEnv {sigma = sigma} {tau = tau}
    fs@(fitsEqCons {sigma = theta} {tau = eta} {A = A} fitsEq dtu)
    (wfCons wfΔ dA) (acc rec) ee =
    let
      eeΔ =
        fundFitsEqEnv fitsEq wfΔ
          (rec {y = mFitsEq fitsEq + mCtxWF wfΔ}
            (fitsEqCtx-tail< fitsEq dtu wfΔ dA))
          ee
      tm , ty =
        fundTmEqEqEnv dtu
          (rec {y = mDeriv dtu}
            (≤-trans (mFitsEq-fitsEqCons-deriv< fitsEq dtu) ≤-sum-l))
          ee
    in
    eqEnvCons eeΔ
      (fundTyEqEnv dA
        (rec {y = mDeriv dA} (fitsEqCtx-headDeriv< fitsEq dtu wfΔ dA))
        eeΔ)
      (compTmEq-subst
        (subTyComp sigma theta A)
        refl refl
        tm)

fundTyEq : {gamma : Ctx} {A B : RawType} {sigma tau : Subst}
  -> Derivable (typeEq gamma A B) -> EqEnv gamma sigma tau
  -> ComputableTyEq (subTy sigma A) (subTy tau B)
fundTyEq d ee = fundTyEqEqEnv d (<-wellFounded (mDeriv d)) ee

fundTmTyEnv : {gamma : Ctx} {t : RawTerm} {A : RawType} {sigma tau : Subst}
  -> Derivable (hasTy gamma t A) -> EqEnv gamma sigma tau
  -> ComputableTyEq (subTy sigma A) (subTy tau A)
fundTmTyEnv d ee = proj₂ (fundTmEqEnv d (<-wellFounded (mDeriv d)) ee)

fundTmEq : {gamma : Ctx} {t u : RawTerm} {A : RawType} {sigma tau : Subst}
  -> Derivable (termEq gamma t u A) -> EqEnv gamma sigma tau
  -> ComputableTmEq (subTy sigma A) (subTm sigma t) (subTm tau u)
fundTmEq d ee = proj₁ (fundTmEqEqEnv d (<-wellFounded (mDeriv d)) ee)

fundFitsEq : {gamma delta : Ctx} {theta eta sigma tau : Subst}
  -> FitsEqSubst gamma delta theta eta -> CtxWF delta -> EqEnv gamma sigma tau
  -> EqEnv delta (compSub sigma theta) (compSub tau eta)
fundFitsEq fitsEq wfΔ ee =
  fundFitsEqEnv fitsEq wfΔ (<-wellFounded (mFitsEq fitsEq + mCtxWF wfΔ)) ee

fundTyClosed : {A : RawType}
  -> Derivable (isType [] A) -> ComputableTy A
fundTyClosed {A = A} d =
  compTy-subst {A = subTy idSubst A} {B = A} (subTyId A)
    (proj₁
      (compTyEq-sides
        {A = subTy idSubst A} {B = subTy idSubst A}
        (fundTyEqEnv d (<-wellFounded (mDeriv d)) eqEnvNil)))

fundTmClosed : {t : RawTerm} {A : RawType}
  -> Derivable (hasTy [] t A) -> Computable A t
fundTmClosed {t = t} {A = A} d =
  compTm-subst
    {A = subTy idSubst A} {B = A}
    {t = subTm idSubst t} {u = t}
    (subTyId A) (subTmId t)
    (proj₁
      (compTmEq-sides
        {A = subTy idSubst A}
        {t = subTm idSubst t} {u = subTm idSubst t}
        (proj₁ (fundTmEqEnv d (<-wellFounded (mDeriv d)) eqEnvNil))))

fundTyEqClosed : {A B : RawType}
  -> Derivable (typeEq [] A B) -> ComputableTyEq A B
fundTyEqClosed {A = A} {B = B} d =
  compTyEq-subst
    {A = subTy idSubst A} {A' = A}
    {B = subTy idSubst B} {B' = B}
    (subTyId A) (subTyId B)
    (fundTyEqEqEnv d (<-wellFounded (mDeriv d)) eqEnvNil)

fundTmEqClosed : {t u : RawTerm} {A : RawType}
  -> Derivable (termEq [] t u A) -> ComputableTmEq A t u
fundTmEqClosed {t = t} {u = u} {A = A} d =
  compTmEq-subst
    {A = subTy idSubst A} {B = A}
    {t = subTm idSubst t} {t' = t}
    {u = subTm idSubst u} {u' = u}
    (subTyId A) (subTmId t) (subTmId u)
    (proj₁ (fundTmEqEqEnv d (<-wellFounded (mDeriv d)) eqEnvNil))
