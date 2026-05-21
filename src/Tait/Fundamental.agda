{-# OPTIONS --safe #-}

module Tait.Fundamental where

open import Tait.Prelude
open import Data.List.Base using ([] ; _∷_ ; _++_ ; length)
open import Data.Nat using (ℕ ; zero ; suc ; _<_)
open import Data.Nat.Induction using () renaming (<-wellFounded to <-wf)
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
    -> ComputableTmEq (subTy sigma A) a b
    -> EqEnv (A ∷ gamma) (consSubst a sigma) (consSubst b tau)

eqEnvLeft : {gamma : Ctx} {sigma tau : Subst}
  -> EqEnv gamma sigma tau -> Env gamma sigma
eqEnvLeft eqEnvNil = envNil
eqEnvLeft (eqEnvCons ee eq) =
  envCons (eqEnvLeft ee) (proj₁ (compTmEq-sides eq))

eqEnvRight : {gamma : Ctx} {sigma tau : Subst}
  -> EqEnv gamma sigma tau -> Env gamma tau
eqEnvRight eqEnvNil = envNil
eqEnvRight (eqEnvCons {A = A} {sigma = sigma} {tau = tau} ee eq) =
  envCons (eqEnvRight ee)
    (compTm-subst (subTyConst sigma tau A) refl (proj₂ (compTmEq-sides eq)))

envReflEq : {gamma : Ctx} {sigma : Subst}
  -> Env gamma sigma -> EqEnv gamma sigma sigma
envReflEq envNil = eqEnvNil
envReflEq (envCons rho ca) =
  eqEnvCons (envReflEq rho) (compTmEq-refl ca)

eqEnvDrop : {gamma delta : Ctx} {sigma tau : Subst}
  -> EqEnv (delta ++ gamma) sigma tau
  -> EqEnv gamma (dropSub (length delta) sigma) (dropSub (length delta) tau)
eqEnvDrop {delta = []} ee = ee
eqEnvDrop {delta = A ∷ delta} (eqEnvCons ee eq) = eqEnvDrop {delta = delta} ee

eqEnvLookup : {gamma delta : Ctx} {A : RawType} {sigma tau : Subst}
  -> EqEnv (delta ++ (A ∷ gamma)) sigma tau
  -> ComputableTmEq (subTy sigma (wkTyBy (suc (length delta)) A))
       (applySubst sigma (length delta)) (applySubst tau (length delta))
eqEnvLookup {delta = []} {A = A} (eqEnvCons {sigma = sigma} {a = a} ee eq) =
  compTmEq-subst (sym (lookupHereTy sigma a A)) refl refl eq
eqEnvLookup {delta = D ∷ delta} {A = A}
  (eqEnvCons {sigma = sigma} {a = a} ee eq) =
  compTmEq-subst
    (sym (lookupWkCancel sigma a (suc (length delta)) A))
    refl refl
    (eqEnvLookup {delta = delta} ee)

singleLiftTy : (a : RawTerm) (sigma : Subst) (B : RawType)
  -> subTy (consSubst a sigma) B
       ≡ subTy (singleSubst a) (subTy (liftSubst sigma) B)
singleLiftTy a sigma B =
  subTyConst (consSubst a sigma) (compSub (singleSubst a) (liftSubst sigma)) B
  ∙ sym (subTyComp (singleSubst a) (liftSubst sigma) B)

sigmaBranchTargetTy : (b c : RawTerm) (sigma : Subst) (d : RawTerm) (M : RawType)
  -> subTy (consSubst c (consSubst b sigma)) (sigmaBranchTy M)
       ≡ subTy sigma (subTy (singleSubst d) M)
sigmaBranchTargetTy b c sigma d M =
  subTyComp (consSubst c (consSubst b sigma)) sigmaMotSub M
  ∙ subTyConst
      (compSub (consSubst c (consSubst b sigma)) sigmaMotSub)
      (compSub sigma (singleSubst d)) M
  ∙ sym (subTyComp sigma (singleSubst d) M)

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

computableResult : {A : RawType} {t : RawTerm}
  -> Computable A t -> Σ[ g ∈ RawTerm ] (t =>e g) × Computable A g
computableResult {A = tyTop} ct = tmStar , ct , evalStar
computableResult {A = tySigma A B} ct =
  let a , b , ev , ca , cb = computableSigma-elim ct in
  tmPair a b , ev , computableSigma-intro (a , b , evalPair , ca , cb)

computableTySigma-introAcc : {A B : RawType}
  -> (p : Acc _<_ (tyDepth (tySigma A B)))
  -> ComputableTy A
  -> ((a : RawTerm) -> Computable A a -> ComputableTy (subTy (singleSubst a) B))
  -> ComputableTyAcc (tySigma A B) p
computableTySigma-introAcc {A} {B} (acc rs) cA fam =
  ComputableTyAcc-cast A
    (<-wf (tyDepth A)) (rs (tyDepth-fst<Sigma A B)) cA ,
  λ a ca ->
    ComputableTyAcc-cast (subTy (singleSubst a) B)
      (<-wf (tyDepth (subTy (singleSubst a) B))) (rs (subTy-snd< A B a))
      (fam a ca)

computableTySigma-intro : {A B : RawType}
  -> ComputableTy A
  -> ((a : RawTerm) -> Computable A a -> ComputableTy (subTy (singleSubst a) B))
  -> ComputableTy (tySigma A B)
computableTySigma-intro {A} {B} =
  computableTySigma-introAcc (<-wf (tyDepth (tySigma A B)))

computableTyEqSigma-introAcc : {A B C D : RawType}
  -> (p : Acc _<_ (tyDepth (tySigma A B)))
  -> (q : Acc _<_ (tyDepth (tySigma C D)))
  -> ComputableTyEq A C
  -> ((a : RawTerm) -> Computable A a
        -> ComputableTyEq (subTy (singleSubst a) B) (subTy (singleSubst a) D))
  -> ComputableTyEqAcc (tySigma A B) (tySigma C D) p q
computableTyEqSigma-introAcc {A} {B} {C} {D} (acc rsAB) (acc rsCD) eqAC fam =
  ComputableTyEqAcc-cast A C
    (<-wf (tyDepth A)) (rsAB (tyDepth-fst<Sigma A B))
    (<-wf (tyDepth C)) (rsCD (tyDepth-fst<Sigma C D))
    eqAC ,
  λ a ca ->
    ComputableTyEqAcc-cast (subTy (singleSubst a) B) (subTy (singleSubst a) D)
      (<-wf (tyDepth (subTy (singleSubst a) B))) (rsAB (subTy-snd< A B a))
      (<-wf (tyDepth (subTy (singleSubst a) D))) (rsCD (subTy-snd< C D a))
      (fam a ca)

computableTyEqSigma-intro : {A B C D : RawType}
  -> ComputableTyEq A C
  -> ((a : RawTerm) -> Computable A a
        -> ComputableTyEq (subTy (singleSubst a) B) (subTy (singleSubst a) D))
  -> ComputableTyEq (tySigma A B) (tySigma C D)
computableTyEqSigma-intro {A} {B} {C} {D} =
  computableTyEqSigma-introAcc
    (<-wf (tyDepth (tySigma A B))) (<-wf (tyDepth (tySigma C D)))

computableTmEqSigma-introAcc : {A B : RawType} {a b c d : RawTerm}
  -> (p : Acc _<_ (tyDepth (tySigma A B)))
  -> ComputableTmEq A a c
  -> ComputableTmEq (subTy (singleSubst a) B) b d
  -> ComputableTmEqAcc (tySigma A B) p (tmPair a b) (tmPair c d)
computableTmEqSigma-introAcc {A} {B} {a} {b} {c} {d} (acc rs) eqA eqB =
  a , b , c , d , evalPair , evalPair ,
  ComputableTmEqAcc-cast A
    (<-wf (tyDepth A)) (rs (tyDepth-fst<Sigma A B)) a c eqA ,
  ComputableTmEqAcc-cast (subTy (singleSubst a) B)
    (<-wf (tyDepth (subTy (singleSubst a) B))) (rs (subTy-snd< A B a)) b d eqB

computableTmEqSigma-intro : {A B : RawType} {a b c d : RawTerm}
  -> ComputableTmEq A a c
  -> ComputableTmEq (subTy (singleSubst a) B) b d
  -> ComputableTmEq (tySigma A B) (tmPair a b) (tmPair c d)
computableTmEqSigma-intro {A} {B} =
  computableTmEqSigma-introAcc (<-wf (tyDepth (tySigma A B)))

SigmaComputableTmEq : RawType -> RawType -> RawTerm -> RawTerm -> Type
SigmaComputableTmEq A B t u =
  Σ[ a ∈ RawTerm ] Σ[ b ∈ RawTerm ] Σ[ c ∈ RawTerm ] Σ[ d ∈ RawTerm ]
      (t =>e tmPair a b)
    × (u =>e tmPair c d)
    × ComputableTmEq A a c
    × ComputableTmEq (subTy (singleSubst a) B) b d

computableTmEqSigma-elimAcc : (A B : RawType)
  -> (p : Acc _<_ (tyDepth (tySigma A B))) (t u : RawTerm)
  -> ComputableTmEqAcc (tySigma A B) p t u
  -> SigmaComputableTmEq A B t u
computableTmEqSigma-elimAcc A B (acc rs) t u
  (a , b , c , d , evt , evu , eqA , eqB) =
  a , b , c , d , evt , evu ,
  ComputableTmEqAcc-cast A
    (rs (tyDepth-fst<Sigma A B)) (<-wf (tyDepth A)) a c eqA ,
  ComputableTmEqAcc-cast (subTy (singleSubst a) B)
    (rs (subTy-snd< A B a)) (<-wf (tyDepth (subTy (singleSubst a) B))) b d eqB

computableTmEqSigma-elim : {A B : RawType} {t u : RawTerm}
  -> ComputableTmEq (tySigma A B) t u
  -> SigmaComputableTmEq A B t u
computableTmEqSigma-elim {A} {B} {t} {u} =
  computableTmEqSigma-elimAcc A B (<-wf (tyDepth (tySigma A B))) t u

compTmEqElimLeft : {A : RawType} {d m u b c : RawTerm}
  -> d =>e tmPair b c
  -> ComputableTmEq A (subTm (sigmaCompSub b c) m) u
  -> ComputableTmEq A (tmElSigma d m) u
compTmEqElimLeft {A = tyTop} evd (evm , evu) =
  evalElSigma evd evm , evu
compTmEqElimLeft {A = tySigma A B} evd eq =
  let a , b , c , d , evm , evu , eqA , eqB = eq in
  a , b , c , d , evalElSigma evd evm , evu , eqA , eqB

compTmEqElimRight : {A : RawType} {t d m b c : RawTerm}
  -> d =>e tmPair b c
  -> ComputableTmEq A t (subTm (sigmaCompSub b c) m)
  -> ComputableTmEq A t (tmElSigma d m)
compTmEqElimRight {A = tyTop} evd (evt , evm) =
  evt , evalElSigma evd evm
compTmEqElimRight {A = tySigma A B} evd eq =
  let a , b , c , d , evt , evm , eqA , eqB = eq in
  a , b , c , d , evt , evalElSigma evd evm , eqA , eqB

mutual
  fundTy : {gamma : Ctx} {A : RawType} {sigma : Subst}
    -> Derivable (isType gamma A) -> Env gamma sigma -> ComputableTy (subTy sigma A)
  fundTy {sigma = sigma} (weakenTy {delta = delta} {A = A} d wf) rho =
    compTy-subst
      (sym (subTyRen sigma (addRen (length delta)) A))
      (fundTy d (envDrop {delta = delta} rho))
  fundTy {sigma = sigma} (substTyRule {sigma = tau} {A = A} d fits) rho =
    compTy-subst
      (sym (subTyComp sigma tau A))
      (fundTy d (fundFits fits rho))
  fundTy (fTop wf) rho = tt
  fundTy {sigma = sigma} (fSigma {A = A} {B = B} dA dB) rho =
    computableTySigma-intro (fundTy dA rho)
    λ a ca ->
      compTy-subst (singleLiftTy a sigma B)
        (fundTy dB (envCons rho ca))

  fundTm : {gamma : Ctx} {t : RawTerm} {A : RawType} {sigma : Subst}
    -> Derivable (hasTy gamma t A) -> Env gamma sigma
    -> Computable (subTy sigma A) (subTm sigma t)
  fundTm (varStar wf dA) rho = envLookup rho
  fundTm {sigma = sigma} (weakenTm {delta = delta} {t = t} {A = A} d wf) rho =
    compTm-subst
      (sym (subTyRen sigma (addRen (length delta)) A))
      (sym (subTmRen sigma (addRen (length delta)) t))
      (fundTm d (envDrop {delta = delta} rho))
  fundTm {sigma = sigma} (conv d dAB) rho =
    compTm-conv (fundTyEqEqEnv dAB (envReflEq rho)) (fundTm d rho)
  fundTm {sigma = sigma} (substTmRule {sigma = tau} {t = t} {A = A} d fits) rho =
    compTm-subst
      (sym (subTyComp sigma tau A))
      (sym (subTmComp sigma tau t))
      (fundTm d (fundFits fits rho))
  fundTm (iTop wf) rho = evalStar
  fundTm {sigma = sigma} (iSigma {a = a} {b = b} {B = B} da db dSig) rho =
    let
      ca = fundTm da rho
      cb =
        compTm-subst
          (subTyComp sigma (singleSubst a) B
           ∙ singleLiftTy (subTm sigma a) sigma B)
          refl
          (fundTm db rho)
    in
    computableSigma-intro (subTm sigma a , subTm sigma b , evalPair , ca , cb)
  fundTm {sigma = sigma} (eSigma {B = B} {M = M} {d = d} {m = m} dM dd dm) rho =
    let
      b , c , evd , cb , ccRaw = computableSigma-elim (fundTm dd rho)
      cc =
        compTm-subst (sym (singleLiftTy b sigma B)) refl ccRaw
      cm =
        fundTm dm (envCons (envCons rho cb) cc)
      cmSource =
        compTm-subst
          (sigmaBranchTargetTy b c sigma d M)
          (sym (sigmaCompLiftTm b c sigma m))
          cm
      g , evm , cg = computableResult cmSource
    in
    compTm-=>e-back (evalElSigma evd evm) cg

  fundFits : {gamma delta : Ctx} {tau sigma : Subst}
    -> FitsSubst gamma delta tau -> Env gamma sigma -> Env delta (compSub sigma tau)
  fundFits (fitsNil wf) rho = envNil
  fundFits {sigma = sigma} (fitsCons {sigma = tau} {A = A} fits dt) rho =
    envCons (fundFits fits rho)
      (compTm-subst (subTyComp sigma tau A) refl (fundTm dt rho))

  fundTyEqEnv : {gamma : Ctx} {A : RawType} {sigma tau : Subst}
    -> Derivable (isType gamma A) -> EqEnv gamma sigma tau
    -> ComputableTyEq (subTy sigma A) (subTy tau A)
  fundTyEqEnv {sigma = sigma} {tau = tau}
    (weakenTy {delta = delta} {A = A} d wf) ee =
    compTyEq-subst
      (sym (subTyRen sigma (addRen (length delta)) A))
      (sym (subTyRen tau (addRen (length delta)) A))
      (fundTyEqEnv d (eqEnvDrop {delta = delta} ee))
  fundTyEqEnv {sigma = sigma} {tau = tau}
    (substTyRule {sigma = theta} {A = A} d fits) ee =
    compTyEq-subst
      (sym (subTyComp sigma theta A))
      (sym (subTyComp tau theta A))
      (fundTyEqEnv d (fundFitsSameEq fits ee))
  fundTyEqEnv (fTop wf) ee = tt
  fundTyEqEnv {sigma = sigma} {tau = tau} (fSigma {B = B} dA dB) ee =
    computableTyEqSigma-intro (fundTyEqEnv dA ee)
    λ a ca ->
      compTyEq-subst
        (singleLiftTy a sigma B)
        (singleLiftTy a tau B)
        (fundTyEqEnv dB (eqEnvCons ee (compTmEq-refl ca)))

  fundTyEqEqEnv : {gamma : Ctx} {A B : RawType} {sigma tau : Subst}
    -> Derivable (typeEq gamma A B) -> EqEnv gamma sigma tau
    -> ComputableTyEq (subTy sigma A) (subTy tau B)
  fundTyEqEqEnv {sigma = sigma} {tau = tau}
    (weakenTyEq {delta = delta} {A = A} {B = B} d wf) ee =
    compTyEq-subst
      (sym (subTyRen sigma (addRen (length delta)) A))
      (sym (subTyRen tau (addRen (length delta)) B))
      (fundTyEqEqEnv d (eqEnvDrop {delta = delta} ee))
  fundTyEqEqEnv (reflTy d) ee = fundTyEqEnv d ee
  fundTyEqEqEnv {A = A} (symTy d dB) ee =
    compTyEq-trans
      (fundTyEqEnv dB ee)
      (compTyEq-sym (fundTyEqEqEnv d (envReflEq (eqEnvRight ee))))
  fundTyEqEqEnv (transTy dAB dBC) ee =
    compTyEq-trans
      (fundTyEqEqEnv dAB ee)
      (fundTyEqEqEnv dBC (envReflEq (eqEnvRight ee)))
  fundTyEqEqEnv {sigma = sigma} {tau = tau}
    (substTyEqRule {sigma = theta} {A = A} {B = B} d fits) ee =
    compTyEq-subst
      (sym (subTyComp sigma theta A))
      (sym (subTyComp tau theta B))
      (fundTyEqEqEnv d (fundFitsSameEq fits ee))
  fundTyEqEqEnv {sigma = sigma} {tau = tau}
    (eqSubTyRule {sigma = theta} {tau = eta} {A = A} d fitsEq) ee =
    compTyEq-subst
      (sym (subTyComp sigma theta A))
      (sym (subTyComp tau eta A))
      (fundTyEqEnv d (fundFitsEqEnv fitsEq ee))
  fundTyEqEqEnv {sigma = sigma} {tau = tau}
    (eqSubTyEqRule {sigma = theta} {tau = eta} {A = A} {B = B} d fitsEq) ee =
    compTyEq-subst
      (sym (subTyComp sigma theta A))
      (sym (subTyComp tau eta B))
      (fundTyEqEqEnv d (fundFitsEqEnv fitsEq ee))
  fundTyEqEqEnv {sigma = sigma} {tau = tau}
    (fSigmaEq {B = B} {D = D} dAC dB dBD) ee =
    computableTyEqSigma-intro (fundTyEqEqEnv dAC ee)
    λ a ca ->
      compTyEq-subst
        (singleLiftTy a sigma B)
        (singleLiftTy a tau D)
        (fundTyEqEqEnv dBD (eqEnvCons ee (compTmEq-refl ca)))

  fundTmEqEnv : {gamma : Ctx} {t : RawTerm} {A : RawType} {sigma tau : Subst}
    -> Derivable (hasTy gamma t A) -> EqEnv gamma sigma tau
    -> ComputableTmEq (subTy sigma A) (subTm sigma t) (subTm tau t)
  fundTmEqEnv (varStar wf dA) ee = eqEnvLookup ee
  fundTmEqEnv {sigma = sigma} {tau = tau}
    (weakenTm {delta = delta} {t = t} {A = A} d wf) ee =
    compTmEq-subst
      (sym (subTyRen sigma (addRen (length delta)) A))
      (sym (subTmRen sigma (addRen (length delta)) t))
      (sym (subTmRen tau (addRen (length delta)) t))
      (fundTmEqEnv d (eqEnvDrop {delta = delta} ee))
  fundTmEqEnv (conv d dAB) ee =
    compTmEq-conv
      (fundTyEqEqEnv dAB (envReflEq (eqEnvLeft ee)))
      (fundTmEqEnv d ee)
  fundTmEqEnv {sigma = sigma} {tau = tau}
    (substTmRule {sigma = theta} {t = t} {A = A} d fits) ee =
    compTmEq-subst
      (sym (subTyComp sigma theta A))
      (sym (subTmComp sigma theta t))
      (sym (subTmComp tau theta t))
      (fundTmEqEnv d (fundFitsSameEq fits ee))
  fundTmEqEnv (iTop wf) ee = evalStar , evalStar
  fundTmEqEnv {sigma = sigma}
    (iSigma {a = a} {b = b} {B = B} da db dSig) ee =
    let
      caeq = fundTmEqEnv da ee
      cbeq =
        compTmEq-subst
          (subTyComp sigma (singleSubst a) B
           ∙ singleLiftTy (subTm sigma a) sigma B)
          refl refl
          (fundTmEqEnv db ee)
    in
    computableTmEqSigma-intro caeq cbeq
  fundTmEqEnv {sigma = sigma} {tau = tau}
    (eSigma {B = B} {M = M} {d = d} {m = m} dM dd dm) ee =
    let
      b , c , e , f , evd , eve , eqB , eqCraw =
        computableTmEqSigma-elim (fundTmEqEnv dd ee)
      eqC =
        compTmEq-subst (sym (singleLiftTy b sigma B)) refl refl eqCraw
      branchEq =
        fundTmEqEnv dm (eqEnvCons (eqEnvCons ee eqB) eqC)
      eqSources =
        compTmEq-subst
          (sigmaBranchTargetTy b c sigma d M)
          (sym (sigmaCompLiftTm b c sigma m))
          (sym (sigmaCompLiftTm e f tau m))
          branchEq
    in
    compTmEqElimRight eve (compTmEqElimLeft evd eqSources)

  fundTmEqEqEnv : {gamma : Ctx} {t u : RawTerm} {A : RawType} {sigma tau : Subst}
    -> Derivable (termEq gamma t u A) -> EqEnv gamma sigma tau
    -> ComputableTmEq (subTy sigma A) (subTm sigma t) (subTm tau u)
  fundTmEqEqEnv {sigma = sigma} {tau = tau}
    (weakenTmEq {delta = delta} {t = t} {u = u} {A = A} d wf) ee =
    compTmEq-subst
      (sym (subTyRen sigma (addRen (length delta)) A))
      (sym (subTmRen sigma (addRen (length delta)) t))
      (sym (subTmRen tau (addRen (length delta)) u))
      (fundTmEqEqEnv d (eqEnvDrop {delta = delta} ee))
  fundTmEqEqEnv (reflTm d) ee = fundTmEqEnv d ee
  fundTmEqEqEnv {A = A} {sigma = sigma} {tau = tau} (symTm d du dA) ee =
    compTmEq-trans
      (fundTmEqEnv du ee)
      (compTmEq-sym
        (compTmEq-subst
          (subTyConst tau sigma A)
          refl refl
          (fundTmEqEqEnv d (envReflEq (eqEnvRight ee)))))
  fundTmEqEqEnv {A = A} {sigma = sigma} {tau = tau} (transTm dtu duv) ee =
    compTmEq-trans
      (fundTmEqEqEnv dtu ee)
      (compTmEq-subst
        (subTyConst tau sigma A)
        refl refl
        (fundTmEqEqEnv duv (envReflEq (eqEnvRight ee))))
  fundTmEqEqEnv (convEq d dAB) ee =
    compTmEq-conv
      (fundTyEqEqEnv dAB (envReflEq (eqEnvLeft ee)))
      (fundTmEqEqEnv d ee)
  fundTmEqEqEnv {sigma = sigma} {tau = tau}
    (substTmEqRule {sigma = theta} {t = t} {u = u} {A = A} d fits) ee =
    compTmEq-subst
      (sym (subTyComp sigma theta A))
      (sym (subTmComp sigma theta t))
      (sym (subTmComp tau theta u))
      (fundTmEqEqEnv d (fundFitsSameEq fits ee))
  fundTmEqEqEnv {sigma = sigma} {tau = tau}
    (eqSubTmRule {sigma = theta} {tau = eta} {t = t} {A = A} d fitsEq) ee =
    compTmEq-subst
      (sym (subTyComp sigma theta A))
      (sym (subTmComp sigma theta t))
      (sym (subTmComp tau eta t))
      (fundTmEqEnv d (fundFitsEqEnv fitsEq ee))
  fundTmEqEqEnv {sigma = sigma} {tau = tau}
    (eqSubTmEqRule {sigma = theta} {tau = eta} {t = t} {u = u} {A = A} d fitsEq) ee =
    compTmEq-subst
      (sym (subTyComp sigma theta A))
      (sym (subTmComp sigma theta t))
      (sym (subTmComp tau eta u))
      (fundTmEqEqEnv d (fundFitsEqEnv fitsEq ee))
  fundTmEqEqEnv (cTop d) ee =
    proj₁ (fundTmEqEnv d ee) , evalStar
  fundTmEqEqEnv {sigma = sigma}
    (iSigmaEq {a = a} {b = b} {c = c} {d = d} {B = B} daeq dbeq dA dB) ee =
    let
      caeq = fundTmEqEqEnv daeq ee
      cbeq =
        compTmEq-subst
          (subTyComp sigma (singleSubst a) B
           ∙ singleLiftTy (subTm sigma a) sigma B)
          refl refl
          (fundTmEqEqEnv dbeq ee)
    in
    computableTmEqSigma-intro caeq cbeq
  fundTmEqEqEnv {sigma = sigma}
    (eSigmaEq {B = B} {M = M} {d = d} {m = m} {m' = m'} dM dd dm dmEq) ee =
    let
      b , c , e , f , evd , eve , eqB , eqCraw =
        computableTmEqSigma-elim (fundTmEqEqEnv dd ee)
      eqC =
        compTmEq-subst (sym (singleLiftTy b sigma B)) refl refl eqCraw
      branchEq =
        fundTmEqEqEnv dmEq (eqEnvCons (eqEnvCons ee eqB) eqC)
      eqSources =
        compTmEq-subst
          (sigmaBranchTargetTy b c sigma d M)
          (sym (sigmaCompLiftTm b c sigma m))
          (sym (sigmaCompLiftTm e f _ m'))
          branchEq
    in
    compTmEqElimRight eve (compTmEqElimLeft evd eqSources)
  fundTmEqEqEnv {sigma = sigma} {tau = tau}
    (cSigma {B = B} {M = M} {b = b} {c = c} {m = m} dM dSig db dc dm) ee =
    let
      bσ = subTm sigma b
      cσ = subTm sigma c
      bτ = subTm tau b
      cτ = subTm tau c
      eqB = fundTmEqEnv db ee
      eqC =
        compTmEq-subst
          (subTyComp sigma (singleSubst b) B)
          refl refl
          (fundTmEqEnv dc ee)
      branchEq =
        fundTmEqEnv dm (eqEnvCons (eqEnvCons ee eqB) eqC)
      eqSources =
        compTmEq-subst
          (sigmaBranchTargetTy bσ cσ sigma (tmPair b c) M)
          (sym (sigmaCompLiftTm bσ cσ sigma m))
          (sym (subTmComp tau (sigmaCompSub b c) m))
          branchEq
    in
    compTmEqElimLeft evalPair eqSources

  fundFitsSameEq : {gamma delta : Ctx} {theta sigma tau : Subst}
    -> FitsSubst gamma delta theta -> EqEnv gamma sigma tau
    -> EqEnv delta (compSub sigma theta) (compSub tau theta)
  fundFitsSameEq (fitsNil wf) ee = eqEnvNil
  fundFitsSameEq {sigma = sigma}
    (fitsCons {sigma = theta} {A = A} fits dt) ee =
    eqEnvCons (fundFitsSameEq fits ee)
      (compTmEq-subst
        (subTyComp sigma theta A)
        refl refl
        (fundTmEqEnv dt ee))

  fundFitsEqEnv : {gamma delta : Ctx} {theta eta sigma tau : Subst}
    -> FitsEqSubst gamma delta theta eta -> EqEnv gamma sigma tau
    -> EqEnv delta (compSub sigma theta) (compSub tau eta)
  fundFitsEqEnv (fitsEqNil wf) ee = eqEnvNil
  fundFitsEqEnv {sigma = sigma}
    (fitsEqCons {sigma = theta} {A = A} fitsEq dtu) ee =
    eqEnvCons (fundFitsEqEnv fitsEq ee)
      (compTmEq-subst
        (subTyComp sigma theta A)
        refl refl
        (fundTmEqEqEnv dtu ee))

fundTyEq : {gamma : Ctx} {A B : RawType} {sigma : Subst}
  -> Derivable (typeEq gamma A B) -> Env gamma sigma
  -> ComputableTyEq (subTy sigma A) (subTy sigma B)
fundTyEq d rho = fundTyEqEqEnv d (envReflEq rho)

fundTmEq : {gamma : Ctx} {t u : RawTerm} {A : RawType} {sigma : Subst}
  -> Derivable (termEq gamma t u A) -> Env gamma sigma
  -> ComputableTmEq (subTy sigma A) (subTm sigma t) (subTm sigma u)
fundTmEq d rho = fundTmEqEqEnv d (envReflEq rho)

fundFitsEq : {gamma delta : Ctx} {tau1 tau2 sigma : Subst}
  -> FitsEqSubst gamma delta tau1 tau2 -> Env gamma sigma
  -> EqEnv delta (compSub sigma tau1) (compSub sigma tau2)
fundFitsEq fitsEq rho = fundFitsEqEnv fitsEq (envReflEq rho)

fundTyClosed : {A : RawType}
  -> Derivable (isType [] A) -> ComputableTy A
fundTyClosed {A = A} d =
  compTy-subst (subTyId A) (fundTy d (envNil {sigma = idSubst}))

fundTmClosed : {t : RawTerm} {A : RawType}
  -> Derivable (hasTy [] t A) -> Computable A t
fundTmClosed {t = t} {A = A} d =
  compTm-subst (subTyId A) (subTmId t) (fundTm d (envNil {sigma = idSubst}))

fundTyEqClosed : {A B : RawType}
  -> Derivable (typeEq [] A B) -> ComputableTyEq A B
fundTyEqClosed {A = A} {B = B} d =
  compTyEq-subst (subTyId A) (subTyId B) (fundTyEq d (envNil {sigma = idSubst}))

fundTmEqClosed : {t u : RawTerm} {A : RawType}
  -> Derivable (termEq [] t u A) -> ComputableTmEq A t u
fundTmEqClosed {t = t} {u = u} {A = A} d =
  compTmEq-subst (subTyId A) (subTmId t) (subTmId u)
    (fundTmEq d (envNil {sigma = idSubst}))
