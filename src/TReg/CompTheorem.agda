module TReg.CompTheorem where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Empty.Base as Empty using (⊥ ; rec)
open import Cubical.Data.Sigma using (Σ-syntax ; _×_ ; _,_)
open import Cubical.Data.List.Base using ([] ; _∷_ ; _++_ ; length)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Nat.Order using (_<_ ; <-wellfounded)
open import Cubical.Data.Nat.Properties using (snotz)
open import Cubical.Data.Unit.Base using (Unit ; tt)
open import Cubical.Induction.WellFounded using (Acc ; acc)

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
open import TReg.SigmaComp
open import TReg.EqComp
open import TReg.QtrComp
open import TReg.MainTheorem

nonemptyNeNil : {A : RawType} {gamma : Ctx} -> (A ∷ gamma ≡ []) -> ⊥
nonemptyNeNil {gamma = gamma} p = snotz (cong length p)

case_of_ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} -> A -> (A -> B) -> B
case x of f = f x

subSubJIntoPath : {theta gamma delta : Ctx} {rho sigma : Subst} {J : JForm}
  -> subJInto theta rho (subJInto gamma sigma J) ≡ subJInto theta (compSub rho sigma) J
subSubJIntoPath {J = isType delta A} =
  cong (isType _) (subTyComp _ _ A)
subSubJIntoPath {J = typeEq delta A B} =
  cong₂ (typeEq _)
    (subTyComp _ _ A)
    (subTyComp _ _ B)
subSubJIntoPath {J = hasTy delta t A} =
  cong₂ (hasTy _)
    (subTmComp _ _ t)
    (subTyComp _ _ A)
subSubJIntoPath {J = termEq delta t u A} =
  cong₃ (termEq _)
    (subTmComp _ _ t)
    (subTmComp _ _ u)
    (subTyComp _ _ A)

subEqJIntoPath : {theta gamma delta : Ctx} {rho sigma tau : Subst} {J : JForm}
  -> subJInto theta rho (eqSubJInto gamma sigma tau J)
   ≡ eqSubJInto theta (compSub rho sigma) (compSub rho tau) J
subEqJIntoPath {J = isType delta A} =
  cong₂ (typeEq _)
    (subTyComp _ _ A)
    (subTyComp _ _ A)
subEqJIntoPath {J = typeEq delta A B} =
  cong₂ (typeEq _)
    (subTyComp _ _ A)
    (subTyComp _ _ B)
subEqJIntoPath {J = hasTy delta t A} =
  cong₃ (termEq _)
    (subTmComp _ _ t)
    (subTmComp _ _ t)
    (subTyComp _ _ A)
subEqJIntoPath {J = termEq delta t u A} =
  cong₃ (termEq _)
    (subTmComp _ _ t)
    (subTmComp _ _ u)
    (subTyComp _ _ A)

eqSubSubJIntoPath : {theta gamma delta : Ctx} {rho eta sigma : Subst} {J : JForm}
  -> eqSubJInto theta rho eta (subJInto gamma sigma J)
   ≡ eqSubJInto theta (compSub rho sigma) (compSub eta sigma) J
eqSubSubJIntoPath {J = isType delta A} =
  cong₂ (typeEq _)
    (subTyComp _ _ A)
    (subTyComp _ _ A)
eqSubSubJIntoPath {J = typeEq delta A B} =
  cong₂ (typeEq _)
    (subTyComp _ _ A)
    (subTyComp _ _ B)
eqSubSubJIntoPath {J = hasTy delta t A} =
  cong₃ (termEq _)
    (subTmComp _ _ t)
    (subTmComp _ _ t)
    (subTyComp _ _ A)
eqSubSubJIntoPath {J = termEq delta t u A} =
  cong₃ (termEq _)
    (subTmComp _ _ t)
    (subTmComp _ _ u)
    (subTyComp _ _ A)

eqSubEqJIntoPath : {theta gamma delta : Ctx} {rho eta sigma tau : Subst} {J : JForm}
  -> eqSubJInto theta rho eta (eqSubJInto gamma sigma tau J)
   ≡ eqSubJInto theta (compSub rho sigma) (compSub eta tau) J
eqSubEqJIntoPath {J = isType delta A} =
  cong₂ (typeEq _)
    (subTyComp _ _ A)
    (subTyComp _ _ A)
eqSubEqJIntoPath {J = typeEq delta A B} =
  cong₂ (typeEq _)
    (subTyComp _ _ A)
    (subTyComp _ _ B)
eqSubEqJIntoPath {J = hasTy delta t A} =
  cong₃ (termEq _)
    (subTmComp _ _ t)
    (subTmComp _ _ t)
    (subTyComp _ _ A)
eqSubEqJIntoPath {J = termEq delta t u A} =
  cong₃ (termEq _)
    (subTmComp _ _ t)
    (subTmComp _ _ u)
    (subTyComp _ _ A)

wkJKeepPath : {delta : Ctx} {J : JForm}
  -> subJInto (delta ++ ctxOf J) (keepSubstBy (length delta)) J ≡ wkJBy delta J
wkJKeepPath {delta = delta} {J = isType gamma A} =
  cong (isType _) (sym (renTyKeepSubstBy (length delta) A))
wkJKeepPath {delta = delta} {J = typeEq gamma A B} =
  cong₂ (typeEq _)
    (sym (renTyKeepSubstBy (length delta) A))
    (sym (renTyKeepSubstBy (length delta) B))
wkJKeepPath {delta = delta} {J = hasTy gamma t A} =
  cong₂ (hasTy _)
    (sym (renTmKeepSubstBy (length delta) t))
    (sym (renTyKeepSubstBy (length delta) A))
wkJKeepPath {delta = delta} {J = termEq gamma t u A} =
  cong₃ (termEq _)
    (sym (renTmKeepSubstBy (length delta) t))
    (sym (renTmKeepSubstBy (length delta) u))
    (sym (renTyKeepSubstBy (length delta) A))

compSubKeepBy : (sigma : Subst) (k : ℕ)
  -> compSub sigma (keepSubstBy k) ≡ dropSubstBy k sigma
compSubKeepBy sigma k = funExt λ n -> refl

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

wkTmBy0 : (t : RawTerm) -> wkTmBy 0 t ≡ t
wkTmBy0 t =
  renTmKeepSubstBy 0 t
  ∙ cong (λ sigma -> subTm sigma t) keepSubstBy0Id
  ∙ subTmId t

dropCons : (t : RawTerm) (sigma : Subst) (k : ℕ)
  -> dropSubstBy (suc k) (consSubst t sigma) ≡ dropSubstBy k sigma
dropCons t sigma k = funExt λ n -> refl

subTyWkStep : (t : RawTerm) (sigma : Subst) (k : ℕ) (A : RawType)
  -> subTy (consSubst t sigma) (wkTyBy (suc k) A)
   ≡ subTy sigma (wkTyBy k A)
subTyWkStep t sigma k A =
  subTyWkBy (consSubst t sigma) (suc k) A
  ∙ cong (λ rho -> subTy rho A) (dropCons t sigma k)
  ∙ sym (subTyWkBy sigma k A)

lookupVarFits : {delta gamma : Ctx} {A : RawType} {sigma : Subst}
  -> FitsSubst [] (delta ++ (A ∷ gamma)) sigma
  -> Derivable
       (hasTy [] (subTm sigma (var (length delta)))
         (subTy sigma (wkTyBy (suc (length delta)) A)))
lookupVarFits {delta = []} {A = A}
  (fitsCons {sigma = sigma} {t = t} fits dt) =
  subst
    (λ T -> Derivable (hasTy [] t T))
    (sym (subTyWkStep t sigma 0 A ∙ cong (subTy sigma) (wkTyBy0 A)))
    dt
lookupVarFits {delta = D ∷ delta} {A = A}
  (fitsCons {sigma = sigma} {t = t} fits dt) =
  subst
    (λ T -> Derivable (hasTy [] (subTm sigma (var (length delta))) T))
    (sym (subTyWkStep t sigma (suc (length delta)) A))
    (lookupVarFits {delta = delta} {A = A} {sigma = sigma} fits)

lookupVarFitsEq : {delta gamma : Ctx} {A : RawType} {sigma tau : Subst}
  -> FitsEqSubst [] (delta ++ (A ∷ gamma)) sigma tau
  -> Derivable
       (termEq [] (subTm sigma (var (length delta))) (subTm tau (var (length delta)))
         (subTy sigma (wkTyBy (suc (length delta)) A)))
lookupVarFitsEq {delta = []} {A = A}
  (fitsEqCons {sigma = sigma} {tau = tau} {t = t} {u = u} fitsEq dtu) =
  subst
    (λ T -> Derivable (termEq [] t u T))
    (sym (subTyWkStep t sigma 0 A ∙ cong (subTy sigma) (wkTyBy0 A)))
    dtu
lookupVarFitsEq {delta = D ∷ delta} {A = A}
  (fitsEqCons {sigma = sigma} {tau = tau} {t = t} {u = u} fitsEq dtu) =
  subst
    (λ T ->
      Derivable
        (termEq [] (subTm sigma (var (length delta))) (subTm tau (var (length delta))) T))
    (sym (subTyWkStep t sigma (suc (length delta)) A))
    (lookupVarFitsEq {delta = delta} {A = A} {sigma = sigma} {tau = tau} fitsEq)

lookupCompFits : {delta gamma : Ctx} {A : RawType} {sigma : Subst}
  -> CompFitsSubst (delta ++ (A ∷ gamma)) sigma
  -> Computable
       (hasTy [] (subTm sigma (var (length delta)))
         (subTy sigma (wkTyBy (suc (length delta)) A)))
lookupCompFits {delta = []} {A = A}
  (compFitsCons {sigma = sigma} {t = t} fits compt) =
  subst
    (λ T -> Computable (hasTy [] t T))
    (sym (subTyWkStep t sigma 0 A ∙ cong (subTy sigma) (wkTyBy0 A)))
    compt
lookupCompFits {delta = D ∷ delta} {A = A}
  (compFitsCons {sigma = sigma} {t = t} fits compt) =
  subst
    (λ T -> Computable (hasTy [] (subTm sigma (var (length delta))) T))
    (sym (subTyWkStep t sigma (suc (length delta)) A))
    (lookupCompFits {delta = delta} {A = A} {sigma = sigma} fits)

lookupCompFitsEq : {delta gamma : Ctx} {A : RawType} {sigma tau : Subst}
  -> CompFitsEqSubst (delta ++ (A ∷ gamma)) sigma tau
  -> Computable
       (termEq [] (subTm sigma (var (length delta))) (subTm tau (var (length delta)))
         (subTy sigma (wkTyBy (suc (length delta)) A)))
lookupCompFitsEq {delta = []} {A = A}
  (compFitsEqCons {sigma = sigma} {tau = tau} {t = t} {u = u} fitsEq comptu) =
  subst
    (λ T -> Computable (termEq [] t u T))
    (sym (subTyWkStep t sigma 0 A ∙ cong (subTy sigma) (wkTyBy0 A)))
    comptu
lookupCompFitsEq {delta = D ∷ delta} {A = A}
  (compFitsEqCons {sigma = sigma} {tau = tau} {t = t} {u = u} fitsEq comptu) =
  subst
    (λ T ->
      Computable
        (termEq [] (subTm sigma (var (length delta))) (subTm tau (var (length delta))) T))
    (sym (subTyWkStep t sigma (suc (length delta)) A))
    (lookupCompFitsEq {delta = delta} {A = A} {sigma = sigma} {tau = tau} fitsEq)

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

dropCompFits : {delta : Ctx} {sigma : Subst}
  -> (drop : Ctx)
  -> CompFitsSubst (drop ++ delta) sigma
  -> CompFitsSubst delta (dropSubstBy (length drop) sigma)
dropCompFits {delta = delta} {sigma = sigma} [] compFits = compFits
dropCompFits {delta = delta} {sigma = sigma} (A ∷ drop)
  (compFitsCons {sigma = sigmaTail} {t = t} compFits compt) =
  subst
    (λ rho -> CompFitsSubst delta rho)
    (dropCons t sigmaTail (length drop))
    (dropCompFits {delta = delta} {sigma = sigmaTail} drop compFits)

dropCompFitsEq : {delta : Ctx} {sigma tau : Subst}
  -> (drop : Ctx)
  -> CompFitsEqSubst (drop ++ delta) sigma tau
  -> CompFitsEqSubst delta (dropSubstBy (length drop) sigma) (dropSubstBy (length drop) tau)
dropCompFitsEq {delta = delta} {sigma = sigma} {tau = tau} [] compFitsEq = compFitsEq
dropCompFitsEq {delta = delta} {sigma = sigma} {tau = tau} (A ∷ drop)
  (compFitsEqCons {sigma = sigmaTail} {tau = tauTail} {t = t} {u = u} compFitsEq comptu) =
  subst
    (λ rho ->
      CompFitsEqSubst delta rho
        (dropSubstBy (suc (length drop)) (consSubst u tauTail)))
    (dropCons t sigmaTail (length drop))
    (subst
      (λ rho ->
        CompFitsEqSubst delta
          (dropSubstBy (suc (length drop)) (consSubst t sigmaTail))
          rho)
      (dropCons u tauTail (length drop))
      (dropCompFitsEq {delta = delta} {sigma = sigmaTail} {tau = tauTail} drop compFitsEq))

closedEqSubTy : {gamma : Ctx} {A : RawType} {sigma tau : Subst}
  -> Derivable (isType [] A)
  -> CtxWF gamma
  -> Derivable (typeEq gamma (subTy sigma A) (subTy tau A))
closedEqSubTy {gamma = gamma} {sigma = sigma} {tau = tau} dA wf =
  eqSubTyRule dA
    (fitsEqNil {gamma = gamma} {delta = []} {sigma = sigma} {tau = tau} wf)

closedEqSubTyEq : {gamma : Ctx} {A B : RawType} {sigma tau : Subst}
  -> Derivable (typeEq [] A B)
  -> CtxWF gamma
  -> Derivable (typeEq gamma (subTy sigma A) (subTy tau B))
closedEqSubTyEq {gamma = gamma} {sigma = sigma} {tau = tau} dAB wf =
  eqSubTyEqRule dAB
    (fitsEqNil {gamma = gamma} {delta = []} {sigma = sigma} {tau = tau} wf)

closedEqSubTm : {gamma : Ctx} {t : RawTerm} {A : RawType} {sigma tau : Subst}
  -> Derivable (hasTy [] t A)
  -> CtxWF gamma
  -> Derivable (termEq gamma (subTm sigma t) (subTm tau t) (subTy sigma A))
closedEqSubTm {gamma = gamma} {sigma = sigma} {tau = tau} dt wf =
  eqSubTmRule dt
    (fitsEqNil {gamma = gamma} {delta = []} {sigma = sigma} {tau = tau} wf)

closedEqSubTmEq : {gamma : Ctx} {t u : RawTerm} {A : RawType} {sigma tau : Subst}
  -> Derivable (termEq [] t u A)
  -> CtxWF gamma
  -> Derivable (termEq gamma (subTm sigma t) (subTm tau u) (subTy sigma A))
closedEqSubTmEq {gamma = gamma} {sigma = sigma} {tau = tau} dtu wf =
  eqSubTmEqRule dtu
    (fitsEqNil {gamma = gamma} {delta = []} {sigma = sigma} {tau = tau} wf)

liftFits : {theta gamma : Ctx} {A : RawType} {sigma : Subst}
  -> FitsSubst theta gamma sigma
  -> Derivable (isType theta (subTy sigma A))
  -> FitsSubst (subTy sigma A ∷ theta) (A ∷ gamma)
       (consSubst (var zero) (compSub (keepSubstBy 1) sigma))
liftFits {theta = theta} {gamma = gamma} {A = A} {sigma = sigma} fits dAσ =
  fitsCons tail headVar
  where
  wfAσ : CtxWF (subTy sigma A ∷ theta)
  wfAσ = wfCons (fitsSubstCtxWF fits) dAσ

  tail : FitsSubst (subTy sigma A ∷ theta) gamma (compSub (keepSubstBy 1) sigma)
  tail =
    composeFits
      (fitsKeep {delta = subTy sigma A ∷ []} {gamma = theta} wfAσ)
      fits

  headVar0 : Derivable
    (hasTy (subTy sigma A ∷ theta) (var zero) (wkTyBy 1 (subTy sigma A)))
  headVar0 = varStar {gamma = theta} {delta = []} {A = subTy sigma A} wfAσ dAσ

  headVar : Derivable
    (hasTy (subTy sigma A ∷ theta) (var zero) (subTy (compSub (keepSubstBy 1) sigma) A))
  headVar =
    subst
      (λ T -> Derivable (hasTy (subTy sigma A ∷ theta) (var zero) T))
      (renTyKeepSubstBy 1 (subTy sigma A) ∙ subTyComp (keepSubstBy 1) sigma A)
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
       (consSubst (var zero) (compSub (keepSubstBy 1) sigma))
       (consSubst (var zero) (compSub (keepSubstBy 1) tau))
liftFitsEq {theta = theta} {gamma = gamma} {A = A} {sigma = sigma} {tau = tau} fitsEq dAσ =
  fitsEqCons tail (reflTm headVar)
  where
  wfAσ : CtxWF (subTy sigma A ∷ theta)
  wfAσ = wfCons (fitsEqSubstCtxWF fitsEq) dAσ

  tail : FitsEqSubst (subTy sigma A ∷ theta) gamma
    (compSub (keepSubstBy 1) sigma)
    (compSub (keepSubstBy 1) tau)
  tail =
    composeFitsEq
      (fitsKeep {delta = subTy sigma A ∷ []} {gamma = theta} wfAσ)
      fitsEq

  headVar0 : Derivable
    (hasTy (subTy sigma A ∷ theta) (var zero) (wkTyBy 1 (subTy sigma A)))
  headVar0 = varStar {gamma = theta} {delta = []} {A = subTy sigma A} wfAσ dAσ

  headVar : Derivable
    (hasTy (subTy sigma A ∷ theta) (var zero) (subTy (compSub (keepSubstBy 1) sigma) A))
  headVar =
    subst
      (λ T -> Derivable (hasTy (subTy sigma A ∷ theta) (var zero) T))
      (renTyKeepSubstBy 1 (subTy sigma A) ∙ subTyComp (keepSubstBy 1) sigma A)
      headVar0

liftFitsEqOne : {gamma : Ctx} {A : RawType} {sigma tau : Subst}
  -> FitsEqSubst [] gamma sigma tau
  -> Derivable (isType [] (subTy sigma A))
  -> FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma)
       (consSubst (var zero) (compSub (keepSubstBy 1) sigma))
       (consSubst (var zero) (compSub (keepSubstBy 1) tau))
liftFitsEqOne = liftFitsEq

liftSubstCompKeep : (sigma : Subst)
  -> consSubst (var zero) (compSub (keepSubstBy 1) sigma) ≡ liftSubst sigma
liftSubstCompKeep sigma = funExt λ where
  zero -> refl
  (suc n) -> sym (renTmKeepSubstBy 1 (sigma n))

reflFitsEq : {gamma delta : Ctx} {sigma : Subst}
  -> FitsSubst gamma delta sigma
  -> FitsEqSubst gamma delta sigma sigma
reflFitsEq {gamma = gamma} {sigma = sigma} (fitsNil wf) =
  fitsEqNil {gamma = gamma} {delta = []} {sigma = sigma} {tau = sigma} wf
reflFitsEq (fitsCons fits dt) =
  fitsEqCons (reflFitsEq fits) (reflTm dt)

compSubIdLeft : (sigma : Subst) -> compSub idSubst sigma ≡ sigma
compSubIdLeft sigma = funExt λ n -> subTmId (sigma n)

oneBinderCompSub : (tau sigma : Subst)
  -> consSubst (tau zero) (compSub (dropSubstBy 1 tau) sigma) ≡ compSub tau (liftSubst sigma)
oneBinderCompSub tau sigma = funExt λ where
  zero -> refl
  (suc n) -> sym (subTmRen tau suc (sigma n))

twoBinderCompSub : (tau sigma : Subst)
  -> consSubst (tau zero) (consSubst (tau (suc zero)) (compSub (dropSubstBy 2 tau) sigma))
       ≡ compSub tau (liftSubst (liftSubst sigma))
twoBinderCompSub tau sigma = funExt λ where
  zero -> refl
  (suc zero) -> refl
  (suc (suc n)) ->
    sym
      (cong (subTm tau) (renTmComp suc suc (sigma n))
        ∙ subTmRen tau (compRen suc suc) (sigma n))

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
    (composeFits fits2 (liftFits lifted1 dBσ))

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
  in
  subst
    (λ rho ->
      FitsEqSubst [] (B ∷ A ∷ gamma) rho (compSub tau₂ (liftSubst (liftSubst sigma))))
    (cong (compSub tau₁) (liftSubstCompKeep (liftSubst sigma)))
    (subst
      (λ rho ->
        FitsEqSubst [] (B ∷ A ∷ gamma)
          (compSub tau₁ (consSubst (var zero) (compSub (keepSubstBy 1) (liftSubst sigma))))
          rho)
      (cong (compSub tau₂) (liftSubstCompKeep (liftSubst sigma)))
      (composeEqFits fitsEq (liftFits lifted1 dBσ)))

singleSubstCompLift : (sigma : Subst) (t : RawTerm)
  -> compSub (singleSubst (subTm sigma t)) (liftSubst sigma) ≡ compSub sigma (singleSubst t)
singleSubstCompLift sigma t = funExt λ where
  zero -> refl
  (suc n) ->
    subTmRen (singleSubst (subTm sigma t)) suc (sigma n)
    ∙ cong (λ rho -> subTm rho (sigma n)) (funExt λ k -> refl)
    ∙ subTmId (sigma n)

qtrBranchSubLiftComp : (sigma : Subst)
  -> compSub (liftSubst sigma) qtrBranchSub ≡ compSub qtrBranchSub (liftSubst sigma)
qtrBranchSubLiftComp sigma = funExt λ where
  zero -> refl
  (suc n) ->
    sym (subTmId (renTm suc (sigma n)))
    ∙ subTmRen idSubst suc (sigma n)
    ∙ cong (λ rho -> subTm rho (sigma n)) (sym (funExt λ k -> refl))
    ∙ sym (subTmRen qtrBranchSub suc (sigma n))

sigmaCompSubLiftComp : (sigma : Subst) (b c : RawTerm)
  -> compSub sigma (sigmaCompSub b c)
   ≡ compSub (sigmaCompSub (subTm sigma b) (subTm sigma c)) (liftSubst (liftSubst sigma))
sigmaCompSubLiftComp sigma b c = funExt λ where
  zero -> refl
  (suc zero) -> refl
  (suc (suc n)) ->
    sym (subTmId (sigma n))
    ∙ cong
        (λ rho -> subTm rho (sigma n))
        (sym (funExt λ k -> refl))
    ∙ sym (subTmRen (sigmaCompSub (subTm sigma b) (subTm sigma c)) (compRen suc suc) (sigma n))
    ∙ cong
        (λ t -> subTm (sigmaCompSub (subTm sigma b) (subTm sigma c)) t)
        (sym (renTmComp suc suc (sigma n)))

sigmaMotSubLiftComp : (sigma : Subst)
  -> compSub (liftSubst (liftSubst sigma)) sigmaMotSub ≡ compSub sigmaMotSub (liftSubst sigma)
sigmaMotSubLiftComp sigma = funExt λ where
  zero -> refl
  (suc n) ->
    renTmComp suc suc (sigma n)
    ∙ sym (subTmId (renTm (addRen 2) (sigma n)))
    ∙ subTmRen idSubst (addRen 2) (sigma n)
    ∙ sym (subTmRen sigmaMotSub suc (sigma n))

qtrCohSubLiftComp : (sigma : Subst)
  -> compSub (liftSubst (liftSubst sigma)) qtrCohSub ≡ compSub qtrCohSub (liftSubst sigma)
qtrCohSubLiftComp sigma = funExt λ where
  zero -> refl
  (suc n) ->
    renTmComp suc suc (sigma n)
    ∙ sym (subTmId (renTm (addRen 2) (sigma n)))
    ∙ subTmRen idSubst (addRen 2) (sigma n)
    ∙ sym (subTmRen qtrCohSub suc (sigma n))

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

qtrSecondBranchRenPath : qtrSecondBranchRen ≡ raiseRen suc
qtrSecondBranchRenPath = funExt λ where
  zero -> refl
  (suc n) -> refl

qtrSecondBranchSubLiftComp : (sigma : Subst)
  -> (λ n -> liftSubst (liftSubst sigma) (qtrSecondBranchRen n))
       ≡ renSub qtrSecondBranchRen (liftSubst sigma)
qtrSecondBranchSubLiftComp sigma = funExt λ where
  zero -> refl
  (suc n) ->
    renTmComp suc suc (sigma n)
    ∙ cong
        (λ rho -> renTm rho (sigma n))
        (funExt λ where
          zero -> refl
          (suc k) -> refl)
    ∙ sym (renTmComp qtrSecondBranchRen suc (sigma n))

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
  renTySub suc qtrBranchSub L
  ∙ cong
      (λ rho -> subTy rho L)
      (funExt λ where
        zero -> refl
        (suc n) -> refl)

{-# TERMINATING #-}
mutual
  fitsToCompFits : {gamma : Ctx} {sigma : Subst}
    -> FitsSubst [] gamma sigma
    -> CompFitsSubst gamma sigma
  fitsToCompFits (fitsNil wf) = compFitsNil
  fitsToCompFits (fitsCons fits dt) =
    compFitsCons
      (fitsToCompFits fits)
      (computableTheorem dt)

  fitsEqToCompFitsEq : {gamma : Ctx} {sigma tau : Subst}
    -> FitsEqSubst [] gamma sigma tau
    -> CompFitsEqSubst gamma sigma tau
  fitsEqToCompFitsEq (fitsEqNil wf) = compFitsEqNil
  fitsEqToCompFitsEq (fitsEqCons fitsEq dtu) =
    compFitsEqCons
      (fitsEqToCompFitsEq fitsEq)
      (computableTheorem dtu)

  packClosedSubst : {J : JForm} {sigma : Subst}
    -> FitsSubst [] (ctxOf J) sigma
    -> Computable (closedSubJ sigma J)
    -> ClosedSubstComp J sigma
  packClosedSubst fits comp = closedSubstComp comp (fitsToCompFits fits)

  packClosedEqSubst : {J : JForm} {sigma tau : Subst}
    -> FitsEqSubst [] (ctxOf J) sigma tau
    -> Computable (closedEqSubJ sigma tau J)
    -> ClosedEqSubstComp J sigma tau
  packClosedEqSubst fitsEq comp = closedEqSubstComp comp (fitsEqToCompFitsEq fitsEq)

  composeCompFits : {gamma delta : Ctx} {sigma sigma' : Subst}
    -> FitsSubst gamma delta sigma'
    -> FitsSubst [] gamma sigma
    -> CompFitsSubst gamma sigma
    -> CompFitsSubst delta (compSub sigma sigma')
  composeCompFits fits' fits cFits =
    compFitsEqLeft (composeCompFitsEq fits cFits (reflFitsEq fits'))

  composeCompEqFits : {gamma delta : Ctx} {sigma tau sigma' : Subst}
    -> FitsEqSubst [] gamma sigma tau
    -> CompFitsEqSubst gamma sigma tau
    -> FitsSubst gamma delta sigma'
    -> CompFitsEqSubst delta (compSub sigma sigma') (compSub tau sigma')
  composeCompEqFits fitsEq cFitsEq (fitsNil wf) = compFitsEqNil
  composeCompEqFits {sigma = sigma} {tau = tau} fitsEq cFitsEq
    (fitsCons {delta = delta} {sigma = sigma'} {A = A} {t = t} fits' dt) =
    subst
      (λ zeta -> CompFitsEqSubst (A ∷ delta) zeta (compSub tau (consSubst t sigma')))
      (sym (compSubCons sigma t sigma'))
      (subst
        (λ zeta ->
          CompFitsEqSubst (A ∷ delta) (consSubst (subTm sigma t) (compSub sigma sigma')) zeta)
        (sym (compSubCons tau t sigma'))
        (compFitsEqCons
          (composeCompEqFits fitsEq cFitsEq fits')
          (subst
            (λ T -> Computable (termEq [] (subTm sigma t) (subTm tau t) T))
            (subTyComp sigma sigma' A)
            (eqSubDerivTmComp dt fitsEq cFitsEq))))

  composeCompFitsEq : {gamma delta : Ctx} {sigma sigma' tau' : Subst}
    -> FitsSubst [] gamma sigma
    -> CompFitsSubst gamma sigma
    -> FitsEqSubst gamma delta sigma' tau'
    -> CompFitsEqSubst delta (compSub sigma sigma') (compSub sigma tau')
  composeCompFitsEq fits cFits fitsEq' =
    composeCompEqFitsEq (reflFitsEq fits) (reflCompFitsEq cFits) fitsEq'

  composeCompEqFitsEq : {gamma delta : Ctx} {sigma tau sigma' tau' : Subst}
    -> FitsEqSubst [] gamma sigma tau
    -> CompFitsEqSubst gamma sigma tau
    -> FitsEqSubst gamma delta sigma' tau'
    -> CompFitsEqSubst delta (compSub sigma sigma') (compSub tau tau')
  composeCompEqFitsEq fitsEq cFitsEq (fitsEqNil wf) = compFitsEqNil
  composeCompEqFitsEq {sigma = sigma} {tau = tau} fitsEq cFitsEq
    (fitsEqCons {delta = delta} {sigma = sigma'} {tau = tau'} {A = A} {t = t} {u = u} fitsEq' dtu) =
    subst
      (λ zeta -> CompFitsEqSubst (A ∷ delta) zeta (compSub tau (consSubst u tau')))
      (sym (compSubCons sigma t sigma'))
      (subst
        (λ zeta ->
          CompFitsEqSubst (A ∷ delta) (consSubst (subTm sigma t) (compSub sigma sigma')) zeta)
        (sym (compSubCons tau u tau'))
        (compFitsEqCons
          (composeCompEqFitsEq fitsEq cFitsEq fitsEq')
          (subst
            (λ T -> Computable (termEq [] (subTm sigma t) (subTm tau u) T))
            (subTyComp sigma sigma' A)
            (eqSubDerivTmEqComp dtu fitsEq cFitsEq))))

  singleClosedCompFits : {A : RawType} {tau : Subst}
    -> FitsSubst [] (A ∷ []) tau
    -> CompFitsSubst (A ∷ []) tau
  singleClosedCompFits (fitsCons {sigma = sigmaTail} {A = A} {t = t} (fitsNil wf) dt) =
    compFitsCons
      {sigma = sigmaTail}
      compFitsNil
      (subst
        (λ J -> Computable J)
        (cong₂ (hasTy [])
          (subTmId t)
          (subTyId (subTy sigmaTail A)))
        (substDerivTmComp dt (fitsNil {gamma = []} {delta = []} {sigma = idSubst} wfNil) compFitsNil))

  singleClosedCompFitsEq : {A : RawType} {tau₁ tau₂ : Subst}
    -> FitsEqSubst [] (A ∷ []) tau₁ tau₂
    -> CompFitsEqSubst (A ∷ []) tau₁ tau₂
  singleClosedCompFitsEq (fitsEqCons {sigma = sigmaTail} {A = A} {t = t} {u = u} (fitsEqNil wf) dtu) =
    compFitsEqCons
      {sigma = sigmaTail}
      compFitsEqNil
      (subst
        (λ J -> Computable J)
        (cong₃ (termEq [])
          (subTmId t)
          (subTmId u)
          (subTyId (subTy sigmaTail A)))
        (substDerivTmEqComp dtu (fitsNil {gamma = []} {delta = []} {sigma = idSubst} wfNil) compFitsNil))

  doubleClosedCompFits : {A B : RawType} {tau : Subst}
    -> FitsSubst [] (B ∷ A ∷ []) tau
    -> CompFitsSubst (B ∷ A ∷ []) tau
  doubleClosedCompFits
    (fitsCons
      {sigma = sigmaTail1} {A = B} {t = t1}
      (fitsCons {sigma = sigmaTail0} {A = A} {t = t0} (fitsNil wf) dt0)
      dt1) =
    compFitsCons
      {sigma = sigmaTail1}
      (compFitsCons
        {sigma = sigmaTail0}
        compFitsNil
        (subst
          (λ J -> Computable J)
          (cong₂ (hasTy [])
            (subTmId t0)
            (subTyId (subTy sigmaTail0 A)))
          (substDerivTmComp dt0 (fitsNil {gamma = []} {delta = []} {sigma = idSubst} wfNil) compFitsNil)))
      (subst
        (λ J -> Computable J)
        (cong₂ (hasTy [])
          (subTmId t1)
          (subTyId (subTy sigmaTail1 B)))
        (substDerivTmComp dt1 (fitsNil {gamma = []} {delta = []} {sigma = idSubst} wfNil) compFitsNil))

  doubleClosedCompFitsEq : {A B : RawType} {tau₁ tau₂ : Subst}
    -> FitsEqSubst [] (B ∷ A ∷ []) tau₁ tau₂
    -> CompFitsEqSubst (B ∷ A ∷ []) tau₁ tau₂
  doubleClosedCompFitsEq
    (fitsEqCons
      {sigma = sigmaTail1} {tau = tauTail1} {A = B} {t = t1} {u = u1}
      (fitsEqCons {sigma = sigmaTail0} {tau = tauTail0} {A = A} {t = t0} {u = u0} (fitsEqNil wf) dtu0)
      dtu1) =
    compFitsEqCons
      {sigma = sigmaTail1} {tau = tauTail1}
      (compFitsEqCons
        {sigma = sigmaTail0} {tau = tauTail0}
        compFitsEqNil
        (subst
          (λ J -> Computable J)
          (cong₃ (termEq [])
            (subTmId t0)
            (subTmId u0)
            (subTyId (subTy sigmaTail0 A)))
          (substDerivTmEqComp dtu0 (fitsNil {gamma = []} {delta = []} {sigma = idSubst} wfNil) compFitsNil)))
      (subst
        (λ J -> Computable J)
        (cong₃ (termEq [])
          (subTmId t1)
          (subTmId u1)
          (subTyId (subTy sigmaTail1 B)))
        (substDerivTmEqComp dtu1 (fitsNil {gamma = []} {delta = []} {sigma = idSubst} wfNil) compFitsNil))

  substClosedCompFits : {gamma : Ctx} {sigma rho : Subst}
    -> CompFitsSubst gamma sigma
    -> CompFitsSubst gamma (compSub rho sigma)
  substClosedCompFits {rho = rho} compFitsNil = compFitsNil
  substClosedCompFits {rho = rho}
    (compFitsCons {gamma = gamma} {sigma = sigma} {A = A} {t = t} cFits compt) =
    subst
      (λ zeta -> CompFitsSubst (A ∷ gamma) zeta)
      (sym (compSubCons rho t sigma))
      (compFitsCons
        (substClosedCompFits {sigma = sigma} {rho = rho} cFits)
        (subst
          (λ T -> Computable (hasTy [] (subTm rho t) T))
          (subTyComp rho sigma A)
          (compTmEqLeft
            (eqSubDerivTmComp
              (compToDerivable compt)
              (fitsEqNil {gamma = []} {delta = []} {sigma = rho} {tau = idSubst} wfNil)
              compFitsEqNil))))

  eqSubClosedCompFits : {gamma : Ctx} {sigma rho eta : Subst}
    -> CompFitsSubst gamma sigma
    -> CompFitsEqSubst gamma (compSub rho sigma) (compSub eta sigma)
  eqSubClosedCompFits {rho = rho} {eta = eta} compFitsNil = compFitsEqNil
  eqSubClosedCompFits {rho = rho} {eta = eta}
    (compFitsCons {gamma = gamma} {sigma = sigma} {A = A} {t = t} cFits compt) =
    subst
      (λ zeta -> CompFitsEqSubst (A ∷ gamma) zeta (compSub eta (consSubst t sigma)))
      (sym (compSubCons rho t sigma))
      (subst
        (λ zeta ->
          CompFitsEqSubst (A ∷ gamma) (consSubst (subTm rho t) (compSub rho sigma)) zeta)
        (sym (compSubCons eta t sigma))
        (compFitsEqCons
          (eqSubClosedCompFits {sigma = sigma} {rho = rho} {eta = eta} cFits)
          (subst
            (λ T -> Computable (termEq [] (subTm rho t) (subTm eta t) T))
            (subTyComp rho sigma A)
            (eqSubDerivTmComp
              (compToDerivable compt)
              (fitsEqNil {gamma = []} {delta = []} {sigma = rho} {tau = eta} wfNil)
              compFitsEqNil))))

  reflCompFitsEq : {gamma : Ctx} {sigma : Subst}
    -> CompFitsSubst gamma sigma
    -> CompFitsEqSubst gamma sigma sigma
  reflCompFitsEq {gamma = gamma} {sigma = sigma} cFits =
    subst
      (λ rho -> CompFitsEqSubst gamma rho sigma)
      (compSubIdLeft sigma)
      (subst
        (λ rho -> CompFitsEqSubst gamma (compSub idSubst sigma) rho)
        (compSubIdLeft sigma)
        (eqSubClosedCompFits {sigma = sigma} {rho = idSubst} {eta = idSubst} cFits))

  composeOneBinderComp : {gamma : Ctx} {A : RawType} {sigma tau : Subst}
    -> FitsSubst [] (subTy sigma A ∷ []) tau
    -> CompFitsSubst gamma sigma
    -> CompFitsSubst (A ∷ gamma) (compSub tau (liftSubst sigma))
  composeOneBinderComp fits cFits =
    compFitsEqLeft (composeOneBinderCompEq cFits (reflFitsEq fits))

  composeOneBinderCompEq : {gamma : Ctx} {A : RawType} {sigma tau₁ tau₂ : Subst}
    -> CompFitsSubst gamma sigma
    -> FitsEqSubst [] (subTy sigma A ∷ []) tau₁ tau₂
    -> CompFitsEqSubst (A ∷ gamma)
         (compSub tau₁ (liftSubst sigma))
         (compSub tau₂ (liftSubst sigma))
  composeOneBinderCompEq {gamma = gamma} {A = A} {sigma = sigma} {tau₁ = tau₁} {tau₂ = tau₂} cFits
    (fitsEqCons {sigma = tauTail₁} {tau = tauTail₂} {t = t} {u = u} (fitsEqNil wf) dtu) =
    subst
      (λ rho -> CompFitsEqSubst (A ∷ gamma) rho (compSub tau₂ (liftSubst sigma)))
      (oneBinderCompSub tau₁ sigma)
      (subst
        (λ rho ->
          CompFitsEqSubst (A ∷ gamma)
            (consSubst t (compSub tauTail₁ sigma))
            rho)
        (oneBinderCompSub tau₂ sigma)
        (compFitsEqCons
          (eqSubClosedCompFits
            {rho = tauTail₁}
            {eta = tauTail₂}
            cFits)
          (subst
            (λ T -> Computable (termEq [] t u T))
            (subTyComp tauTail₁ sigma A)
            (subst
              (λ J -> Computable J)
              (cong₃ (termEq [])
                (subTmId t)
                (subTmId u)
                (subTyId (subTy tauTail₁ (subTy sigma A))))
              (substDerivTmEqComp
                dtu
                (fitsNil {gamma = []} {delta = []} {sigma = idSubst} wfNil)
                compFitsNil)))))

  composeTwoBindersComp : {gamma : Ctx} {A B : RawType} {sigma tau : Subst}
    -> CompFitsSubst gamma sigma
    -> FitsSubst [] (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) tau
    -> CompFitsSubst (B ∷ A ∷ gamma) (compSub tau (liftSubst (liftSubst sigma)))
  composeTwoBindersComp cFits fits =
    compFitsEqLeft (composeTwoBindersCompEq cFits (reflFitsEq fits))

  composeTwoBindersCompEq : {gamma : Ctx} {A B : RawType} {sigma tau₁ tau₂ : Subst}
    -> CompFitsSubst gamma sigma
    -> FitsEqSubst [] (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) tau₁ tau₂
    -> CompFitsEqSubst (B ∷ A ∷ gamma)
         (compSub tau₁ (liftSubst (liftSubst sigma)))
         (compSub tau₂ (liftSubst (liftSubst sigma)))
  composeTwoBindersCompEq {gamma = gamma} {A = A} {B = B} {sigma = sigma} {tau₁ = tau₁} {tau₂ = tau₂}
    cFits
    (fitsEqCons {sigma = tauTail₁} {tau = etaTail₁} {t = t₁} {u = u₁}
      (fitsEqCons {sigma = tauTail₀} {tau = etaTail₀} {t = t₀} {u = u₀} (fitsEqNil wf) dtu₀)
      dtu₁) =
    subst
      (λ rho ->
        CompFitsEqSubst (B ∷ A ∷ gamma) rho (compSub tau₂ (liftSubst (liftSubst sigma))))
      (twoBinderCompSub tau₁ sigma)
      (subst
        (λ rho ->
          CompFitsEqSubst (B ∷ A ∷ gamma)
            (consSubst t₁ (consSubst t₀ (compSub tauTail₀ sigma)))
            rho)
        (twoBinderCompSub tau₂ sigma)
        (compFitsEqCons
          (compFitsEqCons
            (eqSubClosedCompFits
              {rho = tauTail₀}
              {eta = etaTail₀}
              cFits)
            (subst
              (λ T -> Computable (termEq [] t₀ u₀ T))
              (subTyComp tauTail₀ sigma A)
              (subst
                (λ J -> Computable J)
                (cong₃ (termEq [])
                  (subTmId t₀)
                  (subTmId u₀)
                  (subTyId (subTy tauTail₀ (subTy sigma A))))
                (substDerivTmEqComp
                  dtu₀
                  (fitsNil {gamma = []} {delta = []} {sigma = idSubst} wfNil)
                  compFitsNil))))
          (subst
            (λ T -> Computable (termEq [] t₁ u₁ T))
            (subTyComp tauTail₁ (liftSubst sigma) B
              ∙ cong (λ rho -> subTy rho B) (sym (oneBinderCompSub tauTail₁ sigma)))
            (subst
              (λ J -> Computable J)
              (cong₃ (termEq [])
                (subTmId t₁)
                (subTmId u₁)
                (subTyId (subTy tauTail₁ (subTy (liftSubst sigma) B))))
              (substDerivTmEqComp
                dtu₁
                (fitsNil {gamma = []} {delta = []} {sigma = idSubst} wfNil)
                compFitsNil)))))

  substOpenTy1 : {gamma : Ctx} {A B : RawType} {sigma : Subst}
    -> FitsSubst [] gamma sigma
    -> CompFitsSubst gamma sigma
    -> Derivable (isType [] (subTy sigma A))
    -> Computable (isType (A ∷ gamma) B)
    -> Computable (isType (subTy sigma A ∷ []) (subTy (liftSubst sigma) B))
  substOpenTy1 {A = A} {B = B} {sigma = sigma} fits cFits dAσ (compTyOpen neqBody dBody sub subEq) =
    subst
      (λ T -> Computable (isType (subTy sigma A ∷ []) T))
      (cong (λ rho -> subTy rho B) (liftSubstCompKeep sigma))
      (compTyOpen
        nonemptyNeNil
        (substTyRule dBody (liftFitsOne fits dAσ))
        (λ tau fits2 ->
          let
            composedFits = composeOneBinder fits dAσ fits2
            closed =
              sub
                (compSub tau (liftSubst sigma))
                composedFits
          in
          packClosedSubst fits2
            (subst
              (λ T -> Computable (isType [] T))
              (sym
                (cong (λ rho -> subTy tau (subTy rho B)) (liftSubstCompKeep sigma)
                  ∙ subTyComp tau (liftSubst sigma) B))
              (ClosedSubstComp.closedComp closed)))
        (λ tau₁ tau₂ fitsEq2 ->
          let
            composedFitsEq = composeOneBinderEq fits dAσ fitsEq2
            closedEq =
              subEq
                (compSub tau₁ (liftSubst sigma))
                (compSub tau₂ (liftSubst sigma))
                composedFitsEq
          in
          packClosedEqSubst fitsEq2
            (subst
              (λ J -> Computable J)
              (sym
                (cong₂ (typeEq [])
                  (cong (λ rho -> subTy tau₁ (subTy rho B)) (liftSubstCompKeep sigma)
                    ∙ subTyComp tau₁ (liftSubst sigma) B)
                  (cong (λ rho -> subTy tau₂ (subTy rho B)) (liftSubstCompKeep sigma)
                    ∙ subTyComp tau₂ (liftSubst sigma) B)))
              (ClosedEqSubstComp.closedEqComp closedEq))))

  substOpenTyEq1 : {gamma : Ctx} {A B C : RawType} {sigma : Subst}
    -> FitsSubst [] gamma sigma
    -> CompFitsSubst gamma sigma
    -> Derivable (isType [] (subTy sigma A))
    -> Computable (typeEq (A ∷ gamma) B C)
    -> Computable (typeEq (subTy sigma A ∷ []) (subTy (liftSubst sigma) B) (subTy (liftSubst sigma) C))
  substOpenTyEq1 {A = A} {B = B} {C = C} {sigma = sigma} fits cFits dAσ (compTyEqOpen neqBody dBody compLeft sub subEq) =
    subst
      (λ J -> Computable J)
      (cong₂ (typeEq (subTy sigma A ∷ []))
        (cong (λ rho -> subTy rho B) (liftSubstCompKeep sigma))
        (cong (λ rho -> subTy rho C) (liftSubstCompKeep sigma)))
      (compTyEqOpen
        nonemptyNeNil
        (substTyEqRule dBody (liftFitsOne fits dAσ))
        (subst
          (λ T -> Computable (isType (subTy sigma A ∷ []) T))
          (sym (cong (λ rho -> subTy rho B) (liftSubstCompKeep sigma)))
          (substOpenTy1 fits cFits dAσ compLeft))
        (λ tau fits2 ->
          let
            composedFits = composeOneBinder fits dAσ fits2
            closed =
              sub
                (compSub tau (liftSubst sigma))
                composedFits
          in
          packClosedSubst fits2
            (subst
              (λ J -> Computable J)
              (sym
                (cong₂ (typeEq [])
                  (cong (λ rho -> subTy tau (subTy rho B)) (liftSubstCompKeep sigma)
                    ∙ subTyComp tau (liftSubst sigma) B)
                  (cong (λ rho -> subTy tau (subTy rho C)) (liftSubstCompKeep sigma)
                    ∙ subTyComp tau (liftSubst sigma) C)))
              (ClosedSubstComp.closedComp closed)))
        (λ tau₁ tau₂ fitsEq2 ->
          let
            composedFitsEq = composeOneBinderEq fits dAσ fitsEq2
            closedEq =
              subEq
                (compSub tau₁ (liftSubst sigma))
                (compSub tau₂ (liftSubst sigma))
                composedFitsEq
          in
          packClosedEqSubst fitsEq2
            (subst
              (λ J -> Computable J)
              (sym
                (cong₂ (typeEq [])
                  (cong (λ rho -> subTy tau₁ (subTy rho B)) (liftSubstCompKeep sigma)
                    ∙ subTyComp tau₁ (liftSubst sigma) B)
                  (cong (λ rho -> subTy tau₂ (subTy rho C)) (liftSubstCompKeep sigma)
                    ∙ subTyComp tau₂ (liftSubst sigma) C)))
              (ClosedEqSubstComp.closedEqComp closedEq))))

  substOpenTm1 : {gamma : Ctx} {A T : RawType} {t : RawTerm} {sigma : Subst}
    -> FitsSubst [] gamma sigma
    -> CompFitsSubst gamma sigma
    -> Derivable (isType [] (subTy sigma A))
    -> Computable (hasTy (A ∷ gamma) t T)
    -> Computable
         (hasTy (subTy sigma A ∷ [])
           (subTm (liftSubst sigma) t)
           (subTy (liftSubst sigma) T))
  substOpenTm1 {A = A} {T = T} {t = t} {sigma = sigma} fits cFits dAσ (compTmOpen neqBody dBody compTy sub subEq) =
    subst
      (λ J -> Computable J)
      (cong₂
        (hasTy (subTy sigma A ∷ []))
        (cong (λ rho -> subTm rho t) (liftSubstCompKeep sigma))
        (cong (λ rho -> subTy rho T) (liftSubstCompKeep sigma)))
      (compTmOpen
        nonemptyNeNil
        (substTmRule dBody (liftFitsOne fits dAσ))
        (subst
          (λ T' -> Computable (isType (subTy sigma A ∷ []) T'))
          (sym (cong (λ rho -> subTy rho T) (liftSubstCompKeep sigma)))
          (substOpenTy1 fits cFits dAσ compTy))
        (λ tau fits2 ->
          let
            composedFits = composeOneBinder fits dAσ fits2
            closed =
              sub
                (compSub tau (liftSubst sigma))
                composedFits
          in
          packClosedSubst fits2
            (subst
              (λ J -> Computable J)
              (sym
                (cong₂ (hasTy [])
                  (cong (λ rho -> subTm tau (subTm rho t)) (liftSubstCompKeep sigma)
                    ∙ subTmComp tau (liftSubst sigma) t)
                  (cong (λ rho -> subTy tau (subTy rho T)) (liftSubstCompKeep sigma)
                    ∙ subTyComp tau (liftSubst sigma) T)))
              (ClosedSubstComp.closedComp closed)))
        (λ tau₁ tau₂ fitsEq2 ->
          let
            composedFitsEq = composeOneBinderEq fits dAσ fitsEq2
            closedEq =
              subEq
                (compSub tau₁ (liftSubst sigma))
                (compSub tau₂ (liftSubst sigma))
                composedFitsEq
          in
          packClosedEqSubst fitsEq2
            (subst
              (λ J -> Computable J)
              (sym
                (cong₃ (termEq [])
                  (cong (λ rho -> subTm tau₁ (subTm rho t)) (liftSubstCompKeep sigma)
                    ∙ subTmComp tau₁ (liftSubst sigma) t)
                  (cong (λ rho -> subTm tau₂ (subTm rho t)) (liftSubstCompKeep sigma)
                    ∙ subTmComp tau₂ (liftSubst sigma) t)
                  (cong (λ rho -> subTy tau₁ (subTy rho T)) (liftSubstCompKeep sigma)
                    ∙ subTyComp tau₁ (liftSubst sigma) T)))
              (ClosedEqSubstComp.closedEqComp closedEq))))

  substOpenTmEq1 : {gamma : Ctx} {A T : RawType} {t u : RawTerm} {sigma : Subst}
    -> FitsSubst [] gamma sigma
    -> CompFitsSubst gamma sigma
    -> Derivable (isType [] (subTy sigma A))
    -> Computable (termEq (A ∷ gamma) t u T)
    -> Computable
         (termEq (subTy sigma A ∷ [])
           (subTm (liftSubst sigma) t)
           (subTm (liftSubst sigma) u)
           (subTy (liftSubst sigma) T))
  substOpenTmEq1 {A = A} {T = T} {t = t} {u = u} {sigma = sigma} fits cFits dAσ (compTmEqOpen neqBody dBody compTm sub subEq) =
    subst
      (λ J -> Computable J)
      (cong₃
        (termEq (subTy sigma A ∷ []))
        (cong (λ rho -> subTm rho t) (liftSubstCompKeep sigma))
        (cong (λ rho -> subTm rho u) (liftSubstCompKeep sigma))
        (cong (λ rho -> subTy rho T) (liftSubstCompKeep sigma)))
      (compTmEqOpen
        nonemptyNeNil
        (substTmEqRule dBody (liftFitsOne fits dAσ))
        (subst
          (λ J -> Computable J)
          (sym
            (cong₂
              (hasTy (subTy sigma A ∷ []))
              (cong (λ rho -> subTm rho t) (liftSubstCompKeep sigma))
              (cong (λ rho -> subTy rho T) (liftSubstCompKeep sigma))))
          (substOpenTm1 fits cFits dAσ compTm))
        (λ tau fits2 ->
          let
            composedFits = composeOneBinder fits dAσ fits2
            closed =
              sub
                (compSub tau (liftSubst sigma))
                composedFits
          in
          packClosedSubst fits2
            (subst
              (λ J -> Computable J)
              (sym
                (cong₃ (termEq [])
                  (cong (λ rho -> subTm tau (subTm rho t)) (liftSubstCompKeep sigma)
                    ∙ subTmComp tau (liftSubst sigma) t)
                  (cong (λ rho -> subTm tau (subTm rho u)) (liftSubstCompKeep sigma)
                    ∙ subTmComp tau (liftSubst sigma) u)
                  (cong (λ rho -> subTy tau (subTy rho T)) (liftSubstCompKeep sigma)
                    ∙ subTyComp tau (liftSubst sigma) T)))
              (ClosedSubstComp.closedComp closed)))
        (λ tau₁ tau₂ fitsEq2 ->
          let
            composedFitsEq = composeOneBinderEq fits dAσ fitsEq2
            closedEq =
              subEq
                (compSub tau₁ (liftSubst sigma))
                (compSub tau₂ (liftSubst sigma))
                composedFitsEq
          in
          packClosedEqSubst fitsEq2
            (subst
              (λ J -> Computable J)
              (sym
                (cong₃ (termEq [])
                  (cong (λ rho -> subTm tau₁ (subTm rho t)) (liftSubstCompKeep sigma)
                    ∙ subTmComp tau₁ (liftSubst sigma) t)
                  (cong (λ rho -> subTm tau₂ (subTm rho u)) (liftSubstCompKeep sigma)
                    ∙ subTmComp tau₂ (liftSubst sigma) u)
                  (cong (λ rho -> subTy tau₁ (subTy rho T)) (liftSubstCompKeep sigma)
                    ∙ subTyComp tau₁ (liftSubst sigma) T)))
              (ClosedEqSubstComp.closedEqComp closedEq))))

  substOpenTy2 : {gamma : Ctx} {A B T : RawType} {sigma : Subst}
    -> FitsSubst [] gamma sigma
    -> CompFitsSubst gamma sigma
    -> Derivable (isType [] (subTy sigma A))
    -> Derivable (isType (subTy sigma A ∷ []) (subTy (liftSubst sigma) B))
    -> Computable (isType (B ∷ A ∷ gamma) T)
    -> Computable
         (isType (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ [])
           (subTy (liftSubst (liftSubst sigma)) T))
  substOpenTy2 {gamma = gamma} {A = A} {B = B} {T = T} {sigma = sigma} fits cFits dAσ dBσ dT =
    let
      lifted1 : FitsSubst (subTy sigma A ∷ []) (A ∷ gamma) (liftSubst sigma)
      lifted1 =
        subst
          (λ rho -> FitsSubst (subTy sigma A ∷ []) (A ∷ gamma) rho)
          (liftSubstCompKeep sigma)
          (liftFitsOne fits dAσ)
    in
    case dT of λ where
      (compTyOpen neqBody dBody sub subEq) ->
        subst
          (λ T' -> Computable (isType (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) T'))
          (cong (λ rho -> subTy rho T) (liftSubstCompKeep (liftSubst sigma)))
          (compTyOpen
            nonemptyNeNil
            (substTyRule dBody (liftFits lifted1 dBσ))
            (λ tau fits2 ->
              let
                composedFits = composeTwoBinders fits dAσ dBσ fits2
                closed =
                  sub
                    (compSub tau (liftSubst (liftSubst sigma)))
                    composedFits
              in
              packClosedSubst fits2
                (subst
                  (λ T' -> Computable (isType [] T'))
                  (sym
                    (cong (λ rho -> subTy tau (subTy rho T)) (liftSubstCompKeep (liftSubst sigma))
                      ∙ subTyComp tau (liftSubst (liftSubst sigma)) T))
                  (ClosedSubstComp.closedComp closed)))
            (λ tau₁ tau₂ fitsEq2 ->
              let
                composedFitsEq = composeTwoBindersEq fits dAσ dBσ fitsEq2
                closedEq =
                  subEq
                    (compSub tau₁ (liftSubst (liftSubst sigma)))
                    (compSub tau₂ (liftSubst (liftSubst sigma)))
                    composedFitsEq
              in
              packClosedEqSubst fitsEq2
                (subst
                  (λ J -> Computable J)
                  (sym
                    (cong₂ (typeEq [])
                      (cong (λ rho -> subTy tau₁ (subTy rho T)) (liftSubstCompKeep (liftSubst sigma))
                        ∙ subTyComp tau₁ (liftSubst (liftSubst sigma)) T)
                      (cong (λ rho -> subTy tau₂ (subTy rho T)) (liftSubstCompKeep (liftSubst sigma))
                        ∙ subTyComp tau₂ (liftSubst (liftSubst sigma)) T)))
                  (ClosedEqSubstComp.closedEqComp closedEq))))

  substOpenTm2 : {gamma : Ctx} {A B T : RawType} {t : RawTerm} {sigma : Subst}
    -> FitsSubst [] gamma sigma
    -> CompFitsSubst gamma sigma
    -> Derivable (isType [] (subTy sigma A))
    -> Derivable (isType (subTy sigma A ∷ []) (subTy (liftSubst sigma) B))
    -> Computable (hasTy (B ∷ A ∷ gamma) t T)
    -> Computable
         (hasTy (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ [])
           (subTm (liftSubst (liftSubst sigma)) t)
           (subTy (liftSubst (liftSubst sigma)) T))
  substOpenTm2 {gamma = gamma} {A = A} {B = B} {T = T} {t = t} {sigma = sigma} fits cFits dAσ dBσ dt =
    let
      lifted1 : FitsSubst (subTy sigma A ∷ []) (A ∷ gamma) (liftSubst sigma)
      lifted1 =
        subst
          (λ rho -> FitsSubst (subTy sigma A ∷ []) (A ∷ gamma) rho)
          (liftSubstCompKeep sigma)
          (liftFitsOne fits dAσ)
    in
    case dt of λ where
      (compTmOpen neqBody dBody compTy sub subEq) ->
        subst
          (λ J -> Computable J)
          (cong₂
            (hasTy (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []))
            (cong (λ rho -> subTm rho t) (liftSubstCompKeep (liftSubst sigma)))
            (cong (λ rho -> subTy rho T) (liftSubstCompKeep (liftSubst sigma))))
          (compTmOpen
            nonemptyNeNil
            (substTmRule dBody (liftFits lifted1 dBσ))
            (subst
              (λ T' ->
                Computable (isType (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) T'))
              (sym (cong (λ rho -> subTy rho T) (liftSubstCompKeep (liftSubst sigma))))
              (substOpenTy2 fits cFits dAσ dBσ compTy))
            (λ tau fits2 ->
              let
                composedFits = composeTwoBinders fits dAσ dBσ fits2
                closed =
                  sub
                    (compSub tau (liftSubst (liftSubst sigma)))
                    composedFits
              in
              packClosedSubst fits2
                (subst
                  (λ J -> Computable J)
                  (sym
                    (cong₂ (hasTy [])
                      (cong (λ rho -> subTm tau (subTm rho t)) (liftSubstCompKeep (liftSubst sigma))
                        ∙ subTmComp tau (liftSubst (liftSubst sigma)) t)
                      (cong (λ rho -> subTy tau (subTy rho T)) (liftSubstCompKeep (liftSubst sigma))
                        ∙ subTyComp tau (liftSubst (liftSubst sigma)) T)))
                  (ClosedSubstComp.closedComp closed)))
            (λ tau₁ tau₂ fitsEq2 ->
              let
                composedFitsEq = composeTwoBindersEq fits dAσ dBσ fitsEq2
                closedEq =
                  subEq
                    (compSub tau₁ (liftSubst (liftSubst sigma)))
                    (compSub tau₂ (liftSubst (liftSubst sigma)))
                    composedFitsEq
              in
              packClosedEqSubst fitsEq2
                (subst
                  (λ J -> Computable J)
                  (sym
                    (cong₃ (termEq [])
                      (cong (λ rho -> subTm tau₁ (subTm rho t)) (liftSubstCompKeep (liftSubst sigma))
                        ∙ subTmComp tau₁ (liftSubst (liftSubst sigma)) t)
                      (cong (λ rho -> subTm tau₂ (subTm rho t)) (liftSubstCompKeep (liftSubst sigma))
                        ∙ subTmComp tau₂ (liftSubst (liftSubst sigma)) t)
                      (cong (λ rho -> subTy tau₁ (subTy rho T)) (liftSubstCompKeep (liftSubst sigma))
                        ∙ subTyComp tau₁ (liftSubst (liftSubst sigma)) T)))
                  (ClosedEqSubstComp.closedEqComp closedEq))))

  substOpenTmEq2 : {gamma : Ctx} {A B T : RawType} {t u : RawTerm} {sigma : Subst}
    -> FitsSubst [] gamma sigma
    -> CompFitsSubst gamma sigma
    -> Derivable (isType [] (subTy sigma A))
    -> Derivable (isType (subTy sigma A ∷ []) (subTy (liftSubst sigma) B))
    -> Computable (termEq (B ∷ A ∷ gamma) t u T)
    -> Computable
         (termEq (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ [])
           (subTm (liftSubst (liftSubst sigma)) t)
           (subTm (liftSubst (liftSubst sigma)) u)
           (subTy (liftSubst (liftSubst sigma)) T))
  substOpenTmEq2 {gamma = gamma} {A = A} {B = B} {T = T} {t = t} {u = u} {sigma = sigma} fits cFits dAσ dBσ dtu =
    let
      lifted1 : FitsSubst (subTy sigma A ∷ []) (A ∷ gamma) (liftSubst sigma)
      lifted1 =
        subst
          (λ rho -> FitsSubst (subTy sigma A ∷ []) (A ∷ gamma) rho)
          (liftSubstCompKeep sigma)
          (liftFitsOne fits dAσ)
    in
    case dtu of λ where
      (compTmEqOpen neqBody dBody compTm sub subEq) ->
        subst
          (λ J -> Computable J)
          (cong₃
            (termEq (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []))
            (cong (λ rho -> subTm rho t) (liftSubstCompKeep (liftSubst sigma)))
            (cong (λ rho -> subTm rho u) (liftSubstCompKeep (liftSubst sigma)))
            (cong (λ rho -> subTy rho T) (liftSubstCompKeep (liftSubst sigma))))
          (compTmEqOpen
            nonemptyNeNil
            (substTmEqRule dBody (liftFits lifted1 dBσ))
            (subst
              (λ J -> Computable J)
              (sym
                (cong₂
                  (hasTy (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []))
                  (cong (λ rho -> subTm rho t) (liftSubstCompKeep (liftSubst sigma)))
                  (cong (λ rho -> subTy rho T) (liftSubstCompKeep (liftSubst sigma)))))
              (substOpenTm2 fits cFits dAσ dBσ compTm))
            (λ tau fits2 ->
              let
                composedFits = composeTwoBinders fits dAσ dBσ fits2
                closed =
                  sub
                    (compSub tau (liftSubst (liftSubst sigma)))
                    composedFits
              in
              packClosedSubst fits2
                (subst
                  (λ J -> Computable J)
                  (sym
                    (cong₃ (termEq [])
                      (cong (λ rho -> subTm tau (subTm rho t)) (liftSubstCompKeep (liftSubst sigma))
                        ∙ subTmComp tau (liftSubst (liftSubst sigma)) t)
                      (cong (λ rho -> subTm tau (subTm rho u)) (liftSubstCompKeep (liftSubst sigma))
                        ∙ subTmComp tau (liftSubst (liftSubst sigma)) u)
                      (cong (λ rho -> subTy tau (subTy rho T)) (liftSubstCompKeep (liftSubst sigma))
                        ∙ subTyComp tau (liftSubst (liftSubst sigma)) T)))
                  (ClosedSubstComp.closedComp closed)))
            (λ tau₁ tau₂ fitsEq2 ->
              let
                composedFitsEq = composeTwoBindersEq fits dAσ dBσ fitsEq2
                closedEq =
                  subEq
                    (compSub tau₁ (liftSubst (liftSubst sigma)))
                    (compSub tau₂ (liftSubst (liftSubst sigma)))
                    composedFitsEq
              in
              packClosedEqSubst fitsEq2
                (subst
                  (λ J -> Computable J)
                  (sym
                    (cong₃ (termEq [])
                      (cong (λ rho -> subTm tau₁ (subTm rho t)) (liftSubstCompKeep (liftSubst sigma))
                        ∙ subTmComp tau₁ (liftSubst (liftSubst sigma)) t)
                      (cong (λ rho -> subTm tau₂ (subTm rho u)) (liftSubstCompKeep (liftSubst sigma))
                        ∙ subTmComp tau₂ (liftSubst (liftSubst sigma)) u)
                      (cong (λ rho -> subTy tau₁ (subTy rho T)) (liftSubstCompKeep (liftSubst sigma))
                        ∙ subTyComp tau₁ (liftSubst (liftSubst sigma)) T)))
                  (ClosedEqSubstComp.closedEqComp closedEq))))

  eqSubOpenTy1 : {gamma : Ctx} {A B : RawType} {sigma tau : Subst}
    -> FitsEqSubst [] gamma sigma tau
    -> CompFitsEqSubst gamma sigma tau
    -> Derivable (isType [] (subTy sigma A))
    -> Computable (isType (A ∷ gamma) B)
    -> Computable (typeEq (subTy sigma A ∷ []) (subTy (liftSubst sigma) B) (subTy (liftSubst tau) B))
  eqSubOpenTy1 {gamma = gamma} {A = A} {B = B} {sigma = sigma} {tau = tau} fitsEq cFitsEq dAσ dB =
    let
      sigmaCFits = compFitsEqLeft cFitsEq
      sigmaFits = compFitsToFits sigmaCFits
      liftedEq :
        FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma)
          (liftSubst sigma)
          (liftSubst tau)
      liftedEq =
        subst
          (λ rho -> FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma) rho (liftSubst tau))
          (liftSubstCompKeep sigma)
          (subst
            (λ rho ->
              FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma)
                (consSubst (var zero) (compSub (keepSubstBy 1) sigma))
                rho)
            (liftSubstCompKeep tau)
            (liftFitsEqOne fitsEq dAσ))
    in
    case dB of λ where
      (compTyOpen neqBody dBody sub subEq) ->
        compTyEqOpen
          nonemptyNeNil
          (eqSubTyRule dBody liftedEq)
          (substOpenTy1 sigmaFits sigmaCFits dAσ dB)
          (λ rho fits2 ->
            let
              composedFitsEq = composeFitsEq fits2 liftedEq
              closedEq =
                subEq
                  (compSub rho (liftSubst sigma))
                  (compSub rho (liftSubst tau))
                  composedFitsEq
              body =
                subst
                  (λ J -> Computable J)
                  (sym
                    (cong₂ (typeEq [])
                      (subTyComp rho (liftSubst sigma) B)
                      (subTyComp rho (liftSubst tau) B)))
                  (ClosedEqSubstComp.closedEqComp closedEq)
            in
            packClosedSubst fits2 body)
          (λ rho eta fitsEq2 ->
            let
              composedFitsEq = composeEqFitsEq fitsEq2 liftedEq
              closedEq =
                subEq
                  (compSub rho (liftSubst sigma))
                  (compSub eta (liftSubst tau))
                  composedFitsEq
              body =
                subst
                  (λ J -> Computable J)
                  (sym
                    (cong₂ (typeEq [])
                      (subTyComp rho (liftSubst sigma) B)
                      (subTyComp eta (liftSubst tau) B)))
                  (ClosedEqSubstComp.closedEqComp closedEq)
            in
            packClosedEqSubst fitsEq2 body)

  eqSubOpenTyEq1 : {gamma : Ctx} {A B C : RawType} {sigma tau : Subst}
    -> FitsEqSubst [] gamma sigma tau
    -> CompFitsEqSubst gamma sigma tau
    -> Derivable (isType [] (subTy sigma A))
    -> Computable (typeEq (A ∷ gamma) B C)
    -> Computable (typeEq (subTy sigma A ∷ []) (subTy (liftSubst sigma) B) (subTy (liftSubst tau) C))
  eqSubOpenTyEq1 {gamma = gamma} {A = A} {B = B} {C = C} {sigma = sigma} {tau = tau} fitsEq cFitsEq dAσ dBC =
    let
      sigmaCFits = compFitsEqLeft cFitsEq
      sigmaFits = compFitsToFits sigmaCFits
      liftedEq :
        FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma)
          (liftSubst sigma)
          (liftSubst tau)
      liftedEq =
        subst
          (λ rho -> FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma) rho (liftSubst tau))
          (liftSubstCompKeep sigma)
          (subst
            (λ rho ->
              FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma)
                (consSubst (var zero) (compSub (keepSubstBy 1) sigma))
                rho)
            (liftSubstCompKeep tau)
            (liftFitsEqOne fitsEq dAσ))
    in
    case dBC of λ where
      (compTyEqOpen neqBody dBody compLeft sub subEq) ->
        compTyEqOpen
          nonemptyNeNil
          (eqSubTyEqRule dBody liftedEq)
          (substOpenTy1 sigmaFits sigmaCFits dAσ compLeft)
          (λ rho fits2 ->
            let
              composedFitsEq = composeFitsEq fits2 liftedEq
              closedEq =
                subEq
                  (compSub rho (liftSubst sigma))
                  (compSub rho (liftSubst tau))
                  composedFitsEq
              body =
                subst
                  (λ J -> Computable J)
                  (sym
                    (cong₂ (typeEq [])
                      (subTyComp rho (liftSubst sigma) B)
                      (subTyComp rho (liftSubst tau) C)))
                  (ClosedEqSubstComp.closedEqComp closedEq)
            in
            packClosedSubst fits2 body)
          (λ rho eta fitsEq2 ->
            let
              composedFitsEq = composeEqFitsEq fitsEq2 liftedEq
              closedEq =
                subEq
                  (compSub rho (liftSubst sigma))
                  (compSub eta (liftSubst tau))
                  composedFitsEq
              body =
                subst
                  (λ J -> Computable J)
                  (sym
                    (cong₂ (typeEq [])
                      (subTyComp rho (liftSubst sigma) B)
                      (subTyComp eta (liftSubst tau) C)))
                  (ClosedEqSubstComp.closedEqComp closedEq)
            in
            packClosedEqSubst fitsEq2 body)

  eqSubOpenTm1 : {gamma : Ctx} {A T : RawType} {t : RawTerm} {sigma tau : Subst}
    -> FitsEqSubst [] gamma sigma tau
    -> CompFitsEqSubst gamma sigma tau
    -> Derivable (isType [] (subTy sigma A))
    -> Computable (hasTy (A ∷ gamma) t T)
    -> Computable
         (termEq (subTy sigma A ∷ [])
           (subTm (liftSubst sigma) t)
           (subTm (liftSubst tau) t)
           (subTy (liftSubst sigma) T))
  eqSubOpenTm1 {gamma = gamma} {A = A} {T = T} {t = t} {sigma = sigma} {tau = tau}
    fitsEq cFitsEq dAσ dt =
    let
      sigmaCFits = compFitsEqLeft cFitsEq
      sigmaFits = compFitsToFits sigmaCFits
      liftedEq :
        FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma)
          (liftSubst sigma)
          (liftSubst tau)
      liftedEq =
        subst
          (λ rho -> FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma) rho (liftSubst tau))
          (liftSubstCompKeep sigma)
          (subst
            (λ rho ->
              FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma)
                (consSubst (var zero) (compSub (keepSubstBy 1) sigma))
                rho)
            (liftSubstCompKeep tau)
            (liftFitsEqOne fitsEq dAσ))
    in
    case dt of λ where
      (compTmOpen neqBody dBody compTy sub subEq) ->
        compTmEqOpen
          nonemptyNeNil
          (eqSubTmRule dBody liftedEq)
          (substOpenTm1 sigmaFits sigmaCFits dAσ dt)
          (λ rho fits2 ->
            let
              composedFitsEq = composeFitsEq fits2 liftedEq
              closedEq =
                subEq
                  (compSub rho (liftSubst sigma))
                  (compSub rho (liftSubst tau))
                  composedFitsEq
              body =
                subst
                  (λ J -> Computable J)
                  (sym
                    (cong₃ (termEq [])
                      (subTmComp rho (liftSubst sigma) t)
                      (subTmComp rho (liftSubst tau) t)
                      (subTyComp rho (liftSubst sigma) T)))
                  (ClosedEqSubstComp.closedEqComp closedEq)
            in
            packClosedSubst fits2 body)
          (λ rho eta fitsEq2 ->
            let
              composedFitsEq = composeEqFitsEq fitsEq2 liftedEq
              closedEq =
                subEq
                  (compSub rho (liftSubst sigma))
                  (compSub eta (liftSubst tau))
                  composedFitsEq
              body =
                subst
                  (λ J -> Computable J)
                  (sym
                    (cong₃ (termEq [])
                      (subTmComp rho (liftSubst sigma) t)
                      (subTmComp eta (liftSubst tau) t)
                      (subTyComp rho (liftSubst sigma) T)))
                  (ClosedEqSubstComp.closedEqComp closedEq)
            in
            packClosedEqSubst fitsEq2 body)

  eqSubOpenTmEq1 : {gamma : Ctx} {A T : RawType} {t u : RawTerm} {sigma tau : Subst}
    -> FitsEqSubst [] gamma sigma tau
    -> CompFitsEqSubst gamma sigma tau
    -> Derivable (isType [] (subTy sigma A))
    -> Computable (termEq (A ∷ gamma) t u T)
    -> Computable
         (termEq (subTy sigma A ∷ [])
           (subTm (liftSubst sigma) t)
           (subTm (liftSubst tau) u)
           (subTy (liftSubst sigma) T))
  eqSubOpenTmEq1 {gamma = gamma} {A = A} {T = T} {t = t} {u = u} {sigma = sigma} {tau = tau}
    fitsEq cFitsEq dAσ dtu =
    let
      sigmaCFits = compFitsEqLeft cFitsEq
      sigmaFits = compFitsToFits sigmaCFits
      liftedEq :
        FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma)
          (liftSubst sigma)
          (liftSubst tau)
      liftedEq =
        subst
          (λ rho -> FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma) rho (liftSubst tau))
          (liftSubstCompKeep sigma)
          (subst
            (λ rho ->
              FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma)
                (consSubst (var zero) (compSub (keepSubstBy 1) sigma))
                rho)
            (liftSubstCompKeep tau)
            (liftFitsEqOne fitsEq dAσ))
    in
    case dtu of λ where
      (compTmEqOpen neqBody dBody compTm sub subEq) ->
        compTmEqOpen
          nonemptyNeNil
          (eqSubTmEqRule dBody liftedEq)
          (substOpenTm1 sigmaFits sigmaCFits dAσ compTm)
          (λ rho fits2 ->
            let
              composedFitsEq = composeFitsEq fits2 liftedEq
              closedEq =
                subEq
                  (compSub rho (liftSubst sigma))
                  (compSub rho (liftSubst tau))
                  composedFitsEq
              body =
                subst
                  (λ J -> Computable J)
                  (sym
                    (cong₃ (termEq [])
                      (subTmComp rho (liftSubst sigma) t)
                      (subTmComp rho (liftSubst tau) u)
                      (subTyComp rho (liftSubst sigma) T)))
                  (ClosedEqSubstComp.closedEqComp closedEq)
            in
            packClosedSubst fits2 body)
          (λ rho eta fitsEq2 ->
            let
              composedFitsEq = composeEqFitsEq fitsEq2 liftedEq
              closedEq =
                subEq
                  (compSub rho (liftSubst sigma))
                  (compSub eta (liftSubst tau))
                  composedFitsEq
              body =
                subst
                  (λ J -> Computable J)
                  (sym
                    (cong₃ (termEq [])
                      (subTmComp rho (liftSubst sigma) t)
                      (subTmComp eta (liftSubst tau) u)
                      (subTyComp rho (liftSubst sigma) T)))
                  (ClosedEqSubstComp.closedEqComp closedEq)
            in
            packClosedEqSubst fitsEq2 body)

  eqSubOpenTm2 : {gamma : Ctx} {A B T : RawType} {t : RawTerm} {sigma tau : Subst}
    -> FitsEqSubst [] gamma sigma tau
    -> CompFitsEqSubst gamma sigma tau
    -> Derivable (isType [] (subTy sigma A))
    -> Derivable (isType (subTy sigma A ∷ []) (subTy (liftSubst sigma) B))
    -> Computable (hasTy (B ∷ A ∷ gamma) t T)
    -> Computable
         (termEq (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ [])
           (subTm (liftSubst (liftSubst sigma)) t)
           (subTm (liftSubst (liftSubst tau)) t)
           (subTy (liftSubst (liftSubst sigma)) T))
  eqSubOpenTm2 {gamma = gamma} {A = A} {B = B} {T = T} {t = t} {sigma = sigma} {tau = tau}
    fitsEq cFitsEq dAσ dBσ dt =
    let
      sigmaCFits = compFitsEqLeft cFitsEq
      sigmaFits = compFitsToFits sigmaCFits
      lifted1Eq :
        FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma)
          (liftSubst sigma)
          (liftSubst tau)
      lifted1Eq =
        subst
          (λ rho -> FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma) rho (liftSubst tau))
          (liftSubstCompKeep sigma)
          (subst
            (λ rho ->
              FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma)
                (consSubst (var zero) (compSub (keepSubstBy 1) sigma))
                rho)
            (liftSubstCompKeep tau)
            (liftFitsEqOne fitsEq dAσ))
      lifted2Eq :
        FitsEqSubst (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) (B ∷ A ∷ gamma)
          (liftSubst (liftSubst sigma))
          (liftSubst (liftSubst tau))
      lifted2Eq =
        subst
          (λ rho ->
            FitsEqSubst (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) (B ∷ A ∷ gamma)
              rho
              (liftSubst (liftSubst tau)))
          (liftSubstCompKeep (liftSubst sigma))
          (subst
            (λ rho ->
              FitsEqSubst (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) (B ∷ A ∷ gamma)
                (consSubst (var zero) (compSub (keepSubstBy 1) (liftSubst sigma)))
                rho)
            (liftSubstCompKeep (liftSubst tau))
            (liftFitsEq lifted1Eq dBσ))
    in
    case dt of λ where
      (compTmOpen neqBody dBody compTy sub subEq) ->
        compTmEqOpen
          nonemptyNeNil
          (eqSubTmRule dBody lifted2Eq)
          (substOpenTm2 sigmaFits sigmaCFits dAσ dBσ dt)
          (λ rho fits2 ->
            let
              composedFitsEq = composeFitsEq fits2 lifted2Eq
              closedEq =
                subEq
                  (compSub rho (liftSubst (liftSubst sigma)))
                  (compSub rho (liftSubst (liftSubst tau)))
                  composedFitsEq
              body =
                subst
                  (λ J -> Computable J)
                  (sym
                    (cong₃ (termEq [])
                      (subTmComp rho (liftSubst (liftSubst sigma)) t)
                      (subTmComp rho (liftSubst (liftSubst tau)) t)
                      (subTyComp rho (liftSubst (liftSubst sigma)) T)))
                  (ClosedEqSubstComp.closedEqComp closedEq)
            in
            packClosedSubst fits2 body)
          (λ rho eta fitsEq2 ->
            let
              composedFitsEq = composeEqFitsEq fitsEq2 lifted2Eq
              closedEq =
                subEq
                  (compSub rho (liftSubst (liftSubst sigma)))
                  (compSub eta (liftSubst (liftSubst tau)))
                  composedFitsEq
              body =
                subst
                  (λ J -> Computable J)
                  (sym
                    (cong₃ (termEq [])
                      (subTmComp rho (liftSubst (liftSubst sigma)) t)
                      (subTmComp eta (liftSubst (liftSubst tau)) t)
                      (subTyComp rho (liftSubst (liftSubst sigma)) T)))
                  (ClosedEqSubstComp.closedEqComp closedEq)
            in
            packClosedEqSubst fitsEq2 body)

  eqSubOpenTmEq2 : {gamma : Ctx} {A B T : RawType} {t u : RawTerm} {sigma tau : Subst}
    -> FitsEqSubst [] gamma sigma tau
    -> CompFitsEqSubst gamma sigma tau
    -> Derivable (isType [] (subTy sigma A))
    -> Derivable (isType (subTy sigma A ∷ []) (subTy (liftSubst sigma) B))
    -> Computable (termEq (B ∷ A ∷ gamma) t u T)
    -> Computable
         (termEq (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ [])
           (subTm (liftSubst (liftSubst sigma)) t)
           (subTm (liftSubst (liftSubst tau)) u)
           (subTy (liftSubst (liftSubst sigma)) T))
  eqSubOpenTmEq2 {gamma = gamma} {A = A} {B = B} {T = T} {t = t} {u = u} {sigma = sigma} {tau = tau}
    fitsEq cFitsEq dAσ dBσ dtu =
    let
      sigmaCFits = compFitsEqLeft cFitsEq
      sigmaFits = compFitsToFits sigmaCFits
      lifted1Eq :
        FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma)
          (liftSubst sigma)
          (liftSubst tau)
      lifted1Eq =
        subst
          (λ rho -> FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma) rho (liftSubst tau))
          (liftSubstCompKeep sigma)
          (subst
            (λ rho ->
              FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma)
                (consSubst (var zero) (compSub (keepSubstBy 1) sigma))
                rho)
            (liftSubstCompKeep tau)
            (liftFitsEqOne fitsEq dAσ))
      lifted2Eq :
        FitsEqSubst (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) (B ∷ A ∷ gamma)
          (liftSubst (liftSubst sigma))
          (liftSubst (liftSubst tau))
      lifted2Eq =
        subst
          (λ rho ->
            FitsEqSubst (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) (B ∷ A ∷ gamma)
              rho
              (liftSubst (liftSubst tau)))
          (liftSubstCompKeep (liftSubst sigma))
          (subst
            (λ rho ->
              FitsEqSubst (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) (B ∷ A ∷ gamma)
                (consSubst (var zero) (compSub (keepSubstBy 1) (liftSubst sigma)))
                rho)
            (liftSubstCompKeep (liftSubst tau))
            (liftFitsEq lifted1Eq dBσ))
    in
    case dtu of λ where
      (compTmEqOpen neqBody dBody compTm sub subEq) ->
        compTmEqOpen
          nonemptyNeNil
          (eqSubTmEqRule dBody lifted2Eq)
          (substOpenTm2 sigmaFits sigmaCFits dAσ dBσ compTm)
          (λ rho fits2 ->
            let
              composedFitsEq = composeFitsEq fits2 lifted2Eq
              closedEq =
                subEq
                  (compSub rho (liftSubst (liftSubst sigma)))
                  (compSub rho (liftSubst (liftSubst tau)))
                  composedFitsEq
              body =
                subst
                  (λ J -> Computable J)
                  (sym
                    (cong₃ (termEq [])
                      (subTmComp rho (liftSubst (liftSubst sigma)) t)
                      (subTmComp rho (liftSubst (liftSubst tau)) u)
                      (subTyComp rho (liftSubst (liftSubst sigma)) T)))
                  (ClosedEqSubstComp.closedEqComp closedEq)
            in
            packClosedSubst fits2 body)
          (λ rho eta fitsEq2 ->
            let
              composedFitsEq = composeEqFitsEq fitsEq2 lifted2Eq
              closedEq =
                subEq
                  (compSub rho (liftSubst (liftSubst sigma)))
                  (compSub eta (liftSubst (liftSubst tau)))
                  composedFitsEq
              body =
                subst
                  (λ J -> Computable J)
                  (sym
                    (cong₃ (termEq [])
                      (subTmComp rho (liftSubst (liftSubst sigma)) t)
                      (subTmComp eta (liftSubst (liftSubst tau)) u)
                      (subTyComp rho (liftSubst (liftSubst sigma)) T)))
                  (ClosedEqSubstComp.closedEqComp closedEq)
            in
            packClosedEqSubst fitsEq2 body)

  substDerivTyComp : {gamma : Ctx} {A : RawType} {sigma : Subst}
    -> Derivable (isType gamma A)
    -> FitsSubst [] gamma sigma
    -> CompFitsSubst gamma sigma
    -> Computable (isType [] (subTy sigma A))
  substDerivTyComp (fTop wf) fits cFits = compFTopClosed
  substDerivTyComp {sigma = sigma} (fSigma {A = A} {B = B} dA dB) fits cFits =
    let
      compA = substDerivTyComp dA fits cFits
      dAσ = compToDerivable compA
      compB = substOpenTy1 fits cFits dAσ (openCompTy dB)
    in
    compFSigmaClosed compA compB
  substDerivTyComp (fEq dA da db) fits cFits =
    compFEqClosed
      (substDerivTyComp dA fits cFits)
      (substDerivTmComp da fits cFits)
      (substDerivTmComp db fits cFits)
  substDerivTyComp (fQtr dA) fits cFits =
    compFQtrClosed (substDerivTyComp dA fits cFits)
  substDerivTyComp {sigma = sigma} (weakenTy {delta = delta} {A = A} d wf) fits cFits =
    subst
      (λ T -> Computable (isType [] T))
      (sym (subTyWkBy sigma (length delta) A))
      (substDerivTyComp d (dropFits delta fits) (dropCompFits delta cFits))
  substDerivTyComp {sigma = sigma} (substTyRule {sigma = sigma'} {A = A} d fits') fits cFits =
    let
      composedFits = composeFits fits fits'
      composedCFits = composeCompFits fits' fits cFits
    in
    subst
      (λ T -> Computable (isType [] T))
      (sym (subTyComp sigma sigma' A))
      (substDerivTyComp d composedFits composedCFits)

  substDerivTyEqComp : {gamma : Ctx} {A B : RawType} {sigma : Subst}
    -> Derivable (typeEq gamma A B)
    -> FitsSubst [] gamma sigma
    -> CompFitsSubst gamma sigma
    -> Computable (typeEq [] (subTy sigma A) (subTy sigma B))
  substDerivTyEqComp (reflTy d) fits cFits =
    compReflTy (substDerivTyComp d fits cFits)
  substDerivTyEqComp (symTy d) fits cFits =
    compSymTyClosed (substDerivTyEqComp d fits cFits)
  substDerivTyEqComp (transTy d₁ d₂) fits cFits =
    compTransTyClosed (substDerivTyEqComp d₁ fits cFits) (substDerivTyEqComp d₂ fits cFits)
  substDerivTyEqComp {sigma = sigma} (fSigmaEq {A = A} {B = B} {D = D} dAC dBD) fits cFits =
    let
      compAC = substDerivTyEqComp dAC fits cFits
      compA = compTyEqLeft compAC
      compC = compTyEqRight compAC
      dAσ = compToDerivable compA
      compBD =
        substOpenTyEq1 fits cFits dAσ (openCompTyEq dBD)
      compSigmaA = compFSigmaClosed compA (compTyEqLeft compBD)
      compSigmaC = compFSigmaClosed compC (compTransportFamilyTy compAC (compTyEqRight compBD))
    in
    compTyEqClosedSigma
      (fSigmaEq (compToDerivable compAC) (compToDerivable compBD))
      compSigmaA
      compSigmaC
      evalSigma
      evalSigma
      compAC
      compBD
  substDerivTyEqComp (fEqEq dAC dac dbd) fits cFits =
    let
      compAC = substDerivTyEqComp dAC fits cFits
      compac = substDerivTmEqComp dac fits cFits
      compbd = substDerivTmEqComp dbd fits cFits
      compA = compTyEqLeft compAC
      compC = compTyEqRight compAC
      compa = compTmEqLeft compac
      compb = compTmEqLeft compbd
      compcA = compTmEqRightClosed compac
      compdA = compTmEqRightClosed compbd
      compc = compConvTmClosed compcA compAC
      compd = compConvTmClosed compdA compAC
      compEqA = compFEqClosed compA compa compb
      compEqC = compFEqClosed compC compc compd
    in
    compTyEqClosedEq
      (fEqEq (compToDerivable compAC) (compToDerivable compac) (compToDerivable compbd))
      compEqA
      compEqC
      evalEq
      evalEq
      compAC
      compac
      compbd
  substDerivTyEqComp (fQtrEq dAB) fits cFits =
    let
      compAB = substDerivTyEqComp dAB fits cFits
    in
    compTyEqClosedQtr
      (fQtrEq (compToDerivable compAB))
      (compFQtrClosed (compTyEqLeft compAB))
      (compFQtrClosed (compTyEqRight compAB))
      evalQtr
      evalQtr
      compAB
  substDerivTyEqComp {sigma = sigma} (weakenTyEq {delta = delta} {A = A} {B = B} d wf) fits cFits =
    subst
      (λ J -> Computable J)
      (cong₂ (typeEq [])
        (sym (subTyWkBy sigma (length delta) A))
        (sym (subTyWkBy sigma (length delta) B)))
      (substDerivTyEqComp d (dropFits delta fits) (dropCompFits delta cFits))
  substDerivTyEqComp {sigma = sigma} (substTyEqRule {sigma = sigma'} {A = A} {B = B} d fits') fits cFits =
    let
      composedFits = composeFits fits fits'
      composedCFits = composeCompFits fits' fits cFits
    in
    subst
      (λ J -> Computable J)
      (cong₂ (typeEq [])
        (sym (subTyComp sigma sigma' A))
        (sym (subTyComp sigma sigma' B)))
      (substDerivTyEqComp d composedFits composedCFits)
  substDerivTyEqComp {sigma = sigma} (eqSubTyRule {sigma = sigma'} {tau = tau'} {A = A} d fitsEq') fits cFits =
    let
      composedFitsEq = composeFitsEq fits fitsEq'
      composedCFitsEq = composeCompFitsEq fits cFits fitsEq'
    in
    subst
      (λ J -> Computable J)
      (cong₂ (typeEq [])
        (sym (subTyComp sigma sigma' A))
        (sym (subTyComp sigma tau' A)))
      (eqSubDerivTyComp d composedFitsEq composedCFitsEq)
  substDerivTyEqComp {sigma = sigma} (eqSubTyEqRule {sigma = sigma'} {tau = tau'} {A = A} {B = B} d fitsEq') fits cFits =
    let
      composedFitsEq = composeFitsEq fits fitsEq'
      composedCFitsEq = composeCompFitsEq fits cFits fitsEq'
    in
    subst
      (λ J -> Computable J)
      (cong₂ (typeEq [])
        (sym (subTyComp sigma sigma' A))
        (sym (subTyComp sigma tau' B)))
      (eqSubDerivTyEqComp d composedFitsEq composedCFitsEq)

  substDerivTmComp : {gamma : Ctx} {t : RawTerm} {A : RawType} {sigma : Subst}
    -> Derivable (hasTy gamma t A)
    -> FitsSubst [] gamma sigma
    -> CompFitsSubst gamma sigma
    -> Computable (hasTy [] (subTm sigma t) (subTy sigma A))
  substDerivTmCompESigma : {gamma : Ctx} {A B M : RawType} {d m : RawTerm} {sigma : Subst}
    -> Derivable (isType ((tySigma A B) ∷ gamma) M)
    -> Derivable (hasTy gamma d (tySigma A B))
    -> Derivable (hasTy (B ∷ A ∷ gamma) m (sigmaBranchTy M))
    -> FitsSubst [] gamma sigma
    -> CompFitsSubst gamma sigma
    -> Computable (hasTy [] (subTm sigma (tmElSigma d m)) (subTy sigma (subTy (singleSubst d) M)))
  substDerivTmCompESigma {gamma = gamma} {A = A} {B = B} {M = M} {d = d} {m = m} {sigma = sigma} dM dd dm fits cFits =
    let
      compdd = substDerivTmComp dd fits cFits
      compSigma = compTmToCompTy compdd
      dSigmaσ = compToDerivable compSigma
      tyInv = invertSigmaTy compSigma evalSigma
      compAσ = ClosedSigmaTyInv.sigmaTyCompHead tyInv
      compBσ = ClosedSigmaTyInv.sigmaTyCompFam tyInv
      dAσ = compToDerivable compAσ
      dBσ = compToDerivable compBσ
      compM = substOpenTy1 fits cFits dSigmaσ (openCompTy dM)

      lifted1 : FitsSubst (subTy sigma A ∷ []) (A ∷ gamma) (liftSubst sigma)
      lifted1 =
        subst
          (λ rho -> FitsSubst (subTy sigma A ∷ []) (A ∷ gamma) rho)
          (liftSubstCompKeep sigma)
          (liftFitsOne fits dAσ)

      lifted2 =
        subst
          (λ rho ->
            FitsSubst (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) (B ∷ A ∷ gamma) rho)
          (liftSubstCompKeep (liftSubst sigma))
          (liftFits lifted1 dBσ)

      compdm =
        subst
          (λ J -> Computable J)
          (cong
            (hasTy (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ [])
              (subTm (liftSubst (liftSubst sigma)) m))
            (sigmaBranchTyLiftComp sigma M))
          (substOpenTm2 fits cFits dAσ dBσ (openCompTm dm))

      resultPath :
        hasTy [] (subTm sigma (tmElSigma d m)) (subTy sigma (subTy (singleSubst d) M))
          ≡
        hasTy []
          (tmElSigma (subTm sigma d) (subTm (liftSubst (liftSubst sigma)) m))
          (subTy (singleSubst (subTm sigma d)) (subTy (liftSubst sigma) M))
      resultPath =
        cong₂
          (hasTy [])
          refl
          (subTyComp sigma (singleSubst d) M
            ∙ cong (λ rho -> subTy rho M) (sym (singleSubstCompLift sigma d))
            ∙ sym (subTyComp (singleSubst (subTm sigma d)) (liftSubst sigma) M))
    in
    subst
      (λ J -> Computable J)
      (sym resultPath)
      (compTmEqLeft (compESigmaClosed compM (compReflTm compdd) (compReflTm compdm)))

  substDerivTmCompEQtr
    : {gamma : Ctx} {A L : RawType} {l p : RawTerm} {sigma : Subst}
    -> Derivable (isType ((tyQtr A) ∷ gamma) L)
    -> Derivable (hasTy gamma p (tyQtr A))
    -> Derivable (hasTy (A ∷ gamma) l (qtrBranchTy L))
    -> Derivable
         (termEq (wkTyBy 1 A ∷ A ∷ gamma)
           (wkTmBy 1 l)
           (renTm qtrSecondBranchRen l)
           (qtrCohTy L))
    -> FitsSubst [] gamma sigma
    -> CompFitsSubst gamma sigma
    -> Computable
         (hasTy [] (subTm sigma (tmElQtr l p))
           (subTy sigma (subTy (singleSubst p) L)))
  substDerivTmCompEQtr
    {gamma = gamma} {A = A} {L = L} {l = l} {p = p} {sigma = sigma}
    dL dp dl dcoh fits cFits =
    let
      compdp = substDerivTmComp dp fits cFits
      compQtrσ = compTmToCompTy compdp
      dQtrσ = compToDerivable compQtrσ
      tyInv = invertQtrTy compQtrσ evalQtr
      compAσ = ClosedQtrTyInv.qtrTyCompBase tyInv
      dAσ = compToDerivable compAσ
      dWkAσ =
        subst
          (λ T -> Derivable (isType (subTy sigma A ∷ []) T))
          (sym (wkTyLiftSubst sigma A))
          (weakenTy dAσ (wfCons wfNil dAσ))

      compL = substOpenTy1 fits cFits dQtrσ (openCompTy dL)

      compl =
        subst
          (λ T ->
            Computable
              (hasTy (subTy sigma A ∷ [])
                (subTm (liftSubst sigma) l)
                T))
          (qtrBranchTyLiftComp sigma L)
          (substOpenTm1 fits cFits dAσ (openCompTm dl))

      compcoh =
        subst
          (λ J -> Computable J)
          (cong
            (λ T ->
              termEq (T ∷ subTy sigma A ∷ [])
                (subTm (liftSubst (liftSubst sigma)) (wkTmBy 1 l))
                (subTm (liftSubst (liftSubst sigma)) (renTm qtrSecondBranchRen l))
                (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
            (wkTyLiftSubst sigma A)
            ∙ cong
                (λ t ->
                  termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                    t
                    (subTm (liftSubst (liftSubst sigma)) (renTm qtrSecondBranchRen l))
                    (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
                (wkTmLiftSubst (liftSubst sigma) l)
            ∙ cong
                (λ u ->
                  termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                    (wkTmBy 1 (subTm (liftSubst sigma) l))
                    u
                    (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
                (qtrSecondBranchTmLiftComp sigma l)
            ∙ cong
                (λ T ->
                  termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                    (wkTmBy 1 (subTm (liftSubst sigma) l))
                    (renTm qtrSecondBranchRen (subTm (liftSubst sigma) l))
                    T)
                (qtrCohTyLiftComp sigma L))
          (substOpenTmEq2 fits cFits dAσ dWkAσ (openCompTmEq dcoh))

      resultPath :
        hasTy []
          (subTm sigma (tmElQtr l p))
          (subTy sigma (subTy (singleSubst p) L))
          ≡
        hasTy []
          (tmElQtr (subTm (liftSubst sigma) l) (subTm sigma p))
          (subTy (singleSubst (subTm sigma p)) (subTy (liftSubst sigma) L))
      resultPath =
        cong₂
          (hasTy [])
          refl
          (subTyComp sigma (singleSubst p) L
            ∙ cong (λ rho -> subTy rho L) (sym (singleSubstCompLift sigma p))
            ∙ sym (subTyComp (singleSubst (subTm sigma p)) (liftSubst sigma) L))
    in
    subst
      (λ J -> Computable J)
      (sym resultPath)
      (compTmEqLeft
        (compEQtrClosed
          compL
          (compReflTm compdp)
          (compReflTm compl)
          compcoh
          compcoh))

  substDerivTmComp (varStar {delta = delta} {A = A} wf dA) fits cFits =
    lookupCompFits {delta = delta} {A = A} cFits
  substDerivTmComp (iTop wf) fits cFits = compITopClosed
  substDerivTmComp {sigma = sigma}
    (iSigma {a = a} {b = b} {A = A} {B = B} da db dSigma) fits cFits =
    let
      compa = substDerivTmComp da fits cFits
      compb =
        subst
          (λ T -> Computable (hasTy [] (subTm sigma b) T))
          (subTyComp sigma (singleSubst a) B
            ∙ cong (λ rho -> subTy rho B) (sym (singleSubstCompLift sigma a))
            ∙ sym (subTyComp (singleSubst (subTm sigma a)) (liftSubst sigma) B))
          (substDerivTmComp db fits cFits)
    in
    compISigmaClosed compa compb (substDerivTyComp dSigma fits cFits)
  substDerivTmComp (iEq da) fits cFits =
    compIEqClosed (substDerivTmComp da fits cFits)
  substDerivTmComp (iQtr da) fits cFits =
    compIQtrClosed (substDerivTmComp da fits cFits)
  substDerivTmComp (eSigma dM dd dm) fits cFits =
    substDerivTmCompESigma dM dd dm fits cFits
  substDerivTmComp (eQtr dL dp dl dcoh) fits cFits =
    substDerivTmCompEQtr dL dp dl dcoh fits cFits
  substDerivTmComp (conv d dAB) fits cFits =
    compConvTmClosed (substDerivTmComp d fits cFits) (substDerivTyEqComp dAB fits cFits)
  substDerivTmComp {sigma = sigma} (weakenTm {delta = delta} {t = t} {A = A} d wf) fits cFits =
    subst
      (λ J -> Computable J)
      (cong₂ (hasTy [])
        (sym (subTmWkBy sigma (length delta) t))
        (sym (subTyWkBy sigma (length delta) A)))
      (substDerivTmComp d (dropFits delta fits) (dropCompFits delta cFits))
  substDerivTmComp {sigma = sigma} (substTmRule {sigma = sigma'} {t = t} {A = A} d fits') fits cFits =
    let
      composedFits = composeFits fits fits'
      composedCFits = composeCompFits fits' fits cFits
    in
    subst
      (λ J -> Computable J)
      (cong₂ (hasTy [])
        (sym (subTmComp sigma sigma' t))
        (sym (subTyComp sigma sigma' A)))
      (substDerivTmComp d composedFits composedCFits)
  substDerivTmEqComp : {gamma : Ctx} {t u : RawTerm} {A : RawType} {sigma : Subst}
    -> Derivable (termEq gamma t u A)
    -> FitsSubst [] gamma sigma
    -> CompFitsSubst gamma sigma
    -> Computable (termEq [] (subTm sigma t) (subTm sigma u) (subTy sigma A))
  substDerivTmEqCompESigmaEq
    : {gamma : Ctx} {A B M : RawType} {d d' m m' : RawTerm} {sigma : Subst}
    -> Derivable (isType ((tySigma A B) ∷ gamma) M)
    -> Derivable (termEq gamma d d' (tySigma A B))
    -> Derivable (termEq (B ∷ A ∷ gamma) m m' (sigmaBranchTy M))
    -> FitsSubst [] gamma sigma
    -> CompFitsSubst gamma sigma
    -> Computable
         (termEq []
           (subTm sigma (tmElSigma d m))
           (subTm sigma (tmElSigma d' m'))
           (subTy sigma (subTy (singleSubst d) M)))
  substDerivTmEqCompESigmaEq
    {gamma = gamma} {A = A} {B = B} {M = M} {d = d} {d' = d'} {m = m} {m' = m'} {sigma = sigma}
    dM dd dm fits cFits =
    let
      compdd = substDerivTmEqComp dd fits cFits
      compSigma = compTmToCompTy (compTmEqLeft compdd)
      dSigmaσ = compToDerivable compSigma
      tyInv = invertSigmaTy compSigma evalSigma
      compAσ = ClosedSigmaTyInv.sigmaTyCompHead tyInv
      compBσ = ClosedSigmaTyInv.sigmaTyCompFam tyInv
      dAσ = compToDerivable compAσ
      dBσ = compToDerivable compBσ
      compM = substOpenTy1 fits cFits dSigmaσ (openCompTy dM)

      lifted1 =
        subst
          (λ rho -> FitsSubst (subTy sigma A ∷ []) (A ∷ gamma) rho)
          (liftSubstCompKeep sigma)
          (liftFitsOne fits dAσ)

      lifted2 =
        subst
          (λ rho ->
            FitsSubst (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) (B ∷ A ∷ gamma) rho)
          (liftSubstCompKeep (liftSubst sigma))
          (liftFits lifted1 dBσ)

      compdm =
        subst
          (λ J -> Computable J)
          (cong
            (termEq (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ [])
              (subTm (liftSubst (liftSubst sigma)) m)
              (subTm (liftSubst (liftSubst sigma)) m'))
            (sigmaBranchTyLiftComp sigma M))
          (substOpenTmEq2 fits cFits dAσ dBσ (openCompTmEq dm))

      resultPath :
        termEq []
          (subTm sigma (tmElSigma d m))
          (subTm sigma (tmElSigma d' m'))
          (subTy sigma (subTy (singleSubst d) M))
          ≡
        termEq []
          (tmElSigma (subTm sigma d) (subTm (liftSubst (liftSubst sigma)) m))
          (tmElSigma (subTm sigma d') (subTm (liftSubst (liftSubst sigma)) m'))
          (subTy (singleSubst (subTm sigma d)) (subTy (liftSubst sigma) M))
      resultPath =
        cong₃
          (termEq [])
          refl
          refl
          (subTyComp sigma (singleSubst d) M
            ∙ cong (λ rho -> subTy rho M) (sym (singleSubstCompLift sigma d))
            ∙ sym (subTyComp (singleSubst (subTm sigma d)) (liftSubst sigma) M))
    in
    subst
      (λ J -> Computable J)
      (sym resultPath)
      (compESigmaClosed compM compdd compdm)

  substDerivTmEqCompEQtrEq
    : {gamma : Ctx} {A L : RawType} {l l' p p' : RawTerm} {sigma : Subst}
    -> Derivable (isType ((tyQtr A) ∷ gamma) L)
    -> Derivable (termEq gamma p p' (tyQtr A))
    -> Derivable (termEq (A ∷ gamma) l l' (qtrBranchTy L))
    -> Derivable
         (termEq (wkTyBy 1 A ∷ A ∷ gamma)
           (wkTmBy 1 l)
           (renTm qtrSecondBranchRen l)
           (qtrCohTy L))
    -> Derivable
         (termEq (wkTyBy 1 A ∷ A ∷ gamma)
           (wkTmBy 1 l')
           (renTm qtrSecondBranchRen l')
           (qtrCohTy L))
    -> FitsSubst [] gamma sigma
    -> CompFitsSubst gamma sigma
    -> Computable
         (termEq []
           (subTm sigma (tmElQtr l p))
           (subTm sigma (tmElQtr l' p'))
           (subTy sigma (subTy (singleSubst p) L)))
  substDerivTmEqCompEQtrEq
    {gamma = gamma} {A = A} {L = L} {l = l} {l' = l'} {p = p} {p' = p'} {sigma = sigma}
    dL dp dl dcoh dcoh' fits cFits =
    let
      compdp = substDerivTmEqComp dp fits cFits
      compQtrσ = compTmToCompTy (compTmEqLeft compdp)
      dQtrσ = compToDerivable compQtrσ
      tyInv = invertQtrTy compQtrσ evalQtr
      compAσ = ClosedQtrTyInv.qtrTyCompBase tyInv
      dAσ = compToDerivable compAσ
      dWkAσ =
        subst
          (λ T -> Derivable (isType (subTy sigma A ∷ []) T))
          (sym (wkTyLiftSubst sigma A))
          (weakenTy dAσ (wfCons wfNil dAσ))

      compL = substOpenTy1 fits cFits dQtrσ (openCompTy dL)

      compl =
        subst
          (λ T ->
            Computable
              (termEq (subTy sigma A ∷ [])
                (subTm (liftSubst sigma) l)
                (subTm (liftSubst sigma) l')
                T))
          (qtrBranchTyLiftComp sigma L)
          (substOpenTmEq1 fits cFits dAσ (openCompTmEq dl))

      compcoh =
        subst
          (λ J -> Computable J)
          (cong
            (λ T ->
              termEq (T ∷ subTy sigma A ∷ [])
                (subTm (liftSubst (liftSubst sigma)) (wkTmBy 1 l))
                (subTm (liftSubst (liftSubst sigma)) (renTm qtrSecondBranchRen l))
                (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
            (wkTyLiftSubst sigma A)
            ∙ cong
                (λ t ->
                  termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                    t
                    (subTm (liftSubst (liftSubst sigma)) (renTm qtrSecondBranchRen l))
                    (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
                (wkTmLiftSubst (liftSubst sigma) l)
            ∙ cong
                (λ u ->
                  termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                    (wkTmBy 1 (subTm (liftSubst sigma) l))
                    u
                    (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
                (qtrSecondBranchTmLiftComp sigma l)
            ∙ cong
                (λ T ->
                  termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                    (wkTmBy 1 (subTm (liftSubst sigma) l))
                    (renTm qtrSecondBranchRen (subTm (liftSubst sigma) l))
                    T)
                (qtrCohTyLiftComp sigma L))
          (substOpenTmEq2 fits cFits dAσ dWkAσ (openCompTmEq dcoh))

      compcoh' =
        subst
          (λ J -> Computable J)
          (cong
            (λ T ->
              termEq (T ∷ subTy sigma A ∷ [])
                (subTm (liftSubst (liftSubst sigma)) (wkTmBy 1 l'))
                (subTm (liftSubst (liftSubst sigma)) (renTm qtrSecondBranchRen l'))
                (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
            (wkTyLiftSubst sigma A)
            ∙ cong
                (λ t ->
                  termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                    t
                    (subTm (liftSubst (liftSubst sigma)) (renTm qtrSecondBranchRen l'))
                    (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
                (wkTmLiftSubst (liftSubst sigma) l')
            ∙ cong
                (λ u ->
                  termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                    (wkTmBy 1 (subTm (liftSubst sigma) l'))
                    u
                    (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
                (qtrSecondBranchTmLiftComp sigma l')
            ∙ cong
                (λ T ->
                  termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                    (wkTmBy 1 (subTm (liftSubst sigma) l'))
                    (renTm qtrSecondBranchRen (subTm (liftSubst sigma) l'))
                    T)
                (qtrCohTyLiftComp sigma L))
          (substOpenTmEq2 fits cFits dAσ dWkAσ (openCompTmEq dcoh'))

      resultPath :
        termEq []
          (subTm sigma (tmElQtr l p))
          (subTm sigma (tmElQtr l' p'))
          (subTy sigma (subTy (singleSubst p) L))
          ≡
        termEq []
          (tmElQtr (subTm (liftSubst sigma) l) (subTm sigma p))
          (tmElQtr (subTm (liftSubst sigma) l') (subTm sigma p'))
          (subTy (singleSubst (subTm sigma p)) (subTy (liftSubst sigma) L))
      resultPath =
        cong₃
          (termEq [])
          refl
          refl
          (subTyComp sigma (singleSubst p) L
            ∙ cong (λ rho -> subTy rho L) (sym (singleSubstCompLift sigma p))
            ∙ sym (subTyComp (singleSubst (subTm sigma p)) (liftSubst sigma) L))
    in
    subst
      (λ J -> Computable J)
      (sym resultPath)
      (compEQtrClosed compL compdp compl compcoh compcoh')

  substDerivTmEqCompCQtr
    : {gamma : Ctx} {A L : RawType} {a l : RawTerm} {sigma : Subst}
    -> Derivable (isType ((tyQtr A) ∷ gamma) L)
    -> Derivable (hasTy gamma a A)
    -> Derivable (hasTy (A ∷ gamma) l (qtrBranchTy L))
    -> Derivable
         (termEq (wkTyBy 1 A ∷ A ∷ gamma)
           (wkTmBy 1 l)
           (renTm qtrSecondBranchRen l)
           (qtrCohTy L))
    -> FitsSubst [] gamma sigma
    -> CompFitsSubst gamma sigma
    -> Computable
         (termEq []
           (subTm sigma (tmElQtr l (tmClass a)))
           (subTm sigma (subTm (qtrCompSub a) l))
           (subTy sigma (subTy (singleSubst (tmClass a)) L)))
  substDerivTmEqCompCQtr
    {gamma = gamma} {A = A} {L = L} {a = a} {l = l} {sigma = sigma}
    dL da dl dcoh fits cFits =
    let
      compa = substDerivTmComp da fits cFits
      compAσ = compTmToCompTy compa
      dAσ = compToDerivable compAσ
      dQtrσ = compToDerivable (compFQtrClosed compAσ)
      dWkAσ =
        subst
          (λ T -> Derivable (isType (subTy sigma A ∷ []) T))
          (sym (wkTyLiftSubst sigma A))
          (weakenTy dAσ (wfCons wfNil dAσ))

      compL = substOpenTy1 fits cFits dQtrσ (openCompTy dL)

      compl =
        subst
          (λ T ->
            Computable
              (hasTy (subTy sigma A ∷ [])
                (subTm (liftSubst sigma) l)
                T))
          (qtrBranchTyLiftComp sigma L)
          (substOpenTm1 fits cFits dAσ (openCompTm dl))

      compcoh =
        subst
          (λ J -> Computable J)
          (cong
            (λ T ->
              termEq (T ∷ subTy sigma A ∷ [])
                (subTm (liftSubst (liftSubst sigma)) (wkTmBy 1 l))
                (subTm (liftSubst (liftSubst sigma)) (renTm qtrSecondBranchRen l))
                (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
            (wkTyLiftSubst sigma A)
            ∙ cong
                (λ t ->
                  termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                    t
                    (subTm (liftSubst (liftSubst sigma)) (renTm qtrSecondBranchRen l))
                    (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
                (wkTmLiftSubst (liftSubst sigma) l)
            ∙ cong
                (λ u ->
                  termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                    (wkTmBy 1 (subTm (liftSubst sigma) l))
                    u
                    (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
                (qtrSecondBranchTmLiftComp sigma l)
            ∙ cong
                (λ T ->
                  termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                    (wkTmBy 1 (subTm (liftSubst sigma) l))
                    (renTm qtrSecondBranchRen (subTm (liftSubst sigma) l))
                    T)
                (qtrCohTyLiftComp sigma L))
          (substOpenTmEq2 fits cFits dAσ dWkAσ (openCompTmEq dcoh))

      resultPath :
        termEq []
          (subTm sigma (tmElQtr l (tmClass a)))
          (subTm sigma (subTm (qtrCompSub a) l))
          (subTy sigma (subTy (singleSubst (tmClass a)) L))
          ≡
        termEq []
          (tmElQtr (subTm (liftSubst sigma) l) (tmClass (subTm sigma a)))
          (subTm (qtrCompSub (subTm sigma a)) (subTm (liftSubst sigma) l))
          (subTy (singleSubst (tmClass (subTm sigma a))) (subTy (liftSubst sigma) L))
      resultPath =
        cong₃
          (termEq [])
          refl
          (subTmComp sigma (qtrCompSub a) l
            ∙ cong (λ rho -> subTm rho l) (qtrCompSubLiftComp sigma a)
            ∙ sym (subTmComp (qtrCompSub (subTm sigma a)) (liftSubst sigma) l))
          (subTyComp sigma (singleSubst (tmClass a)) L
            ∙ cong (λ rho -> subTy rho L) (sym (singleSubstCompLift sigma (tmClass a)))
            ∙ sym (subTyComp (singleSubst (tmClass (subTm sigma a))) (liftSubst sigma) L))
    in
    subst
      (λ J -> Computable J)
      (sym resultPath)
      (compCQtrClosed compL compa compl compcoh)

  substDerivTmEqComp (reflTm d) fits cFits =
    compReflTmClosed (substDerivTmComp d fits cFits)
  substDerivTmEqComp (symTm d) fits cFits =
    compSymTmClosed (substDerivTmEqComp d fits cFits)
  substDerivTmEqComp (transTm d₁ d₂) fits cFits =
    compTransTmClosed (substDerivTmEqComp d₁ fits cFits) (substDerivTmEqComp d₂ fits cFits)
  substDerivTmEqComp (convEq d dAB) fits cFits =
    compConvTmEqClosed (substDerivTmEqComp d fits cFits) (substDerivTyEqComp dAB fits cFits)
  substDerivTmEqComp (cTop d) fits cFits =
    compCTopClosed (substDerivTmComp d fits cFits)
  substDerivTmEqComp {sigma = sigma}
    (iSigmaEq {a = a} {b = b} {d = d} {A = A} {B = B} dac dbd dA dB) fits cFits =
    let
      compac = substDerivTmEqComp dac fits cFits
      compbdRaw = substDerivTmEqComp dbd fits cFits
      compA = substDerivTyComp dA fits cFits
      dAσ = compToDerivable compA
      compB = substOpenTy1 fits cFits dAσ (openCompTy dB)
      compa = compTmEqLeft compac
      compcA = compTmEqRightClosed compac
      compbd =
        subst
          (λ T -> Computable (termEq [] (subTm sigma b) (subTm sigma d) T))
          (subTyComp sigma (singleSubst a) B
            ∙ cong (λ rho -> subTy rho B) (sym (singleSubstCompLift sigma a))
            ∙ sym (subTyComp (singleSubst (subTm sigma a)) (liftSubst sigma) B))
          compbdRaw
      compb = compTmEqLeft compbd
      compdA = compTmEqRightClosed compbd
      compd =
        compConvTmClosed compdA (compSingleEqSubstTyClosed compB compac)
      compPairLeft = compISigmaClosed compa compb (compFSigmaClosed compA compB)
      compPairRight = compISigmaClosed compcA compd (compFSigmaClosed compA compB)
    in
    compTmEqClosedSigma
      (iSigmaEq (compToDerivable compac) (compToDerivable compbd) dAσ (compToDerivable compB))
      compPairLeft
      compPairRight
      evalSigma
      evalPair
      evalPair
      compac
      compbd
  substDerivTmEqComp (eSigmaEq dM dd dm) fits cFits =
    substDerivTmEqCompESigmaEq dM dd dm fits cFits
  substDerivTmEqComp (eQtrEq dL dp dl dcoh dcoh') fits cFits =
    substDerivTmEqCompEQtrEq dL dp dl dcoh dcoh' fits cFits
  substDerivTmEqComp {gamma = gamma} {sigma = sigma}
    (cSigma {A = A} {B = B} {M = M} {b = b} {c = c} {m = m} dM db dc dm) fits cFits =
    let
      compb = substDerivTmComp db fits cFits
      sigmaTy = ctxSuffixTy {delta = []} {gamma = gamma} {A = tySigma A B} (derivToCtxWF dM)
      compSigma = substDerivTyComp sigmaTy fits cFits
      dSigmaσ = compToDerivable compSigma
      tyInv = invertSigmaTy compSigma evalSigma
      compAσ = ClosedSigmaTyInv.sigmaTyCompHead tyInv
      compBσ = ClosedSigmaTyInv.sigmaTyCompFam tyInv
      dAσ = compToDerivable compAσ
      dBσ = compToDerivable compBσ
      compM = substOpenTy1 fits cFits dSigmaσ (openCompTy dM)

      lifted1 =
        subst
          (λ rho -> FitsSubst (subTy sigma A ∷ []) (A ∷ gamma) rho)
          (liftSubstCompKeep sigma)
          (liftFitsOne fits dAσ)

      lifted2 =
        subst
          (λ rho ->
            FitsSubst (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) (B ∷ A ∷ gamma) rho)
          (liftSubstCompKeep (liftSubst sigma))
          (liftFits lifted1 dBσ)

      compdm =
        subst
          (λ J -> Computable J)
          (cong
            (hasTy (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ [])
              (subTm (liftSubst (liftSubst sigma)) m))
            (sigmaBranchTyLiftComp sigma M))
          (substOpenTm2 fits cFits dAσ dBσ (openCompTm dm))

      compcRaw = substDerivTmComp dc fits cFits
      compc =
        subst
          (λ T -> Computable (hasTy [] (subTm sigma c) T))
          (subTyComp sigma (singleSubst b) B
            ∙ cong (λ rho -> subTy rho B) (sym (singleSubstCompLift sigma b))
            ∙ sym (subTyComp (singleSubst (subTm sigma b)) (liftSubst sigma) B))
          compcRaw

      resultPath :
        termEq []
          (subTm sigma (tmElSigma (tmPair b c) m))
          (subTm sigma (subTm (sigmaCompSub b c) m))
          (subTy sigma (subTy (singleSubst (tmPair b c)) M))
          ≡
        termEq []
          (tmElSigma (tmPair (subTm sigma b) (subTm sigma c))
            (subTm (liftSubst (liftSubst sigma)) m))
          (subTm (sigmaCompSub (subTm sigma b) (subTm sigma c))
            (subTm (liftSubst (liftSubst sigma)) m))
          (subTy (singleSubst (tmPair (subTm sigma b) (subTm sigma c)))
            (subTy (liftSubst sigma) M))
      resultPath =
        cong₃
          (termEq [])
          refl
          (subTmComp sigma (sigmaCompSub b c) m
            ∙ cong (λ rho -> subTm rho m) (sigmaCompSubLiftComp sigma b c)
            ∙ sym (subTmComp (sigmaCompSub (subTm sigma b) (subTm sigma c))
                (liftSubst (liftSubst sigma)) m))
          (subTyComp sigma (singleSubst (tmPair b c)) M
            ∙ cong (λ rho -> subTy rho M) (sym (singleSubstCompLift sigma (tmPair b c)))
            ∙ sym (subTyComp (singleSubst (tmPair (subTm sigma b) (subTm sigma c)))
                (liftSubst sigma) M))
    in
    subst
      (λ J -> Computable J)
      (sym resultPath)
      (compCSigmaClosed compM compb compc compdm)
  substDerivTmEqComp (iEqEq d) fits cFits =
    compReflTm (compIEqClosed (compTmEqLeft (substDerivTmEqComp d fits cFits)))
  substDerivTmEqComp (eEqStar dp dA da db) fits cFits =
    compEEqClosed (substDerivTmComp dp fits cFits)
  substDerivTmEqComp (cEq dp dA da db) fits cFits =
    compCEqClosed (substDerivTmComp dp fits cFits)
  substDerivTmEqComp (iQtrEq da db) fits cFits =
    compIQtrEqClosed (substDerivTmComp da fits cFits) (substDerivTmComp db fits cFits)
  substDerivTmEqComp (cQtr dL da dl dcoh) fits cFits =
    substDerivTmEqCompCQtr dL da dl dcoh fits cFits
  substDerivTmEqComp {sigma = sigma} (weakenTmEq {delta = delta} {t = t} {u = u} {A = A} d wf) fits cFits =
    subst
      (λ J -> Computable J)
      (cong₃ (termEq [])
        (sym (subTmWkBy sigma (length delta) t))
        (sym (subTmWkBy sigma (length delta) u))
        (sym (subTyWkBy sigma (length delta) A)))
      (substDerivTmEqComp d (dropFits delta fits) (dropCompFits delta cFits))
  substDerivTmEqComp {sigma = sigma} (substTmEqRule {sigma = sigma'} {t = t} {u = u} {A = A} d fits') fits cFits =
    let
      composedFits = composeFits fits fits'
      composedCFits = composeCompFits fits' fits cFits
    in
    subst
      (λ J -> Computable J)
      (cong₃ (termEq [])
        (sym (subTmComp sigma sigma' t))
        (sym (subTmComp sigma sigma' u))
        (sym (subTyComp sigma sigma' A)))
      (substDerivTmEqComp d composedFits composedCFits)
  substDerivTmEqComp {sigma = sigma}
    (eqSubTmRule {sigma = sigma'} {tau = tau'} {t = t} {A = A} d fitsEq') fits cFits =
    let
      composedFitsEq = composeFitsEq fits fitsEq'
      composedCFitsEq = composeCompFitsEq fits cFits fitsEq'
    in
    subst
      (λ J -> Computable J)
      (cong₃ (termEq [])
        (sym (subTmComp sigma sigma' t))
        (sym (subTmComp sigma tau' t))
        (sym (subTyComp sigma sigma' A)))
      (eqSubDerivTmComp d composedFitsEq composedCFitsEq)
  substDerivTmEqComp {sigma = sigma}
    (eqSubTmEqRule {sigma = sigma'} {tau = tau'} {t = t} {u = u} {A = A} d fitsEq') fits cFits =
    let
      composedFitsEq = composeFitsEq fits fitsEq'
      composedCFitsEq = composeCompFitsEq fits cFits fitsEq'
    in
    subst
      (λ J -> Computable J)
      (cong₃ (termEq [])
        (sym (subTmComp sigma sigma' t))
        (sym (subTmComp sigma tau' u))
        (sym (subTyComp sigma sigma' A)))
      (eqSubDerivTmEqComp d composedFitsEq composedCFitsEq)
  eqSubDerivTyComp : {gamma : Ctx} {A : RawType} {sigma tau : Subst}
    -> Derivable (isType gamma A)
    -> FitsEqSubst [] gamma sigma tau
    -> CompFitsEqSubst gamma sigma tau
    -> Computable (typeEq [] (subTy sigma A) (subTy tau A))
  eqSubDerivTyComp (fTop wf) fitsEq cFitsEq = compReflTy compFTopClosed
  eqSubDerivTyComp {sigma = sigma} {tau = tau}
    (fSigma {A = A} {B = B} dA dB) fitsEq cFitsEq =
    let
      compAA' = eqSubDerivTyComp dA fitsEq cFitsEq
      compA = compTyEqLeft compAA'
      compA' = compTyEqRight compAA'
      dAσ = compToDerivable compA
      compBD = eqSubOpenTy1 fitsEq cFitsEq dAσ (openCompTy dB)
      compSigmaA = compFSigmaClosed compA (compTyEqLeft compBD)
      compSigmaA' = compFSigmaClosed compA' (compTransportFamilyTy compAA' (compTyEqRight compBD))
    in
    compTyEqClosedSigma
      (fSigmaEq (compToDerivable compAA') (compToDerivable compBD))
      compSigmaA
      compSigmaA'
      evalSigma
      evalSigma
      compAA'
      compBD
  eqSubDerivTyComp (fEq dA da db) fitsEq cFitsEq =
    let
      compAA' = eqSubDerivTyComp dA fitsEq cFitsEq
      compac = eqSubDerivTmComp da fitsEq cFitsEq
      compbd = eqSubDerivTmComp db fitsEq cFitsEq
      compA = compTyEqLeft compAA'
      compA' = compTyEqRight compAA'
      compa = compTmEqLeft compac
      compb = compTmEqLeft compbd
      compcA = compTmEqRightClosed compac
      compdA = compTmEqRightClosed compbd
      compc = compConvTmClosed compcA compAA'
      compd = compConvTmClosed compdA compAA'
      compEqA = compFEqClosed compA compa compb
      compEqA' = compFEqClosed compA' compc compd
    in
    compTyEqClosedEq
      (fEqEq (compToDerivable compAA') (compToDerivable compac) (compToDerivable compbd))
      compEqA
      compEqA'
      evalEq
      evalEq
      compAA'
      compac
      compbd
  eqSubDerivTyComp (fQtr dA) fitsEq cFitsEq =
    let
      compAA' = eqSubDerivTyComp dA fitsEq cFitsEq
    in
    compTyEqClosedQtr
      (fQtrEq (compToDerivable compAA'))
      (compFQtrClosed (compTyEqLeft compAA'))
      (compFQtrClosed (compTyEqRight compAA'))
      evalQtr
      evalQtr
      compAA'
  eqSubDerivTyComp {sigma = sigma} {tau = tau}
    (weakenTy {delta = delta} {A = A} d wf) fitsEq cFitsEq =
    subst
      (λ J -> Computable J)
      (cong₂ (typeEq [])
        (sym (subTyWkBy sigma (length delta) A))
        (sym (subTyWkBy tau (length delta) A)))
      (eqSubDerivTyComp d (dropFitsEq delta fitsEq) (dropCompFitsEq delta cFitsEq))
  eqSubDerivTyComp {sigma = sigma} {tau = tau}
    (substTyRule {sigma = sigma'} {A = A} d fits') fitsEq cFitsEq =
    let
      composedFitsEq = composeEqFits fitsEq fits'
      composedCFitsEq = composeCompEqFits fitsEq cFitsEq fits'
    in
    subst
      (λ J -> Computable J)
      (cong₂ (typeEq [])
        (sym (subTyComp sigma sigma' A))
        (sym (subTyComp tau sigma' A)))
      (eqSubDerivTyComp d composedFitsEq composedCFitsEq)

  eqSubDerivTyEqComp : {gamma : Ctx} {A B : RawType} {sigma tau : Subst}
    -> Derivable (typeEq gamma A B)
    -> FitsEqSubst [] gamma sigma tau
    -> CompFitsEqSubst gamma sigma tau
    -> Computable (typeEq [] (subTy sigma A) (subTy tau B))
  eqSubDerivTyEqComp (reflTy d) fitsEq cFitsEq =
    eqSubDerivTyComp d fitsEq cFitsEq
  eqSubDerivTyEqComp (symTy d) fitsEq cFitsEq =
    let
      sigmaCFits = compFitsEqLeft cFitsEq
      sigmaFits = compFitsToFits sigmaCFits
    in
    compTransTyClosed
      (compSymTyClosed (substDerivTyEqComp d sigmaFits sigmaCFits))
      (eqSubDerivTyComp (assocTyLeft d) fitsEq cFitsEq)
  eqSubDerivTyEqComp (transTy d₁ d₂) fitsEq cFitsEq =
    let
      sigmaCFits = compFitsEqLeft cFitsEq
      sigmaFits = compFitsToFits sigmaCFits
    in
    compTransTyClosed
      (substDerivTyEqComp d₁ sigmaFits sigmaCFits)
      (eqSubDerivTyEqComp d₂ fitsEq cFitsEq)
  eqSubDerivTyEqComp {sigma = sigma} {tau = tau}
    (fSigmaEq {A = A} {B = B} {D = D} dAC dBD) fitsEq cFitsEq =
    let
      compAC = eqSubDerivTyEqComp dAC fitsEq cFitsEq
      compA = compTyEqLeft compAC
      compC = compTyEqRight compAC
      dAσ = compToDerivable compA
      compBD = eqSubOpenTyEq1 fitsEq cFitsEq dAσ (openCompTyEq dBD)
      compSigmaA = compFSigmaClosed compA (compTyEqLeft compBD)
      compSigmaC = compFSigmaClosed compC (compTransportFamilyTy compAC (compTyEqRight compBD))
    in
    compTyEqClosedSigma
      (fSigmaEq (compToDerivable compAC) (compToDerivable compBD))
      compSigmaA
      compSigmaC
      evalSigma
      evalSigma
      compAC
      compBD
  eqSubDerivTyEqComp {sigma = sigma} {tau = tau}
    (weakenTyEq {delta = delta} {A = A} {B = B} d wf) fitsEq cFitsEq =
    subst
      (λ J -> Computable J)
      (cong₂ (typeEq [])
        (sym (subTyWkBy sigma (length delta) A))
        (sym (subTyWkBy tau (length delta) B)))
      (eqSubDerivTyEqComp d (dropFitsEq delta fitsEq) (dropCompFitsEq delta cFitsEq))
  eqSubDerivTyEqComp {sigma = sigma} {tau = tau}
    (substTyEqRule {sigma = sigma'} {A = A} {B = B} d fits') fitsEq cFitsEq =
    let
      composedFitsEq = composeEqFits fitsEq fits'
      composedCFitsEq = composeCompEqFits fitsEq cFitsEq fits'
    in
    subst
      (λ J -> Computable J)
      (cong₂ (typeEq [])
        (sym (subTyComp sigma sigma' A))
        (sym (subTyComp tau sigma' B)))
      (eqSubDerivTyEqComp d composedFitsEq composedCFitsEq)
  eqSubDerivTyEqComp {sigma = sigma} {tau = tau}
    (eqSubTyRule {sigma = sigma'} {tau = tau'} {A = A} d fitsEq') fitsEq cFitsEq =
    let
      composedFitsEq = composeEqFitsEq fitsEq fitsEq'
      composedCFitsEq = composeCompEqFitsEq fitsEq cFitsEq fitsEq'
    in
    subst
      (λ J -> Computable J)
      (cong₂ (typeEq [])
        (sym (subTyComp sigma sigma' A))
        (sym (subTyComp tau tau' A)))
      (eqSubDerivTyComp d composedFitsEq composedCFitsEq)
  eqSubDerivTyEqComp {sigma = sigma} {tau = tau}
    (eqSubTyEqRule {sigma = sigma'} {tau = tau'} {A = A} {B = B} d fitsEq') fitsEq cFitsEq =
    let
      composedFitsEq = composeEqFitsEq fitsEq fitsEq'
      composedCFitsEq = composeCompEqFitsEq fitsEq cFitsEq fitsEq'
    in
    subst
      (λ J -> Computable J)
      (cong₂ (typeEq [])
        (sym (subTyComp sigma sigma' A))
        (sym (subTyComp tau tau' B)))
      (eqSubDerivTyEqComp d composedFitsEq composedCFitsEq)
  eqSubDerivTyEqComp (fEqEq dAC dac dbd) fitsEq cFitsEq =
    let
      compAC = eqSubDerivTyEqComp dAC fitsEq cFitsEq
      compac = eqSubDerivTmEqComp dac fitsEq cFitsEq
      compbd = eqSubDerivTmEqComp dbd fitsEq cFitsEq
      compA = compTyEqLeft compAC
      compC = compTyEqRight compAC
      compa = compTmEqLeft compac
      compb = compTmEqLeft compbd
      compcA = compTmEqRightClosed compac
      compdA = compTmEqRightClosed compbd
      compc = compConvTmClosed compcA compAC
      compd = compConvTmClosed compdA compAC
      compEqA = compFEqClosed compA compa compb
      compEqC = compFEqClosed compC compc compd
    in
    compTyEqClosedEq
      (fEqEq (compToDerivable compAC) (compToDerivable compac) (compToDerivable compbd))
      compEqA
      compEqC
      evalEq
      evalEq
      compAC
      compac
      compbd
  eqSubDerivTyEqComp (fQtrEq dAB) fitsEq cFitsEq =
    let
      compAB = eqSubDerivTyEqComp dAB fitsEq cFitsEq
    in
    compTyEqClosedQtr
      (fQtrEq (compToDerivable compAB))
      (compFQtrClosed (compTyEqLeft compAB))
      (compFQtrClosed (compTyEqRight compAB))
      evalQtr
      evalQtr
      compAB

  eqSubDerivTmCompEQtr
    : {gamma : Ctx} {A L : RawType} {l p : RawTerm} {sigma tau : Subst}
    -> Derivable (isType ((tyQtr A) ∷ gamma) L)
    -> Derivable (hasTy gamma p (tyQtr A))
    -> Derivable (hasTy (A ∷ gamma) l (qtrBranchTy L))
    -> Derivable
         (termEq (wkTyBy 1 A ∷ A ∷ gamma)
           (wkTmBy 1 l)
           (renTm qtrSecondBranchRen l)
           (qtrCohTy L))
    -> FitsEqSubst [] gamma sigma tau
    -> CompFitsEqSubst gamma sigma tau
    -> Computable
         (termEq []
           (subTm sigma (tmElQtr l p))
           (subTm tau (tmElQtr l p))
           (subTy sigma (subTy (singleSubst p) L)))
  eqSubDerivTmCompEQtr
    {gamma = gamma} {A = A} {L = L} {l = l} {p = p} {sigma = sigma} {tau = tau}
    dL dp dl dcoh fitsEq cFitsEq =
    let
      sigmaCFits = compFitsEqLeft cFitsEq
      sigmaFits = compFitsToFits sigmaCFits
      compp = eqSubDerivTmComp dp fitsEq cFitsEq
      compQtrσ = compTmToCompTy (compTmEqLeft compp)
      dQtrσ = compToDerivable compQtrσ
      tyInv = invertQtrTy compQtrσ evalQtr
      compAσ = ClosedQtrTyInv.qtrTyCompBase tyInv
      dAσ = compToDerivable compAσ
      dWkBaseσ = weakenTy dAσ (wfCons wfNil dAσ)
      dWkAσ =
        subst
          (λ T -> Derivable (isType (subTy sigma A ∷ []) T))
          (sym (wkTyLiftSubst sigma A))
          dWkBaseσ
      wkCtxWF : CtxWF (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
      wkCtxWF = wfCons (wfCons wfNil dAσ) dWkBaseσ

      compL = substOpenTy1 sigmaFits sigmaCFits dQtrσ (openCompTy dL)

      branchEq =
        subst
          (λ T ->
            Computable
              (termEq (subTy sigma A ∷ [])
                (subTm (liftSubst sigma) l)
                (subTm (liftSubst tau) l)
                T))
          (qtrBranchTyLiftComp sigma L)
          (eqSubOpenTm1 fitsEq cFitsEq dAσ (openCompTm dl))

      branchEqWk =
        subst
          (λ J -> Computable J)
          (cong
            (λ T ->
              termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                (wkTmBy 1 (subTm (liftSubst sigma) l))
                (wkTmBy 1 (subTm (liftSubst tau) l))
                T)
            (qtrBranchTyWk (subTy (liftSubst sigma) L)))
          (weakenOneOpenTmEq branchEq wkCtxWF)

      cohσ =
        subst
          (λ J -> Computable J)
          (cong
            (λ T ->
              termEq (T ∷ subTy sigma A ∷ [])
                (subTm (liftSubst (liftSubst sigma)) (wkTmBy 1 l))
                (subTm (liftSubst (liftSubst sigma)) (renTm qtrSecondBranchRen l))
                (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
            (wkTyLiftSubst sigma A)
            ∙ cong
                (λ t ->
                  termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                    t
                    (subTm (liftSubst (liftSubst sigma)) (renTm qtrSecondBranchRen l))
                    (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
                (wkTmLiftSubst (liftSubst sigma) l)
            ∙ cong
                (λ u ->
                  termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                    (wkTmBy 1 (subTm (liftSubst sigma) l))
                    u
                    (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
                (qtrSecondBranchTmLiftComp sigma l)
            ∙ cong
                (λ T ->
                  termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                    (wkTmBy 1 (subTm (liftSubst sigma) l))
                    (renTm qtrSecondBranchRen (subTm (liftSubst sigma) l))
                    T)
                (qtrCohTyLiftComp sigma L))
          (substOpenTmEq2 sigmaFits sigmaCFits dAσ dWkAσ (openCompTmEq dcoh))

      cohστ =
        subst
          (λ J -> Computable J)
          (cong
            (λ T ->
              termEq (T ∷ subTy sigma A ∷ [])
                (subTm (liftSubst (liftSubst sigma)) (wkTmBy 1 l))
                (subTm (liftSubst (liftSubst tau)) (renTm qtrSecondBranchRen l))
                (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
            (wkTyLiftSubst sigma A)
            ∙ cong
                (λ t ->
                  termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                    t
                    (subTm (liftSubst (liftSubst tau)) (renTm qtrSecondBranchRen l))
                    (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
                (wkTmLiftSubst (liftSubst sigma) l)
            ∙ cong
                (λ u ->
                  termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                    (wkTmBy 1 (subTm (liftSubst sigma) l))
                    u
                    (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
                (qtrSecondBranchTmLiftComp tau l)
            ∙ cong
                (λ T ->
                  termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                    (wkTmBy 1 (subTm (liftSubst sigma) l))
                    (renTm qtrSecondBranchRen (subTm (liftSubst tau) l))
                    T)
                (qtrCohTyLiftComp sigma L))
          (eqSubOpenTmEq2 fitsEq cFitsEq dAσ dWkAσ (openCompTmEq dcoh))

      cohτ = compTransTm (compSymTm branchEqWk) cohστ

      resultPath :
        termEq []
          (subTm sigma (tmElQtr l p))
          (subTm tau (tmElQtr l p))
          (subTy sigma (subTy (singleSubst p) L))
          ≡
        termEq []
          (tmElQtr (subTm (liftSubst sigma) l) (subTm sigma p))
          (tmElQtr (subTm (liftSubst tau) l) (subTm tau p))
          (subTy (singleSubst (subTm sigma p)) (subTy (liftSubst sigma) L))
      resultPath =
        cong₃
          (termEq [])
          refl
          refl
          (subTyComp sigma (singleSubst p) L
            ∙ cong (λ rho -> subTy rho L) (sym (singleSubstCompLift sigma p))
            ∙ sym (subTyComp (singleSubst (subTm sigma p)) (liftSubst sigma) L))
    in
    subst
      (λ J -> Computable J)
      (sym resultPath)
      (compEQtrClosed compL compp branchEq cohσ cohτ)

  eqSubDerivTmEqCompEQtrEq
    : {gamma : Ctx} {A L : RawType} {l l' p p' : RawTerm} {sigma tau : Subst}
    -> Derivable (isType ((tyQtr A) ∷ gamma) L)
    -> Derivable (termEq gamma p p' (tyQtr A))
    -> Derivable (termEq (A ∷ gamma) l l' (qtrBranchTy L))
    -> Derivable
         (termEq (wkTyBy 1 A ∷ A ∷ gamma)
           (wkTmBy 1 l)
           (renTm qtrSecondBranchRen l)
           (qtrCohTy L))
    -> Derivable
         (termEq (wkTyBy 1 A ∷ A ∷ gamma)
           (wkTmBy 1 l')
           (renTm qtrSecondBranchRen l')
           (qtrCohTy L))
    -> FitsEqSubst [] gamma sigma tau
    -> CompFitsEqSubst gamma sigma tau
    -> Computable
         (termEq []
           (subTm sigma (tmElQtr l p))
           (subTm tau (tmElQtr l' p'))
           (subTy sigma (subTy (singleSubst p) L)))
  eqSubDerivTmEqCompEQtrEq
    {gamma = gamma} {A = A} {L = L} {l = l} {l' = l'} {p = p} {p' = p'} {sigma = sigma} {tau = tau}
    dL dp dl dcoh dcoh' fitsEq cFitsEq =
    let
      sigmaCFits = compFitsEqLeft cFitsEq
      sigmaFits = compFitsToFits sigmaCFits
      compp = eqSubDerivTmEqComp dp fitsEq cFitsEq
      compQtrσ = compTmToCompTy (compTmEqLeft compp)
      dQtrσ = compToDerivable compQtrσ
      tyInv = invertQtrTy compQtrσ evalQtr
      compAσ = ClosedQtrTyInv.qtrTyCompBase tyInv
      dAσ = compToDerivable compAσ
      dWkBaseσ = weakenTy dAσ (wfCons wfNil dAσ)
      dWkAσ =
        subst
          (λ T -> Derivable (isType (subTy sigma A ∷ []) T))
          (sym (wkTyLiftSubst sigma A))
          dWkBaseσ
      wkCtxWF : CtxWF (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
      wkCtxWF = wfCons (wfCons wfNil dAσ) dWkBaseσ

      compL = substOpenTy1 sigmaFits sigmaCFits dQtrσ (openCompTy dL)

      branchEq =
        subst
          (λ T ->
            Computable
              (termEq (subTy sigma A ∷ [])
                (subTm (liftSubst sigma) l)
                (subTm (liftSubst tau) l')
                T))
          (qtrBranchTyLiftComp sigma L)
          (eqSubOpenTmEq1 fitsEq cFitsEq dAσ (openCompTmEq dl))

      branchEqRight =
        subst
          (λ T ->
            Computable
              (termEq (subTy sigma A ∷ [])
                (subTm (liftSubst sigma) l')
                (subTm (liftSubst tau) l')
                T))
          (qtrBranchTyLiftComp sigma L)
          (eqSubOpenTm1 fitsEq cFitsEq dAσ (openCompTm (assocTmRight dl)))

      branchEqRightWk =
        subst
          (λ J -> Computable J)
          (cong
            (λ T ->
              termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                (wkTmBy 1 (subTm (liftSubst sigma) l'))
                (wkTmBy 1 (subTm (liftSubst tau) l'))
                T)
            (qtrBranchTyWk (subTy (liftSubst sigma) L)))
          (weakenOneOpenTmEq branchEqRight wkCtxWF)

      cohσ =
        subst
          (λ J -> Computable J)
          (cong
            (λ T ->
              termEq (T ∷ subTy sigma A ∷ [])
                (subTm (liftSubst (liftSubst sigma)) (wkTmBy 1 l))
                (subTm (liftSubst (liftSubst sigma)) (renTm qtrSecondBranchRen l))
                (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
            (wkTyLiftSubst sigma A)
            ∙ cong
                (λ t ->
                  termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                    t
                    (subTm (liftSubst (liftSubst sigma)) (renTm qtrSecondBranchRen l))
                    (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
                (wkTmLiftSubst (liftSubst sigma) l)
            ∙ cong
                (λ u ->
                  termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                    (wkTmBy 1 (subTm (liftSubst sigma) l))
                    u
                    (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
                (qtrSecondBranchTmLiftComp sigma l)
            ∙ cong
                (λ T ->
                  termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                    (wkTmBy 1 (subTm (liftSubst sigma) l))
                    (renTm qtrSecondBranchRen (subTm (liftSubst sigma) l))
                    T)
                (qtrCohTyLiftComp sigma L))
          (substOpenTmEq2 sigmaFits sigmaCFits dAσ dWkAσ (openCompTmEq dcoh))

      coh'στ =
        subst
          (λ J -> Computable J)
          (cong
            (λ T ->
              termEq (T ∷ subTy sigma A ∷ [])
                (subTm (liftSubst (liftSubst sigma)) (wkTmBy 1 l'))
                (subTm (liftSubst (liftSubst tau)) (renTm qtrSecondBranchRen l'))
                (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
            (wkTyLiftSubst sigma A)
            ∙ cong
                (λ t ->
                  termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                    t
                    (subTm (liftSubst (liftSubst tau)) (renTm qtrSecondBranchRen l'))
                    (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
                (wkTmLiftSubst (liftSubst sigma) l')
            ∙ cong
                (λ u ->
                  termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                    (wkTmBy 1 (subTm (liftSubst sigma) l'))
                    u
                    (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
                (qtrSecondBranchTmLiftComp tau l')
            ∙ cong
                (λ T ->
                  termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                    (wkTmBy 1 (subTm (liftSubst sigma) l'))
                    (renTm qtrSecondBranchRen (subTm (liftSubst tau) l'))
                    T)
                (qtrCohTyLiftComp sigma L))
          (eqSubOpenTmEq2 fitsEq cFitsEq dAσ dWkAσ (openCompTmEq dcoh'))

      cohτ = compTransTm (compSymTm branchEqRightWk) coh'στ

      resultPath :
        termEq []
          (subTm sigma (tmElQtr l p))
          (subTm tau (tmElQtr l' p'))
          (subTy sigma (subTy (singleSubst p) L))
          ≡
        termEq []
          (tmElQtr (subTm (liftSubst sigma) l) (subTm sigma p))
          (tmElQtr (subTm (liftSubst tau) l') (subTm tau p'))
          (subTy (singleSubst (subTm sigma p)) (subTy (liftSubst sigma) L))
      resultPath =
        cong₃
          (termEq [])
          refl
          refl
          (subTyComp sigma (singleSubst p) L
            ∙ cong (λ rho -> subTy rho L) (sym (singleSubstCompLift sigma p))
            ∙ sym (subTyComp (singleSubst (subTm sigma p)) (liftSubst sigma) L))
    in
    subst
      (λ J -> Computable J)
      (sym resultPath)
      (compEQtrClosed compL compp branchEq cohσ cohτ)

  eqSubDerivTmEqCompCQtr
    : {gamma : Ctx} {A L : RawType} {a l : RawTerm} {sigma tau : Subst}
    -> Derivable (isType ((tyQtr A) ∷ gamma) L)
    -> Derivable (hasTy gamma a A)
    -> Derivable (hasTy (A ∷ gamma) l (qtrBranchTy L))
    -> Derivable
         (termEq (wkTyBy 1 A ∷ A ∷ gamma)
           (wkTmBy 1 l)
           (renTm qtrSecondBranchRen l)
           (qtrCohTy L))
    -> FitsEqSubst [] gamma sigma tau
    -> CompFitsEqSubst gamma sigma tau
    -> Computable
         (termEq []
           (subTm sigma (tmElQtr l (tmClass a)))
           (subTm tau (subTm (qtrCompSub a) l))
           (subTy sigma (subTy (singleSubst (tmClass a)) L)))
  eqSubDerivTmEqCompCQtr
    {gamma = gamma} {A = A} {L = L} {a = a} {l = l} {sigma = sigma} {tau = tau}
    dL da dl dcoh fitsEq cFitsEq =
    let
      sigmaCFits = compFitsEqLeft cFitsEq
      sigmaFits = compFitsToFits sigmaCFits
      compa = eqSubDerivTmComp da fitsEq cFitsEq
      compaσ = compTmEqLeft compa
      compAσ = compTmToCompTy compaσ
      dAσ = compToDerivable compAσ
      dQtrσ = compToDerivable (compFQtrClosed compAσ)
      dWkBaseσ = weakenTy dAσ (wfCons wfNil dAσ)
      dWkAσ =
        subst
          (λ T -> Derivable (isType (subTy sigma A ∷ []) T))
          (sym (wkTyLiftSubst sigma A))
          dWkBaseσ

      compL = substOpenTy1 sigmaFits sigmaCFits dQtrσ (openCompTy dL)

      complσ =
        subst
          (λ T ->
            Computable
              (hasTy (subTy sigma A ∷ [])
                (subTm (liftSubst sigma) l)
                T))
          (qtrBranchTyLiftComp sigma L)
          (substOpenTm1 sigmaFits sigmaCFits dAσ (openCompTm dl))

      compcohσ =
        subst
          (λ J -> Computable J)
          (cong
            (λ T ->
              termEq (T ∷ subTy sigma A ∷ [])
                (subTm (liftSubst (liftSubst sigma)) (wkTmBy 1 l))
                (subTm (liftSubst (liftSubst sigma)) (renTm qtrSecondBranchRen l))
                (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
            (wkTyLiftSubst sigma A)
            ∙ cong
                (λ t ->
                  termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                    t
                    (subTm (liftSubst (liftSubst sigma)) (renTm qtrSecondBranchRen l))
                    (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
                (wkTmLiftSubst (liftSubst sigma) l)
            ∙ cong
                (λ u ->
                  termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                    (wkTmBy 1 (subTm (liftSubst sigma) l))
                    u
                    (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
                (qtrSecondBranchTmLiftComp sigma l)
            ∙ cong
                (λ T ->
                  termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                    (wkTmBy 1 (subTm (liftSubst sigma) l))
                    (renTm qtrSecondBranchRen (subTm (liftSubst sigma) l))
                    T)
                (qtrCohTyLiftComp sigma L))
          (substOpenTmEq2 sigmaFits sigmaCFits dAσ dWkAσ (openCompTmEq dcoh))

      leftCan = compCQtrClosed compL compaσ complσ compcohσ

      complEq =
        subst
          (λ T ->
            Computable
              (termEq (subTy sigma A ∷ [])
                (subTm (liftSubst sigma) l)
                (subTm (liftSubst tau) l)
                T))
          (qtrBranchTyLiftComp sigma L)
          (eqSubOpenTm1 fitsEq cFitsEq dAσ (openCompTm dl))

      branchFitsEq :
        FitsEqSubst [] (subTy sigma A ∷ [])
          (qtrCompSub (subTm sigma a))
          (qtrCompSub (subTm tau a))
      branchFitsEq =
        compFitsEqToFitsEq (qtrCompCompFitsEqHelper compa)

      compBodyEq = branchSubEq branchFitsEq complEq

      resultPath :
        termEq []
          (subTm sigma (tmElQtr l (tmClass a)))
          (subTm tau (subTm (qtrCompSub a) l))
          (subTy sigma (subTy (singleSubst (tmClass a)) L))
          ≡
        termEq []
          (tmElQtr (subTm (liftSubst sigma) l) (tmClass (subTm sigma a)))
          (subTm (qtrCompSub (subTm tau a)) (subTm (liftSubst tau) l))
          (subTy (singleSubst (tmClass (subTm sigma a))) (subTy (liftSubst sigma) L))
      resultPath =
        cong₃
          (termEq [])
          refl
          (subTmComp tau (qtrCompSub a) l
            ∙ cong (λ rho -> subTm rho l) (qtrCompSubLiftComp tau a)
            ∙ sym (subTmComp (qtrCompSub (subTm tau a)) (liftSubst tau) l))
          (subTyComp sigma (singleSubst (tmClass a)) L
            ∙ cong (λ rho -> subTy rho L) (sym (singleSubstCompLift sigma (tmClass a)))
            ∙ sym (subTyComp (singleSubst (tmClass (subTm sigma a))) (liftSubst sigma) L))
    in
    subst
      (λ J -> Computable J)
      (sym resultPath)
      (compTransTmClosed leftCan compBodyEq)
    where
    branchSubEq :
      FitsEqSubst [] (subTy sigma A ∷ [])
        (qtrCompSub (subTm sigma a))
        (qtrCompSub (subTm tau a))
      ->
      Computable
        (termEq (subTy sigma A ∷ [])
          (subTm (liftSubst sigma) l)
          (subTm (liftSubst tau) l)
          (qtrBranchTy (subTy (liftSubst sigma) L)))
      ->
      Computable
        (termEq []
          (subTm (qtrCompSub (subTm sigma a)) (subTm (liftSubst sigma) l))
          (subTm (qtrCompSub (subTm tau a)) (subTm (liftSubst tau) l))
          (subTy (singleSubst (tmClass (subTm sigma a))) (subTy (liftSubst sigma) L)))
    branchSubEq branchFitsEq (compTmEqOpen _ _ _ _ subEqdl) =
      subst
        (λ J -> Computable J)
        (cong
          (termEq []
            (subTm (qtrCompSub (subTm sigma a)) (subTm (liftSubst sigma) l))
            (subTm (qtrCompSub (subTm tau a)) (subTm (liftSubst tau) l)))
          (qtrBranchTyComp (subTm sigma a) (subTy (liftSubst sigma) L)))
        (ClosedEqSubstComp.closedEqComp
          (subEqdl
            (qtrCompSub (subTm sigma a))
            (qtrCompSub (subTm tau a))
            branchFitsEq))

  eqSubDerivTmComp : {gamma : Ctx} {t : RawTerm} {A : RawType} {sigma tau : Subst}
    -> Derivable (hasTy gamma t A)
    -> FitsEqSubst [] gamma sigma tau
    -> CompFitsEqSubst gamma sigma tau
    -> Computable (termEq [] (subTm sigma t) (subTm tau t) (subTy sigma A))
  eqSubDerivTmComp (varStar {delta = delta} {A = A} wf dA) fitsEq cFitsEq =
    lookupCompFitsEq {delta = delta} {A = A} cFitsEq
  eqSubDerivTmComp (iTop wf) fitsEq cFitsEq =
    compReflTm compITopClosed
  eqSubDerivTmComp {sigma = sigma} {tau = tau}
    (iSigma {a = a} {b = b} {A = A} {B = B} da db dSigma) fitsEq cFitsEq =
    let
      sigmaCFits = compFitsEqLeft cFitsEq
      sigmaFits = compFitsToFits sigmaCFits
      compac = eqSubDerivTmComp da fitsEq cFitsEq
      compSigma = substDerivTyComp dSigma sigmaFits sigmaCFits
      tyInv = invertSigmaTy compSigma evalSigma
      compAσ = ClosedSigmaTyInv.sigmaTyCompHead tyInv
      compBσ = ClosedSigmaTyInv.sigmaTyCompFam tyInv
      compbdRaw = eqSubDerivTmComp db fitsEq cFitsEq
      compbd =
        subst
          (λ T -> Computable (termEq [] (subTm sigma b) (subTm tau b) T))
          (subTyComp sigma (singleSubst a) B
            ∙ cong (λ rho -> subTy rho B) (sym (singleSubstCompLift sigma a))
            ∙ sym (subTyComp (singleSubst (subTm sigma a)) (liftSubst sigma) B))
          compbdRaw
      compa = compTmEqLeft compac
      compcA = compTmEqRightClosed compac
      compb = compTmEqLeft compbd
      compdA = compTmEqRightClosed compbd
      compd =
        compConvTmClosed compdA (compSingleEqSubstTyClosed compBσ compac)
      compPairLeft = compISigmaClosed compa compb compSigma
      compPairRight = compISigmaClosed compcA compd compSigma
    in
    compTmEqClosedSigma
      (iSigmaEq (compToDerivable compac) (compToDerivable compbd)
        (compToDerivable compAσ) (compToDerivable compBσ))
      compPairLeft
      compPairRight
      evalSigma
      evalPair
      evalPair
      compac
      compbd
  eqSubDerivTmComp (iEq da) fitsEq cFitsEq =
    compReflTm (compIEqClosed (compTmEqLeft (eqSubDerivTmComp da fitsEq cFitsEq)))
  eqSubDerivTmComp (iQtr da) fitsEq cFitsEq =
    let
      compab = eqSubDerivTmComp da fitsEq cFitsEq
    in
    compIQtrEqClosed (compTmEqLeft compab) (compTmEqRightClosed compab)
  eqSubDerivTmComp {gamma = gamma} {sigma = sigma} {tau = tau}
    (eSigma {A = A} {B = B} {M = M} {d = d} {m = m} dM dd dm) fitsEq cFitsEq =
    let
      sigmaCFits = compFitsEqLeft cFitsEq
      sigmaFits = compFitsToFits sigmaCFits
      compdd = eqSubDerivTmComp dd fitsEq cFitsEq
      compSigma = compTmToCompTy (compTmEqLeft compdd)
      dSigmaσ = compToDerivable compSigma
      compM = substOpenTy1 sigmaFits sigmaCFits dSigmaσ (openCompTy dM)

      tyInv = invertSigmaTy compSigma evalSigma
      compAσ = ClosedSigmaTyInv.sigmaTyCompHead tyInv
      compBσ = ClosedSigmaTyInv.sigmaTyCompFam tyInv
      dAσ = compToDerivable compAσ
      dBσ = compToDerivable compBσ

      lifted1Eq :
        FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma) (liftSubst sigma) (liftSubst tau)
      lifted1Eq =
        subst
          (λ rho -> FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma) rho (liftSubst tau))
          (liftSubstCompKeep sigma)
          (subst
            (λ rho ->
              FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma)
                (consSubst (var zero) (compSub (keepSubstBy 1) sigma))
                rho)
            (liftSubstCompKeep tau)
            (liftFitsEqOne fitsEq dAσ))

      lifted2Eq :
        FitsEqSubst (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) (B ∷ A ∷ gamma)
          (liftSubst (liftSubst sigma))
          (liftSubst (liftSubst tau))
      lifted2Eq =
        subst
          (λ rho ->
            FitsEqSubst (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) (B ∷ A ∷ gamma)
              rho
              (liftSubst (liftSubst tau)))
          (liftSubstCompKeep (liftSubst sigma))
          (subst
            (λ rho ->
              FitsEqSubst (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) (B ∷ A ∷ gamma)
                (consSubst (var zero) (compSub (keepSubstBy 1) (liftSubst sigma)))
                rho)
            (liftSubstCompKeep (liftSubst tau))
            (liftFitsEq lifted1Eq dBσ))

      compdm =
        subst
          (λ J -> Computable J)
          (cong
            (termEq (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ [])
              (subTm (liftSubst (liftSubst sigma)) m)
              (subTm (liftSubst (liftSubst tau)) m))
            (sigmaBranchTyLiftComp sigma M))
          (eqSubOpenTm2 fitsEq cFitsEq dAσ dBσ (openCompTm dm))

      resultPath :
        termEq []
          (subTm sigma (tmElSigma d m))
          (subTm tau (tmElSigma d m))
          (subTy sigma (subTy (singleSubst d) M))
          ≡
        termEq []
          (tmElSigma (subTm sigma d) (subTm (liftSubst (liftSubst sigma)) m))
          (tmElSigma (subTm tau d) (subTm (liftSubst (liftSubst tau)) m))
          (subTy (singleSubst (subTm sigma d)) (subTy (liftSubst sigma) M))
      resultPath =
        cong₃
          (termEq [])
          refl
          refl
          (subTyComp sigma (singleSubst d) M
            ∙ cong (λ rho -> subTy rho M) (sym (singleSubstCompLift sigma d))
            ∙ sym (subTyComp (singleSubst (subTm sigma d)) (liftSubst sigma) M))
    in
    subst
      (λ J -> Computable J)
      (sym resultPath)
      (compESigmaClosed compM compdd compdm)
  eqSubDerivTmComp (eQtr dL dp dl dcoh) fitsEq cFitsEq =
    eqSubDerivTmCompEQtr dL dp dl dcoh fitsEq cFitsEq
  eqSubDerivTmComp (conv d dAB) fitsEq cFitsEq =
    let
      sigmaCFits = compFitsEqLeft cFitsEq
      sigmaFits = compFitsToFits sigmaCFits
    in
    compConvTmEqClosed (eqSubDerivTmComp d fitsEq cFitsEq) (substDerivTyEqComp dAB sigmaFits sigmaCFits)
  eqSubDerivTmComp {sigma = sigma} {tau = tau}
    (weakenTm {delta = delta} {t = t} {A = A} d wf) fitsEq cFitsEq =
    subst
      (λ J -> Computable J)
      (cong₃ (termEq [])
        (sym (subTmWkBy sigma (length delta) t))
        (sym (subTmWkBy tau (length delta) t))
        (sym (subTyWkBy sigma (length delta) A)))
      (eqSubDerivTmComp d (dropFitsEq delta fitsEq) (dropCompFitsEq delta cFitsEq))
  eqSubDerivTmComp {sigma = sigma} {tau = tau}
    (substTmRule {sigma = sigma'} {t = t} {A = A} d fits') fitsEq cFitsEq =
    let
      composedFitsEq = composeEqFits fitsEq fits'
      composedCFitsEq = composeCompEqFits fitsEq cFitsEq fits'
    in
    subst
      (λ J -> Computable J)
      (cong₃ (termEq [])
        (sym (subTmComp sigma sigma' t))
        (sym (subTmComp tau sigma' t))
        (sym (subTyComp sigma sigma' A)))
      (eqSubDerivTmComp d composedFitsEq composedCFitsEq)
  eqSubDerivTmEqComp : {gamma : Ctx} {t u : RawTerm} {A : RawType} {sigma tau : Subst}
    -> Derivable (termEq gamma t u A)
    -> FitsEqSubst [] gamma sigma tau
    -> CompFitsEqSubst gamma sigma tau
    -> Computable (termEq [] (subTm sigma t) (subTm tau u) (subTy sigma A))
  eqSubDerivTmEqComp (reflTm d) fitsEq cFitsEq =
    eqSubDerivTmComp d fitsEq cFitsEq
  eqSubDerivTmEqComp (symTm d) fitsEq cFitsEq =
    let
      sigmaCFits = compFitsEqLeft cFitsEq
      sigmaFits = compFitsToFits sigmaCFits
    in
    compTransTmClosed
      (compSymTmClosed (substDerivTmEqComp d sigmaFits sigmaCFits))
      (eqSubDerivTmComp (assocTmLeft d) fitsEq cFitsEq)
  eqSubDerivTmEqComp (transTm d₁ d₂) fitsEq cFitsEq =
    let
      sigmaCFits = compFitsEqLeft cFitsEq
      sigmaFits = compFitsToFits sigmaCFits
    in
    compTransTmClosed
      (substDerivTmEqComp d₁ sigmaFits sigmaCFits)
      (eqSubDerivTmEqComp d₂ fitsEq cFitsEq)
  eqSubDerivTmEqComp (convEq d dAB) fitsEq cFitsEq =
    let
      sigmaCFits = compFitsEqLeft cFitsEq
      sigmaFits = compFitsToFits sigmaCFits
    in
    compConvTmEqClosed (eqSubDerivTmEqComp d fitsEq cFitsEq) (substDerivTyEqComp dAB sigmaFits sigmaCFits)
  eqSubDerivTmEqComp (cTop d) fitsEq cFitsEq =
    compCTopClosed (compTmEqLeft (eqSubDerivTmComp d fitsEq cFitsEq))
  eqSubDerivTmEqComp {sigma = sigma} {tau = tau}
    (iSigmaEq {a = a} {b = b} {d = d} {A = A} {B = B} dac dbd dA dB) fitsEq cFitsEq =
    let
      sigmaCFits = compFitsEqLeft cFitsEq
      sigmaFits = compFitsToFits sigmaCFits
      compac = eqSubDerivTmEqComp dac fitsEq cFitsEq
      compA = substDerivTyComp dA sigmaFits sigmaCFits
      dAσ = compToDerivable compA
      compB = substOpenTy1 sigmaFits sigmaCFits dAσ (openCompTy dB)
      compbdRaw = eqSubDerivTmEqComp dbd fitsEq cFitsEq
      compbd =
        subst
          (λ T -> Computable (termEq [] (subTm sigma b) (subTm tau d) T))
          (subTyComp sigma (singleSubst a) B
            ∙ cong (λ rho -> subTy rho B) (sym (singleSubstCompLift sigma a))
            ∙ sym (subTyComp (singleSubst (subTm sigma a)) (liftSubst sigma) B))
          compbdRaw
      compa = compTmEqLeft compac
      compcA = compTmEqRightClosed compac
      compb = compTmEqLeft compbd
      compdA = compTmEqRightClosed compbd
      compd =
        compConvTmClosed compdA (compSingleEqSubstTyClosed compB compac)
      compPairLeft = compISigmaClosed compa compb (compFSigmaClosed compA compB)
      compPairRight = compISigmaClosed compcA compd (compFSigmaClosed compA compB)
    in
    compTmEqClosedSigma
      (iSigmaEq (compToDerivable compac) (compToDerivable compbd) dAσ (compToDerivable compB))
      compPairLeft
      compPairRight
      evalSigma
      evalPair
      evalPair
      compac
      compbd
  eqSubDerivTmEqComp {gamma = gamma} {sigma = sigma} {tau = tau}
    (eSigmaEq {A = A} {B = B} {M = M} {d = d} {d' = d'} {m = m} {m' = m'} dM dd dm) fitsEq cFitsEq =
    let
      sigmaCFits = compFitsEqLeft cFitsEq
      sigmaFits = compFitsToFits sigmaCFits
      compdd = eqSubDerivTmEqComp dd fitsEq cFitsEq
      compSigma = compTmToCompTy (compTmEqLeft compdd)
      dSigmaσ = compToDerivable compSigma
      compM = substOpenTy1 sigmaFits sigmaCFits dSigmaσ (openCompTy dM)

      tyInv = invertSigmaTy compSigma evalSigma
      compAσ = ClosedSigmaTyInv.sigmaTyCompHead tyInv
      compBσ = ClosedSigmaTyInv.sigmaTyCompFam tyInv
      dAσ = compToDerivable compAσ
      dBσ = compToDerivable compBσ

      lifted1Eq :
        FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma) (liftSubst sigma) (liftSubst tau)
      lifted1Eq =
        subst
          (λ rho -> FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma) rho (liftSubst tau))
          (liftSubstCompKeep sigma)
          (subst
            (λ rho ->
              FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma)
                (consSubst (var zero) (compSub (keepSubstBy 1) sigma))
                rho)
            (liftSubstCompKeep tau)
            (liftFitsEqOne fitsEq dAσ))

      lifted2Eq :
        FitsEqSubst (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) (B ∷ A ∷ gamma)
          (liftSubst (liftSubst sigma))
          (liftSubst (liftSubst tau))
      lifted2Eq =
        subst
          (λ rho ->
            FitsEqSubst (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) (B ∷ A ∷ gamma)
              rho
              (liftSubst (liftSubst tau)))
          (liftSubstCompKeep (liftSubst sigma))
          (subst
            (λ rho ->
              FitsEqSubst (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) (B ∷ A ∷ gamma)
                (consSubst (var zero) (compSub (keepSubstBy 1) (liftSubst sigma)))
                rho)
            (liftSubstCompKeep (liftSubst tau))
            (liftFitsEq lifted1Eq dBσ))

      compdm =
        subst
          (λ J -> Computable J)
          (cong
            (termEq (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ [])
              (subTm (liftSubst (liftSubst sigma)) m)
              (subTm (liftSubst (liftSubst tau)) m'))
            (sigmaBranchTyLiftComp sigma M))
          (eqSubOpenTmEq2 fitsEq cFitsEq dAσ dBσ (openCompTmEq dm))

      resultPath :
        termEq []
          (subTm sigma (tmElSigma d m))
          (subTm tau (tmElSigma d' m'))
          (subTy sigma (subTy (singleSubst d) M))
          ≡
        termEq []
          (tmElSigma (subTm sigma d) (subTm (liftSubst (liftSubst sigma)) m))
          (tmElSigma (subTm tau d') (subTm (liftSubst (liftSubst tau)) m'))
          (subTy (singleSubst (subTm sigma d)) (subTy (liftSubst sigma) M))
      resultPath =
        cong₃
          (termEq [])
          refl
          refl
          (subTyComp sigma (singleSubst d) M
            ∙ cong (λ rho -> subTy rho M) (sym (singleSubstCompLift sigma d))
            ∙ sym (subTyComp (singleSubst (subTm sigma d)) (liftSubst sigma) M))
    in
    subst
      (λ J -> Computable J)
      (sym resultPath)
      (compESigmaClosed compM compdd compdm)
  eqSubDerivTmEqComp {gamma = gamma} {sigma = sigma} {tau = tau}
    (cSigma {A = A} {B = B} {M = M} {b = b} {c = c} {m = m} dM db dc dm) fitsEq cFitsEq =
    let
      sigmaCFits = compFitsEqLeft cFitsEq
      sigmaFits = compFitsToFits sigmaCFits
      compb = eqSubDerivTmComp db fitsEq cFitsEq
      compSigma = substDerivTyComp (ctxSuffixTy {delta = []} {gamma = gamma} {A = tySigma A B} (derivToCtxWF dM)) sigmaFits sigmaCFits
      dSigmaσ = compToDerivable compSigma
      tyInv = invertSigmaTy compSigma evalSigma
      compAσ = ClosedSigmaTyInv.sigmaTyCompHead tyInv
      compBσ = ClosedSigmaTyInv.sigmaTyCompFam tyInv
      dAσ = compToDerivable compAσ
      dBσ = compToDerivable compBσ
      compM = substOpenTy1 sigmaFits sigmaCFits dSigmaσ (openCompTy dM)

      compcRaw = eqSubDerivTmComp dc fitsEq cFitsEq
      compc =
        subst
          (λ T -> Computable (termEq [] (subTm sigma c) (subTm tau c) T))
          (subTyComp sigma (singleSubst b) B
            ∙ cong (λ rho -> subTy rho B) (sym (singleSubstCompLift sigma b))
            ∙ sym (subTyComp (singleSubst (subTm sigma b)) (liftSubst sigma) B))
          compcRaw

      branchFitsEq : FitsEqSubst [] (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ [])
        (sigmaCompSub (subTm sigma b) (subTm sigma c))
        (sigmaCompSub (subTm tau b) (subTm tau c))
      branchFitsEq =
        compFitsEqToFitsEq
          (sigmaCompCompFitsEqHelper compb compc)

      compdmOpen =
        eqSubOpenTm2 fitsEq cFitsEq dAσ dBσ (openCompTm dm)

      compdmEq =
        branchSubEq branchFitsEq compdmOpen

      leftCanPath :
        termEq []
          (subTm sigma (tmElSigma (tmPair b c) m))
          (subTm sigma (subTm (sigmaCompSub b c) m))
          (subTy sigma (subTy (singleSubst (tmPair b c)) M))
          ≡
        termEq []
          (tmElSigma (tmPair (subTm sigma b) (subTm sigma c))
            (subTm (liftSubst (liftSubst sigma)) m))
          (subTm (sigmaCompSub (subTm sigma b) (subTm sigma c))
            (subTm (liftSubst (liftSubst sigma)) m))
          (subTy (singleSubst (tmPair (subTm sigma b) (subTm sigma c)))
            (subTy (liftSubst sigma) M))
      leftCanPath =
        cong₃
          (termEq [])
          refl
          (subTmComp sigma (sigmaCompSub b c) m
            ∙ cong (λ rho -> subTm rho m) (sigmaCompSubLiftComp sigma b c)
            ∙ sym (subTmComp (sigmaCompSub (subTm sigma b) (subTm sigma c))
                (liftSubst (liftSubst sigma)) m))
          (subTyComp sigma (singleSubst (tmPair b c)) M
            ∙ cong (λ rho -> subTy rho M) (sym (singleSubstCompLift sigma (tmPair b c)))
            ∙ sym (subTyComp (singleSubst (tmPair (subTm sigma b) (subTm sigma c)))
                (liftSubst sigma) M))

      leftCan =
        subst
          (λ J -> Computable J)
          leftCanPath
          (substDerivTmEqComp (cSigma dM db dc dm) sigmaFits sigmaCFits)

      resultPath :
        termEq []
          (subTm sigma (tmElSigma (tmPair b c) m))
          (subTm tau (subTm (sigmaCompSub b c) m))
          (subTy sigma (subTy (singleSubst (tmPair b c)) M))
          ≡
        termEq []
          (tmElSigma (tmPair (subTm sigma b) (subTm sigma c))
            (subTm (liftSubst (liftSubst sigma)) m))
          (subTm (sigmaCompSub (subTm tau b) (subTm tau c))
            (subTm (liftSubst (liftSubst tau)) m))
          (subTy (singleSubst (tmPair (subTm sigma b) (subTm sigma c)))
            (subTy (liftSubst sigma) M))
      resultPath =
        cong₃
          (termEq [])
          refl
          (subTmComp tau (sigmaCompSub b c) m
            ∙ cong (λ rho -> subTm rho m) (sigmaCompSubLiftComp tau b c)
            ∙ sym (subTmComp (sigmaCompSub (subTm tau b) (subTm tau c))
                (liftSubst (liftSubst tau)) m))
          (subTyComp sigma (singleSubst (tmPair b c)) M
            ∙ cong (λ rho -> subTy rho M) (sym (singleSubstCompLift sigma (tmPair b c)))
            ∙ sym (subTyComp (singleSubst (tmPair (subTm sigma b) (subTm sigma c)))
                (liftSubst sigma) M))
    in
    subst
      (λ J -> Computable J)
      (sym resultPath)
      (compTransTmClosed leftCan compdmEq)
    where
    branchSubEq :
      FitsEqSubst [] (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ [])
        (sigmaCompSub (subTm sigma b) (subTm sigma c))
        (sigmaCompSub (subTm tau b) (subTm tau c))
      ->
      Computable
        (termEq (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ [])
          (subTm (liftSubst (liftSubst sigma)) m)
          (subTm (liftSubst (liftSubst tau)) m)
          (subTy (liftSubst (liftSubst sigma)) (sigmaBranchTy M)))
      -> Computable
           (termEq []
             (subTm (sigmaCompSub (subTm sigma b) (subTm sigma c))
               (subTm (liftSubst (liftSubst sigma)) m))
             (subTm (sigmaCompSub (subTm tau b) (subTm tau c))
               (subTm (liftSubst (liftSubst tau)) m))
             (subTy (singleSubst (tmPair (subTm sigma b) (subTm sigma c)))
               (subTy (liftSubst sigma) M)))
    branchSubEq branchFitsEq (compTmEqOpen _ _ _ _ subEqdm) =
      subst
        (λ J -> Computable J)
        (cong
          (termEq []
            (subTm (sigmaCompSub (subTm sigma b) (subTm sigma c))
              (subTm (liftSubst (liftSubst sigma)) m))
            (subTm (sigmaCompSub (subTm tau b) (subTm tau c))
              (subTm (liftSubst (liftSubst tau)) m)))
          (cong
            (λ T -> subTy (sigmaCompSub (subTm sigma b) (subTm sigma c)) T)
            (sigmaBranchTyLiftComp sigma M)
            ∙ sigmaBranchTyComp (subTm sigma b) (subTm sigma c) (subTy (liftSubst sigma) M)))
        (ClosedEqSubstComp.closedEqComp
          (subEqdm
            (sigmaCompSub (subTm sigma b) (subTm sigma c))
            (sigmaCompSub (subTm tau b) (subTm tau c))
            branchFitsEq))
  eqSubDerivTmEqComp (iEqEq d) fitsEq cFitsEq =
    compReflTm (compIEqClosed (compTmEqLeft (eqSubDerivTmEqComp d fitsEq cFitsEq)))
  eqSubDerivTmEqComp (eEqStar dp dA da db) fitsEq cFitsEq =
    let
      compp = eqSubDerivTmComp dp fitsEq cFitsEq
      compab = compEEqClosed (compTmEqLeft compp)
      compbb' = eqSubDerivTmComp db fitsEq cFitsEq
    in
    compTransTmClosed compab compbb'
  eqSubDerivTmEqComp (cEq dp dA da db) fitsEq cFitsEq =
    compCEqClosed (compTmEqLeft (eqSubDerivTmComp dp fitsEq cFitsEq))
  eqSubDerivTmEqComp (iQtrEq da db) fitsEq cFitsEq =
    let
      compab = eqSubDerivTmComp da fitsEq cFitsEq
      compcd = eqSubDerivTmComp db fitsEq cFitsEq
    in
    compIQtrEqClosed (compTmEqLeft compab) (compTmEqRightClosed compcd)
  eqSubDerivTmEqComp (eQtrEq dL dp dl dcoh dcoh') fitsEq cFitsEq =
    eqSubDerivTmEqCompEQtrEq dL dp dl dcoh dcoh' fitsEq cFitsEq
  eqSubDerivTmEqComp (cQtr dL da dl dcoh) fitsEq cFitsEq =
    eqSubDerivTmEqCompCQtr dL da dl dcoh fitsEq cFitsEq
  eqSubDerivTmEqComp {sigma = sigma} {tau = tau}
    (weakenTmEq {delta = delta} {t = t} {u = u} {A = A} d wf) fitsEq cFitsEq =
    subst
      (λ J -> Computable J)
      (cong₃ (termEq [])
        (sym (subTmWkBy sigma (length delta) t))
        (sym (subTmWkBy tau (length delta) u))
        (sym (subTyWkBy sigma (length delta) A)))
      (eqSubDerivTmEqComp d (dropFitsEq delta fitsEq) (dropCompFitsEq delta cFitsEq))
  eqSubDerivTmEqComp {sigma = sigma} {tau = tau}
    (substTmEqRule {sigma = sigma'} {t = t} {u = u} {A = A} d fits') fitsEq cFitsEq =
    let
      composedFitsEq = composeEqFits fitsEq fits'
      composedCFitsEq = composeCompEqFits fitsEq cFitsEq fits'
    in
    subst
      (λ J -> Computable J)
      (cong₃ (termEq [])
        (sym (subTmComp sigma sigma' t))
        (sym (subTmComp tau sigma' u))
        (sym (subTyComp sigma sigma' A)))
      (eqSubDerivTmEqComp d composedFitsEq composedCFitsEq)
  eqSubDerivTmEqComp {sigma = sigma} {tau = tau}
    (eqSubTmRule {sigma = sigma'} {tau = tau'} {t = t} {A = A} d fitsEq') fitsEq cFitsEq =
    let
      composedFitsEq = composeEqFitsEq fitsEq fitsEq'
      composedCFitsEq = composeCompEqFitsEq fitsEq cFitsEq fitsEq'
    in
    subst
      (λ J -> Computable J)
      (cong₃ (termEq [])
        (sym (subTmComp sigma sigma' t))
        (sym (subTmComp tau tau' t))
        (sym (subTyComp sigma sigma' A)))
      (eqSubDerivTmComp d composedFitsEq composedCFitsEq)
  eqSubDerivTmEqComp {sigma = sigma} {tau = tau}
    (eqSubTmEqRule {sigma = sigma'} {tau = tau'} {t = t} {u = u} {A = A} d fitsEq') fitsEq cFitsEq =
    let
      composedFitsEq = composeEqFitsEq fitsEq fitsEq'
      composedCFitsEq = composeCompEqFitsEq fitsEq cFitsEq fitsEq'
    in
    subst
      (λ J -> Computable J)
      (cong₃ (termEq [])
        (sym (subTmComp sigma sigma' t))
        (sym (subTmComp tau tau' u))
        (sym (subTyComp sigma sigma' A)))
      (eqSubDerivTmEqComp d composedFitsEq composedCFitsEq)
  openCompTy : {A : RawType} {B : RawType} {gamma : Ctx}
    -> Derivable (isType (B ∷ gamma) A)
    -> Computable (isType (B ∷ gamma) A)
  openCompTy d =
    compTyOpen
      nonemptyNeNil
      d
      (λ sigma fits -> packClosedSubst fits (substDerivTyComp d fits (fitsToCompFits fits)))
      (λ sigma tau fitsEq -> packClosedEqSubst fitsEq (eqSubDerivTyComp d fitsEq (fitsEqToCompFitsEq fitsEq)))

  openCompTyEq : {A B C : RawType} {gamma : Ctx}
    -> Derivable (typeEq (C ∷ gamma) A B)
    -> Computable (typeEq (C ∷ gamma) A B)
  openCompTyEq d =
    compTyEqOpen
      nonemptyNeNil
      d
      (openCompTy (assocTyLeft d))
      (λ sigma fits -> packClosedSubst fits (substDerivTyEqComp d fits (fitsToCompFits fits)))
      (λ sigma tau fitsEq -> packClosedEqSubst fitsEq (eqSubDerivTyEqComp d fitsEq (fitsEqToCompFitsEq fitsEq)))

  openCompTm : {t : RawTerm} {A B : RawType} {gamma : Ctx}
    -> Derivable (hasTy (B ∷ gamma) t A)
    -> Computable (hasTy (B ∷ gamma) t A)
  openCompTm d =
    compTmOpen
      nonemptyNeNil
      d
      (openCompTy (assocTy d))
      (λ sigma fits -> packClosedSubst fits (substDerivTmComp d fits (fitsToCompFits fits)))
      (λ sigma tau fitsEq -> packClosedEqSubst fitsEq (eqSubDerivTmComp d fitsEq (fitsEqToCompFitsEq fitsEq)))

  openCompTmEq : {t u : RawTerm} {A B : RawType} {gamma : Ctx}
    -> Derivable (termEq (B ∷ gamma) t u A)
    -> Computable (termEq (B ∷ gamma) t u A)
  openCompTmEq d =
    compTmEqOpen
      nonemptyNeNil
      d
      (openCompTm (assocTmLeft d))
      (λ sigma fits -> packClosedSubst fits (substDerivTmEqComp d fits (fitsToCompFits fits)))
      (λ sigma tau fitsEq -> packClosedEqSubst fitsEq (eqSubDerivTmEqComp d fitsEq (fitsEqToCompFitsEq fitsEq)))

  substTyClosed : {delta : Ctx} {A : RawType} {sigma : Subst}
    -> Derivable (isType delta A)
    -> FitsSubst [] delta sigma
    -> Computable (isType [] (subTy sigma A))
  substTyClosed d fits = substDerivTyComp d fits (fitsToCompFits fits)

  substTyEqClosed : {delta : Ctx} {A B : RawType} {sigma : Subst}
    -> Derivable (typeEq delta A B)
    -> FitsSubst [] delta sigma
    -> Computable (typeEq [] (subTy sigma A) (subTy sigma B))
  substTyEqClosed d fits = substDerivTyEqComp d fits (fitsToCompFits fits)

  substTmClosed : {delta : Ctx} {t : RawTerm} {A : RawType} {sigma : Subst}
    -> Derivable (hasTy delta t A)
    -> FitsSubst [] delta sigma
    -> Computable (hasTy [] (subTm sigma t) (subTy sigma A))
  substTmClosed d fits = substDerivTmComp d fits (fitsToCompFits fits)

  substTmEqClosed : {delta : Ctx} {t u : RawTerm} {A : RawType} {sigma : Subst}
    -> Derivable (termEq delta t u A)
    -> FitsSubst [] delta sigma
    -> Computable (termEq [] (subTm sigma t) (subTm sigma u) (subTy sigma A))
  substTmEqClosed d fits = substDerivTmEqComp d fits (fitsToCompFits fits)

  eqSubTyClosed : {delta : Ctx} {A : RawType} {sigma tau : Subst}
    -> Derivable (isType delta A)
    -> FitsEqSubst [] delta sigma tau
    -> Computable (typeEq [] (subTy sigma A) (subTy tau A))
  eqSubTyClosed d fitsEq = eqSubDerivTyComp d fitsEq (fitsEqToCompFitsEq fitsEq)

  eqSubTyEqClosed : {delta : Ctx} {A B : RawType} {sigma tau : Subst}
    -> Derivable (typeEq delta A B)
    -> FitsEqSubst [] delta sigma tau
    -> Computable (typeEq [] (subTy sigma A) (subTy tau B))
  eqSubTyEqClosed d fitsEq = eqSubDerivTyEqComp d fitsEq (fitsEqToCompFitsEq fitsEq)

  eqSubTmClosed : {delta : Ctx} {t : RawTerm} {A : RawType} {sigma tau : Subst}
    -> Derivable (hasTy delta t A)
    -> FitsEqSubst [] delta sigma tau
    -> Computable (termEq [] (subTm sigma t) (subTm tau t) (subTy sigma A))
  eqSubTmClosed d fitsEq = eqSubDerivTmComp d fitsEq (fitsEqToCompFitsEq fitsEq)

  eqSubTmEqClosed : {delta : Ctx} {t u : RawTerm} {A : RawType} {sigma tau : Subst}
    -> Derivable (termEq delta t u A)
    -> FitsEqSubst [] delta sigma tau
    -> Computable (termEq [] (subTm sigma t) (subTm tau u) (subTy sigma A))
  eqSubTmEqClosed d fitsEq = eqSubDerivTmEqComp d fitsEq (fitsEqToCompFitsEq fitsEq)

  compTransportFamilyTy : {A C D : RawType}
    -> Computable (typeEq [] A C)
    -> Computable (isType (A ∷ []) D)
    -> Computable (isType (C ∷ []) D)
  compTransportFamilyTy {A = A} {C = C} {D = D} compAC (compTyOpen neq dD sub subEq) =
    compTyOpen
      nonemptyNeNil
      (transportFamilyTy dAC dC dD)
      (λ sigma fits ->
        packClosedSubst fits
          (subst
            (λ T -> Computable (isType [] T))
            (sym (subTyComp sigma idSubst D) ∙ cong (subTy sigma) (subTyId D))
            (ClosedSubstComp.closedComp
              (sub (compSub sigma idSubst) (composeFits fits transportFits)))))
      (λ sigma tau fitsEq ->
        packClosedEqSubst fitsEq
          (subst
            (λ J -> Computable J)
            (cong₂ (typeEq [])
              (sym (subTyComp sigma idSubst D) ∙ cong (subTy sigma) (subTyId D))
              (sym (subTyComp tau idSubst D) ∙ cong (subTy tau) (subTyId D)))
            (ClosedEqSubstComp.closedEqComp
              (subEq
                (compSub sigma idSubst)
                (compSub tau idSubst)
                (composeEqFits fitsEq transportFits)))))
    where
    dAC : Derivable (typeEq [] A C)
    dAC = compToDerivable compAC

    dC : Derivable (isType [] C)
    dC = compToDerivable (compTyEqRightClosed compAC)

    transportFits : FitsSubst (C ∷ []) (A ∷ []) idSubst
    transportFits = headTypeTransportFits dAC dC

  compTransportFamilyTyEq : {A C D F : RawType}
    -> Computable (typeEq [] A C)
    -> Computable (typeEq (A ∷ []) D F)
    -> Computable (typeEq (C ∷ []) D F)
  compTransportFamilyTyEq {A = A} {C = C} {D = D} {F = F} compAC (compTyEqOpen neq dDF compD sub subEq) =
    compTyEqOpen
      nonemptyNeNil
      (transportFamilyTyEq dAC dC dDF)
      (compTransportFamilyTy compAC compD)
      (λ sigma fits ->
        packClosedSubst fits
          (subst
            (λ J -> Computable J)
            (cong₂ (typeEq [])
              (sym (subTyComp sigma idSubst D) ∙ cong (subTy sigma) (subTyId D))
              (sym (subTyComp sigma idSubst F) ∙ cong (subTy sigma) (subTyId F)))
            (ClosedSubstComp.closedComp
              (sub (compSub sigma idSubst) (composeFits fits transportFits)))))
      (λ sigma tau fitsEq ->
        packClosedEqSubst fitsEq
          (subst
            (λ J -> Computable J)
            (cong₂ (typeEq [])
              (sym (subTyComp sigma idSubst D) ∙ cong (subTy sigma) (subTyId D))
              (sym (subTyComp tau idSubst F) ∙ cong (subTy tau) (subTyId F)))
            (ClosedEqSubstComp.closedEqComp
              (subEq
                (compSub sigma idSubst)
                (compSub tau idSubst)
                (composeEqFits fitsEq transportFits)))))
    where
    dAC : Derivable (typeEq [] A C)
    dAC = compToDerivable compAC

    dC : Derivable (isType [] C)
    dC = compToDerivable (compTyEqRightClosed compAC)

    transportFits : FitsSubst (C ∷ []) (A ∷ []) idSubst
    transportFits = headTypeTransportFits dAC dC

  compSymTyOpenHelper : {gamma : Ctx} {A B : RawType}
    -> ({A B : RawType} -> Computable (typeEq [] A B) -> Computable (typeEq [] B A))
    -> ({A B C : RawType} -> Computable (typeEq [] A B) -> Computable (typeEq [] B C) -> Computable (typeEq [] A C))
    -> ((gamma ≡ []) -> ⊥)
    -> Derivable (typeEq gamma A B)
    -> Computable (isType gamma A)
    -> ((sigma : Subst) -> FitsSubst [] gamma sigma
         -> ClosedSubstComp (typeEq gamma A B) sigma)
    -> ((sigma tau : Subst) -> FitsEqSubst [] gamma sigma tau
         -> ClosedEqSubstComp (typeEq gamma A B) sigma tau)
    -> Computable (typeEq gamma B A)
  compSymTyOpenHelper symCl transCl neq d compA sub subEq =
    compTyEqOpen
      neq
      (symTy d)
      (compTyOpen
        neq
        (assocTyRight d)
        (λ sigma fits ->
          packClosedSubst fits
            (compTyEqRightClosed (ClosedSubstComp.closedComp (sub sigma fits))))
        (λ sigma tau fitsEq ->
          let
            closedσ = ClosedSubstComp.closedComp (sub sigma (fitsEqSubstLeft fitsEq))
            closedστ = ClosedEqSubstComp.closedEqComp (subEq sigma tau fitsEq)
          in
          packClosedEqSubst fitsEq
            (transCl
              (symCl closedσ)
              closedστ)))
      (λ sigma fits ->
        packClosedSubst fits
          (symCl (ClosedSubstComp.closedComp (sub sigma fits))))
      (λ sigma tau fitsEq ->
        let
          closedσ = ClosedSubstComp.closedComp (sub sigma (fitsEqSubstLeft fitsEq))
          closedστ = ClosedEqSubstComp.closedEqComp (subEq sigma tau fitsEq)
          closedτ = ClosedSubstComp.closedComp (sub tau (fitsEqSubstRight (derivToCtxWF d) fitsEq))
        in
        packClosedEqSubst fitsEq
          (transCl
            (transCl (symCl closedσ) closedστ)
            (symCl closedτ)))

  compTransTyOpenHelper : {gamma : Ctx} {A B C : RawType}
    -> ({A B C : RawType} -> Computable (typeEq [] A B) -> Computable (typeEq [] B C) -> Computable (typeEq [] A C))
    -> ((gamma ≡ []) -> ⊥)
    -> Derivable (typeEq gamma A B)
    -> Computable (isType gamma A)
    -> ((sigma : Subst) -> FitsSubst [] gamma sigma
         -> ClosedSubstComp (typeEq gamma A B) sigma)
    -> ((sigma tau : Subst) -> FitsEqSubst [] gamma sigma tau
         -> ClosedEqSubstComp (typeEq gamma A B) sigma tau)
    -> Derivable (typeEq gamma B C)
    -> ((sigma : Subst) -> FitsSubst [] gamma sigma
         -> ClosedSubstComp (typeEq gamma B C) sigma)
    -> ((sigma tau : Subst) -> FitsEqSubst [] gamma sigma tau
         -> ClosedEqSubstComp (typeEq gamma B C) sigma tau)
    -> Computable (typeEq gamma A C)
  compTransTyOpenHelper transCl neq dAB compA subAB subEqAB dBC subBC subEqBC =
    compTyEqOpen
      neq
      (transTy dAB dBC)
      compA
      (λ sigma fits ->
        packClosedSubst fits
          (transCl
            (ClosedSubstComp.closedComp (subAB sigma fits))
            (ClosedSubstComp.closedComp (subBC sigma fits))))
      (λ sigma tau fitsEq ->
        let
          closedστ = ClosedEqSubstComp.closedEqComp (subEqAB sigma tau fitsEq)
          closedτ = ClosedSubstComp.closedComp (subBC tau (fitsEqSubstRight (derivToCtxWF dBC) fitsEq))
        in
        packClosedEqSubst fitsEq
          (transCl closedστ closedτ))

  compSymTransportFamilyTyEq : {A C D F : RawType}
    -> ((sigma : Subst) -> FitsSubst [] (C ∷ []) sigma
         -> Computable (isType [] (subTy sigma F)))
    -> ((sigma tau : Subst) -> FitsEqSubst [] (C ∷ []) sigma tau
         -> Computable (typeEq [] (subTy sigma F) (subTy tau F)))
    -> ((sigma : Subst) -> FitsSubst [] (C ∷ []) sigma
         -> Computable (typeEq [] (subTy sigma F) (subTy sigma D)))
    -> ((sigma tau : Subst) -> FitsEqSubst [] (C ∷ []) sigma tau
         -> Computable (typeEq [] (subTy sigma F) (subTy tau D)))
    -> Computable (typeEq [] A C)
    -> Computable (typeEq (A ∷ []) D F)
    -> Computable (typeEq (C ∷ []) F D)
  compSymTransportFamilyTyEq
    {A = A} {C = C} {D = D} {F = F}
    tySub tySubEq symSub symSubEq compAC (compTyEqOpen neq dDF compD sub subEq) =
    compTyEqOpen
      nonemptyNeNil
      (symTy transportedEq)
      (compTyOpen
        nonemptyNeNil
        (assocTyRight transportedEq)
        (λ sigma fits -> packClosedSubst fits (tySub sigma fits))
        (λ sigma tau fitsEq -> packClosedEqSubst fitsEq (tySubEq sigma tau fitsEq)))
      (λ sigma fits -> packClosedSubst fits (symSub sigma fits))
      (λ sigma tau fitsEq -> packClosedEqSubst fitsEq (symSubEq sigma tau fitsEq))
    where
    dAC : Derivable (typeEq [] A C)
    dAC = compToDerivable compAC

    dC : Derivable (isType [] C)
    dC = compToDerivable (compTyEqRightClosed compAC)

    transportedEq : Derivable (typeEq (C ∷ []) D F)
    transportedEq = transportFamilyTyEq dAC dC dDF

    transportFits : FitsSubst (C ∷ []) (A ∷ []) idSubst
    transportFits = headTypeTransportFits dAC dC

  compSymTy : {gamma : Ctx} {A B : RawType}
    -> Computable (typeEq gamma A B)
    -> Computable (typeEq gamma B A)
  compSymTy comp@(compTyEqClosedTop _ _ _ _ _) = compSymTyClosed comp
  compSymTy comp@(compTyEqClosedSigma _ _ _ _ _ _ _) = compSymTyClosed comp
  compSymTy comp@(compTyEqClosedEq _ _ _ _ _ _ _ _) = compSymTyClosed comp
  compSymTy comp@(compTyEqClosedQtr _ _ _ _ _ _) = compSymTyClosed comp
  compSymTy {gamma = []} (compTyEqOpen neq _ _ _ _) = Empty.rec (neq refl)
  compSymTy {gamma = C ∷ gamma} (compTyEqOpen neq d compA sub subEq) =
    compSymTyOpenHelper compSymTyClosed compTransTyClosed neq d compA sub subEq

  compTransTy : {gamma : Ctx} {A B C : RawType}
    -> Computable (typeEq gamma A B)
    -> Computable (typeEq gamma B C)
    -> Computable (typeEq gamma A C)
  compTransTy compAB@(compTyEqClosedTop _ _ _ _ _) compBC = compTransTyClosed compAB compBC
  compTransTy compAB@(compTyEqClosedSigma _ _ _ _ _ _ _) compBC = compTransTyClosed compAB compBC
  compTransTy compAB@(compTyEqClosedEq _ _ _ _ _ _ _ _) compBC = compTransTyClosed compAB compBC
  compTransTy compAB@(compTyEqClosedQtr _ _ _ _ _ _) compBC = compTransTyClosed compAB compBC
  compTransTy {gamma = []} (compTyEqOpen neq _ _ _ _) _ = Empty.rec (neq refl)
  compTransTy {gamma = D ∷ gamma}
    (compTyEqOpen neq dAB compA subAB subEqAB)
    (compTyEqOpen _ dBC _ subBC subEqBC) =
    compTransTyOpenHelper compTransTyClosed neq dAB compA subAB subEqAB dBC subBC subEqBC

  compConvTm : {gamma : Ctx} {t : RawTerm} {A B : RawType}
    -> Computable (hasTy gamma t A)
    -> Computable (typeEq gamma A B)
    -> Computable (hasTy gamma t B)
  compConvTm comp@(compTmClosedTop _ _ _ _ _) compAB = compConvTmClosed comp compAB
  compConvTm comp@(compTmClosedSigma _ _ _ _ _ _ _) compAB = compConvTmClosed comp compAB
  compConvTm comp@(compTmClosedEq _ _ _ _ _ _) compAB = compConvTmClosed comp compAB
  compConvTm comp@(compTmClosedQtr _ _ _ _ _ _) compAB = compConvTmClosed comp compAB
  compConvTm {gamma = []} (compTmOpen neq _ _ _ _) _ = Empty.rec (neq refl)
  compConvTm {gamma = C ∷ gamma} (compTmOpen _ d _ _ _) compAB =
    openCompTm (conv d (compToDerivable compAB))

  compConvTmEq : {gamma : Ctx} {t u : RawTerm} {A B : RawType}
    -> Computable (termEq gamma t u A)
    -> Computable (typeEq gamma A B)
    -> Computable (termEq gamma t u B)
  compConvTmEq comp@(compTmEqClosedTop _ _ _ _ _ _) compAB = compConvTmEqClosed comp compAB
  compConvTmEq comp@(compTmEqClosedSigma _ _ _ _ _ _ _ _) compAB = compConvTmEqClosed comp compAB
  compConvTmEq comp@(compTmEqClosedEq _ _ _ _ _ _ _) compAB = compConvTmEqClosed comp compAB
  compConvTmEq comp@(compTmEqClosedQtr _ _ _ _ _ _ _ _) compAB = compConvTmEqClosed comp compAB
  compConvTmEq {gamma = []} (compTmEqOpen neq _ _ _ _) _ = Empty.rec (neq refl)
  compConvTmEq {gamma = C ∷ gamma} (compTmEqOpen _ d _ _ _) compAB =
    openCompTmEq (convEq d (compToDerivable compAB))

  compTransTm : {gamma : Ctx} {t u v : RawTerm} {A : RawType}
    -> Computable (termEq gamma t u A)
    -> Computable (termEq gamma u v A)
    -> Computable (termEq gamma t v A)
  compTransTm comp₁@(compTmEqClosedTop _ _ _ _ _ _) comp₂ = compTransTmClosed comp₁ comp₂
  compTransTm comp₁@(compTmEqClosedSigma _ _ _ _ _ _ _ _) comp₂ = compTransTmClosed comp₁ comp₂
  compTransTm comp₁@(compTmEqClosedEq _ _ _ _ _ _ _) comp₂ = compTransTmClosed comp₁ comp₂
  compTransTm comp₁@(compTmEqClosedQtr _ _ _ _ _ _ _ _) comp₂ = compTransTmClosed comp₁ comp₂
  compTransTm {gamma = []} (compTmEqOpen neq _ _ _ _) _ = Empty.rec (neq refl)
  compTransTm {gamma = C ∷ gamma}
    (compTmEqOpen neq d₁ compt₁ sub₁ subEq₁)
    (compTmEqOpen _ d₂ _ sub₂ subEq₂)
    with compTmToCompTy compt₁
  ... | compTyOpen _ _ _ subEqA =
    compTmEqOpen
      neq
      (transTm d₁ d₂)
      compt₁
      (λ sigma fits ->
        packClosedSubst fits
          (compTransTmClosed
            (ClosedSubstComp.closedComp (sub₁ sigma fits))
            (ClosedSubstComp.closedComp (sub₂ sigma fits))))
      (λ sigma tau fitsEq ->
        let
          closedστ = ClosedEqSubstComp.closedEqComp (subEq₁ sigma tau fitsEq)
          closedτ = ClosedSubstComp.closedComp (sub₂ tau (fitsEqSubstRight (derivToCtxWF d₂) fitsEq))
          closedτσ =
            compConvTmEqClosed
              closedτ
              (compSymTyClosed (ClosedEqSubstComp.closedEqComp (subEqA sigma tau fitsEq)))
        in
        packClosedEqSubst fitsEq
          (compTransTmClosed closedστ closedτσ))

  compSymTm : {gamma : Ctx} {t u : RawTerm} {A : RawType}
    -> Computable (termEq gamma t u A)
    -> Computable (termEq gamma u t A)
  compSymTm comp@(compTmEqClosedTop _ _ _ _ _ _) = compSymTmClosed comp
  compSymTm comp@(compTmEqClosedSigma _ _ _ _ _ _ _ _) = compSymTmClosed comp
  compSymTm comp@(compTmEqClosedEq _ _ _ _ _ _ _) = compSymTmClosed comp
  compSymTm comp@(compTmEqClosedQtr _ _ _ _ _ _ _ _) = compSymTmClosed comp
  compSymTm {gamma = []} (compTmEqOpen neq _ _ _ _) = Empty.rec (neq refl)
  compSymTm {gamma = B ∷ gamma} (compTmEqOpen neq d compt sub subEq) with compTmToCompTy compt
  ... | compAeq@(compTyOpen _ _ _ subEqA) =
    compTmEqOpen
      neq
      (symTm d)
      (compTmOpen
        neq
        (assocTmRight d)
        compAeq
        (λ sigma fits ->
          packClosedSubst fits
            (compTmEqRightClosed (ClosedSubstComp.closedComp (sub sigma fits))))
        (λ sigma tau fitsEq ->
          let
            closedσ = ClosedSubstComp.closedComp (sub sigma (fitsEqSubstLeft fitsEq))
            closedστ = ClosedEqSubstComp.closedEqComp (subEq sigma tau fitsEq)
          in
          packClosedEqSubst fitsEq
            (compTransTmClosed
              (compSymTmClosed closedσ)
              closedστ)))
      (λ sigma fits ->
        packClosedSubst fits
          (compSymTmClosed (ClosedSubstComp.closedComp (sub sigma fits))))
      (λ sigma tau fitsEq ->
        let
          closedσ = ClosedSubstComp.closedComp (sub sigma (fitsEqSubstLeft fitsEq))
          closedστ = ClosedEqSubstComp.closedEqComp (subEq sigma tau fitsEq)
          closedτ = ClosedSubstComp.closedComp (sub tau (fitsEqSubstRight (derivToCtxWF d) fitsEq))
          closedτσ =
            compConvTmEqClosed
              (compSymTmClosed closedτ)
              (compSymTyClosed (ClosedEqSubstComp.closedEqComp (subEqA sigma tau fitsEq)))
        in
        packClosedEqSubst fitsEq
          (compTransTmClosed
            (compTransTmClosed (compSymTmClosed closedσ) closedστ)
            closedτσ))

  weakenOneOpenTy : {A B C : RawType}
    -> Computable (isType (A ∷ []) B)
    -> CtxWF (C ∷ A ∷ [])
    -> Computable (isType (C ∷ A ∷ []) (wkTyBy 1 B))
  weakenOneOpenTy {A = A} {B = B} {C = C} (compTyOpen neq d sub subEq) wf =
    compTyOpen
      nonemptyNeNil
      (weakenTy {gamma = A ∷ []} {delta = C ∷ []} d wf)
      (λ sigma fits ->
        packClosedSubst fits
          (subst
            (λ T -> Computable (isType [] T))
            (sym (subTyWkBy sigma 1 B))
            (ClosedSubstComp.closedComp
              (sub (dropSubstBy 1 sigma) (dropFits (C ∷ []) fits)))))
      (λ sigma tau fitsEq ->
        packClosedEqSubst fitsEq
          (subst
            (λ J -> Computable J)
            (cong₂ (typeEq [])
              (sym (subTyWkBy sigma 1 B))
              (sym (subTyWkBy tau 1 B)))
            (ClosedEqSubstComp.closedEqComp
              (subEq
                (dropSubstBy 1 sigma)
                (dropSubstBy 1 tau)
                (dropFitsEq (C ∷ []) fitsEq)))))

  weakenOneOpenTm : {A B C : RawType} {t : RawTerm}
    -> Computable (hasTy (A ∷ []) t B)
    -> CtxWF (C ∷ A ∷ [])
    -> Computable (hasTy (C ∷ A ∷ []) (wkTmBy 1 t) (wkTyBy 1 B))
  weakenOneOpenTm {A = A} {B = B} {C = C} {t = t}
    (compTmOpen neq d compB sub subEq) wf =
    compTmOpen
      nonemptyNeNil
      (weakenTm {gamma = A ∷ []} {delta = C ∷ []} d wf)
      (weakenOneOpenTy compB wf)
      (λ sigma fits ->
        packClosedSubst fits
          (subst
            (λ J -> Computable J)
            (cong₂ (hasTy [])
              (sym (subTmWkBy sigma 1 t))
              (sym (subTyWkBy sigma 1 B)))
            (ClosedSubstComp.closedComp
              (sub (dropSubstBy 1 sigma) (dropFits (C ∷ []) fits)))))
      (λ sigma tau fitsEq ->
        packClosedEqSubst fitsEq
          (subst
            (λ J -> Computable J)
            (cong₃ (termEq [])
              (sym (subTmWkBy sigma 1 t))
              (sym (subTmWkBy tau 1 t))
              (sym (subTyWkBy sigma 1 B)))
            (ClosedEqSubstComp.closedEqComp
              (subEq
                (dropSubstBy 1 sigma)
                (dropSubstBy 1 tau)
                (dropFitsEq (C ∷ []) fitsEq)))))

  weakenOneOpenTmEq : {A B C : RawType} {t u : RawTerm}
    -> Computable (termEq (A ∷ []) t u B)
    -> CtxWF (C ∷ A ∷ [])
    -> Computable (termEq (C ∷ A ∷ []) (wkTmBy 1 t) (wkTmBy 1 u) (wkTyBy 1 B))
  weakenOneOpenTmEq {A = A} {B = B} {C = C} {t = t} {u = u}
    (compTmEqOpen neq d compt sub subEq) wf =
    compTmEqOpen
      nonemptyNeNil
      (weakenTmEq {gamma = A ∷ []} {delta = C ∷ []} d wf)
      (weakenOneOpenTm compt wf)
      (λ sigma fits ->
        packClosedSubst fits
          (subst
            (λ J -> Computable J)
            (cong₃ (termEq [])
              (sym (subTmWkBy sigma 1 t))
              (sym (subTmWkBy sigma 1 u))
              (sym (subTyWkBy sigma 1 B)))
            (ClosedSubstComp.closedComp
              (sub (dropSubstBy 1 sigma) (dropFits (C ∷ []) fits)))))
      (λ sigma tau fitsEq ->
        packClosedEqSubst fitsEq
          (subst
            (λ J -> Computable J)
            (cong₃ (termEq [])
              (sym (subTmWkBy sigma 1 t))
              (sym (subTmWkBy tau 1 u))
              (sym (subTyWkBy sigma 1 B)))
            (ClosedEqSubstComp.closedEqComp
              (subEq
                (dropSubstBy 1 sigma)
                (dropSubstBy 1 tau)
                (dropFitsEq (C ∷ []) fitsEq)))))

  compSubst : {gamma : Ctx} {J : JForm} {sigma : Subst}
    -> Computable J
    -> FitsSubst gamma (ctxOf J) sigma
    -> Computable (subJInto gamma sigma J)
  compSubst {gamma = []} {J = isType delta A} comp fits =
    substTyClosed (compToDerivable comp) fits
  compSubst {gamma = []} {J = typeEq delta A B} comp fits =
    substTyEqClosed (compToDerivable comp) fits
  compSubst {gamma = []} {J = hasTy delta t A} comp fits =
    substTmClosed (compToDerivable comp) fits
  compSubst {gamma = []} {J = termEq delta t u A} comp fits =
    substTmEqClosed (compToDerivable comp) fits
  compSubst {gamma = B ∷ gamma} {J = isType delta A} comp fits =
    openCompTy (substTyRule (compToDerivable comp) fits)
  compSubst {gamma = B ∷ gamma} {J = typeEq delta A C} comp fits =
    openCompTyEq (substTyEqRule (compToDerivable comp) fits)
  compSubst {gamma = B ∷ gamma} {J = hasTy delta t A} comp fits =
    openCompTm (substTmRule (compToDerivable comp) fits)
  compSubst {gamma = B ∷ gamma} {J = termEq delta t u A} comp fits =
    openCompTmEq (substTmEqRule (compToDerivable comp) fits)

  compEqSubst : {gamma : Ctx} {J : JForm} {sigma tau : Subst}
    -> Computable J
    -> FitsEqSubst gamma (ctxOf J) sigma tau
    -> Computable (eqSubJInto gamma sigma tau J)
  compEqSubst {gamma = []} {J = isType delta A} comp fitsEq =
    eqSubTyClosed (compToDerivable comp) fitsEq
  compEqSubst {gamma = []} {J = typeEq delta A B} comp fitsEq =
    eqSubTyEqClosed (compToDerivable comp) fitsEq
  compEqSubst {gamma = []} {J = hasTy delta t A} comp fitsEq =
    eqSubTmClosed (compToDerivable comp) fitsEq
  compEqSubst {gamma = []} {J = termEq delta t u A} comp fitsEq =
    eqSubTmEqClosed (compToDerivable comp) fitsEq
  compEqSubst {gamma = B ∷ gamma} {J = isType delta A} comp fitsEq =
    openCompTyEq (eqSubTyRule (compToDerivable comp) fitsEq)
  compEqSubst {gamma = B ∷ gamma} {J = typeEq delta A C} comp fitsEq =
    openCompTyEq (eqSubTyEqRule (compToDerivable comp) fitsEq)
  compEqSubst {gamma = B ∷ gamma} {J = hasTy delta t A} comp fitsEq =
    openCompTmEq (eqSubTmRule (compToDerivable comp) fitsEq)
  compEqSubst {gamma = B ∷ gamma} {J = termEq delta t u A} comp fitsEq =
    openCompTmEq (eqSubTmEqRule (compToDerivable comp) fitsEq)

  compVar : {delta gamma : Ctx} {A : RawType}
    -> CtxWF (delta ++ (A ∷ gamma))
    -> Computable (isType gamma A)
    -> Computable (hasTy (delta ++ (A ∷ gamma)) (var (length delta)) (wkTyBy (suc (length delta)) A))
  compVar wf compA = computeVar wf (compToDerivable compA)

  compSymTyClosedAcc : {A B : RawType}
    -> Computable (typeEq [] A B)
    -> Acc _<_ (closedTaskMeasure A)
    -> Computable (typeEq [] B A)
  compSymTyClosedAcc (compTyEqClosedTop d compA compB evA evB) (acc rs) =
    compTyEqClosedTop (symTy d) compB compA evB evA
  compSymTyClosedAcc
    {A = AΣ}
    (compTyEqClosedSigma {C = C} {D = D} {E = E} {F = F} d compA compB evA evB compCE compDF)
    (acc rs) with compDF
  ... | compTyEqOpen {B = F} neq dDF compD subDF subEqDF =
    let
      acHead =
        rs _ (rewriteClosedUpper {H = tySigma C D} (evalSigmaPath evA)
          (smallerClosedTask<ClosedTask {A = C} {B = tySigma C D}
            (tyDepth-fst<Sigma C D)))
      dCE : Derivable (typeEq [] C E)
      dCE = compToDerivable compCE
      dRight : Derivable (isType [] E)
      dRight = compToDerivable (compTyEqRightClosed compCE)
      transportedEq : Derivable (typeEq (E ∷ []) D F)
      transportedEq = transportFamilyTyEq dCE dRight dDF
      transportFits : FitsSubst (E ∷ []) (C ∷ []) idSubst
      transportFits = headTypeTransportFits dCE dRight
      familyAcc : (sigma : Subst) -> Acc _<_ (closedTaskMeasure (subTy sigma D))
      familyAcc sigma =
        rs (closedTaskMeasure (subTy sigma D))
          (rewriteClosedUpper {A = AΣ} {H = tySigma C D} (evalSigmaPath evA)
            (smallerClosedTask<ClosedTask {A = subTy sigma D} {B = tySigma C D}
              (subTySigmaFamilyDepth< sigma C D)))
      familySym :
        (sigma : Subst) ->
        FitsSubst [] (E ∷ []) sigma ->
        Computable (typeEq [] (subTy sigma F) (subTy sigma D))
      familySym sigma fits =
        let
          closedσ =
            subst
              (λ J -> Computable J)
              (cong₂ (typeEq [])
                (sym (subTyComp sigma idSubst D) ∙ cong (subTy sigma) (subTyId D))
                (sym (subTyComp sigma idSubst F) ∙ cong (subTy sigma) (subTyId F)))
              (ClosedSubstComp.closedComp
                (subDF (compSub sigma idSubst) (composeFits fits transportFits)))
        in
        compSymTyClosedAcc closedσ (familyAcc sigma)
      familySymEq :
        (sigma tau : Subst) ->
        FitsEqSubst [] (E ∷ []) sigma tau ->
        Computable (typeEq [] (subTy sigma F) (subTy tau D))
      familySymEq sigma tau fitsEq =
        let
          closedσ =
            subst
              (λ J -> Computable J)
              (cong₂ (typeEq [])
                (sym (subTyComp sigma idSubst D) ∙ cong (subTy sigma) (subTyId D))
                (sym (subTyComp sigma idSubst F) ∙ cong (subTy sigma) (subTyId F)))
              (ClosedSubstComp.closedComp
                (subDF (compSub sigma idSubst) (composeFits (fitsEqSubstLeft fitsEq) transportFits)))
          closedστ =
            subst
              (λ J -> Computable J)
              (cong₂ (typeEq [])
                (sym (subTyComp sigma idSubst D) ∙ cong (subTy sigma) (subTyId D))
                (sym (subTyComp tau idSubst F) ∙ cong (subTy tau) (subTyId F)))
              (ClosedEqSubstComp.closedEqComp
                (subEqDF
                  (compSub sigma idSubst)
                  (compSub tau idSubst)
                  (composeEqFits fitsEq transportFits)))
          closedτ =
            subst
              (λ J -> Computable J)
              (cong₂ (typeEq [])
                (sym (subTyComp tau idSubst D) ∙ cong (subTy tau) (subTyId D))
                (sym (subTyComp tau idSubst F) ∙ cong (subTy tau) (subTyId F)))
              (ClosedSubstComp.closedComp
                (subDF
                  (compSub tau idSubst)
                  (composeFits
                    (fitsEqSubstRight (derivToCtxWF transportedEq) fitsEq)
                    transportFits)))
        in
        compTransTyClosed
          (compTransTyClosed
            (compSymTyClosedAcc closedσ (familyAcc sigma))
            closedστ)
          (compSymTyClosedAcc closedτ (familyAcc tau))
      familyTy :
        (sigma : Subst) ->
        FitsSubst [] (E ∷ []) sigma ->
        Computable (isType [] (subTy sigma F))
      familyTy sigma fits =
        compTyEqLeft (familySym sigma fits)
      familyTyEq :
        (sigma tau : Subst) ->
        FitsEqSubst [] (E ∷ []) sigma tau ->
        Computable (typeEq [] (subTy sigma F) (subTy tau F))
      familyTyEq sigma tau fitsEq =
        let
          closedτ =
            subst
              (λ J -> Computable J)
              (cong₂ (typeEq [])
                (sym (subTyComp tau idSubst D) ∙ cong (subTy tau) (subTyId D))
                (sym (subTyComp tau idSubst F) ∙ cong (subTy tau) (subTyId F)))
              (ClosedSubstComp.closedComp
                (subDF
                  (compSub tau idSubst)
                  (composeFits
                    (fitsEqSubstRight (derivToCtxWF transportedEq) fitsEq)
                    transportFits)))
        in
        compTransTyClosed
          (familySymEq sigma tau fitsEq)
          closedτ
    in
      compTyEqClosedSigma
        (symTy d)
        compB
        compA
        evB
        evA
        (compSymTyClosedAcc compCE acHead)
        (compSymTransportFamilyTyEq
          familyTy
          familyTyEq
          familySym
          familySymEq
          compCE
          compDF)
  compSymTyClosedAcc
    (compTyEqClosedEq {C = C} {a = a} {b = b} d compA compB evA evB compCD compac compbd)
    (acc rs) =
    let
      acBase =
        rs _ (rewriteClosedUpper {H = tyEq C a b} (evalEqPath evA)
          (smallerClosedTask<ClosedTask {A = C} {B = tyEq C a b}
            (tyDepth-base<Eq C a b)))
    in
    compTyEqClosedEq
      (symTy d)
      compB
      compA
      evB
      evA
      (compSymTyClosedAcc compCD acBase)
      (compConvTmEqClosed (compSymTmClosed compac) compCD)
      (compConvTmEqClosed (compSymTmClosed compbd) compCD)
  compSymTyClosedAcc
    (compTyEqClosedQtr {C = C} d compA compB evA evB compCD)
    (acc rs) =
    let
      acBase =
        rs _ (rewriteClosedUpper {H = tyQtr C} (evalQtrPath evA)
          (smallerClosedTask<ClosedTask {A = C} {B = tyQtr C}
            (tyDepth-base<Qtr C)))
    in
    compTyEqClosedQtr
      (symTy d)
      compB
      compA
      evB
      evA
      (compSymTyClosedAcc compCD acBase)
  compSymTyClosedAcc (compTyEqOpen neq _ _ _ _) _ = Empty.rec (neq refl)

  compTransTyClosedAcc : {A B C : RawType}
    -> Computable (typeEq [] A B)
    -> Computable (typeEq [] B C)
    -> Acc _<_ (closedTaskMeasure A)
    -> Computable (typeEq [] A C)
  compTransTyClosedAcc
    (compTyEqClosedTop dAB compA compB evA evB)
    (compTyEqClosedTop dBC _ compC evB' evC)
    (acc rs) =
    compTyEqClosedTop
      (transTy dAB dBC)
      compA
      compC
      evA
      evC
  compTransTyClosedAcc
    (compTyEqClosedTop _ _ _ _ evB)
    (compTyEqClosedSigma _ _ _ evB' _ _ _)
    _ =
    Empty.rec (topNeSigma (sym (evalTopPath evB) ∙ evalSigmaPath evB'))
  compTransTyClosedAcc
    (compTyEqClosedTop _ _ _ _ evB)
    (compTyEqClosedEq _ _ _ evB' _ _ _ _)
    _ =
    Empty.rec (topNeEq (sym (evalTopPath evB) ∙ evalEqPath evB'))
  compTransTyClosedAcc
    (compTyEqClosedTop _ _ _ _ evB)
    (compTyEqClosedQtr _ _ _ evB' _ _)
    _ =
    Empty.rec (topNeQtr (sym (evalTopPath evB) ∙ evalQtrPath evB'))
  compTransTyClosedAcc
    (compTyEqClosedTop _ _ _ _ _)
    (compTyEqOpen neq _ _ _ _)
    _ =
    Empty.rec (neq refl)
  compTransTyClosedAcc
    comp₁@(compTyEqClosedSigma {C = C} {D = D} dAB compA compB evA evB compCE compDF)
    comp₂
    (acc rs)
    with compDF
  ... | compTyEqOpen neq dDF compD subDF subEqDF =
    let
      inv₂ = invertSigmaTyEq comp₂ evB
      open ClosedSigmaTyEqInv inv₂
      acHead =
        rs _ (rewriteClosedUpper {H = tySigma C D} (evalSigmaPath evA)
          (smallerClosedTask<ClosedTask {A = C} {B = tySigma C D}
            (tyDepth-fst<Sigma C D)))
      compCG = compTransTyClosedAcc compCE sigmaTyEqCompHead acHead
      compGC = compSymTyClosedAcc compCE acHead
      compFH = compTransportFamilyTyEq compGC sigmaTyEqCompFam
    in
    case compFH of λ where
      (compTyEqOpen _ dFH _ subFH subEqFH) ->
        let
          compDH =
            compTransTyOpenHelper
              compTransTyClosed
              neq
              dDF
              compD
              subDF
              subEqDF
              dFH
              subFH
              subEqFH
        in
        compTyEqClosedSigma
          (transTy dAB (compToDerivable comp₂))
          compA
          sigmaTyEqCompRight
          evA
          sigmaTyEqEvalRight
          compCG
          compDH
  compTransTyClosedAcc
    (compTyEqClosedEq {C = C} {a = a} {b = b} dAB compA compB evA evB compCD compac compbd)
    comp₂
    (acc rs) =
    let
      inv₂ = invertEqTyEq comp₂ evB
      open ClosedEqTyEqInv inv₂
      acBase =
        rs _ (rewriteClosedUpper {H = tyEq C a b} (evalEqPath evA)
          (smallerClosedTask<ClosedTask {A = C} {B = tyEq C a b}
            (tyDepth-base<Eq C a b)))
      compDG = compTransTyClosedAcc compCD eqTyEqCompBase acBase
      compeRight = compConvTmEqClosed eqTyEqCompLeftTerm (compSymTyClosedAcc compCD acBase)
      compfRight = compConvTmEqClosed eqTyEqCompRightTerm (compSymTyClosedAcc compCD acBase)
      compae = compTransTmClosed compac compeRight
      compbf = compTransTmClosed compbd compfRight
    in
    compTyEqClosedEq
      (transTy dAB (compToDerivable comp₂))
      compA
      eqTyEqCompRight
      evA
      eqTyEqEvalRight
      compDG
      compae
      compbf
  compTransTyClosedAcc
    (compTyEqClosedQtr {C = C} dAB compA compB evA evB compCD)
    comp₂
    (acc rs) =
    let
      inv₂ = invertQtrTyEq comp₂ evB
      open ClosedQtrTyEqInv inv₂
      acBase =
        rs _ (rewriteClosedUpper {H = tyQtr C} (evalQtrPath evA)
          (smallerClosedTask<ClosedTask {A = C} {B = tyQtr C}
            (tyDepth-base<Qtr C)))
    in
    compTyEqClosedQtr
      (transTy dAB (compToDerivable comp₂))
      compA
      qtrTyEqCompRight
      evA
      qtrTyEqEvalRight
      (compTransTyClosedAcc compCD qtrTyEqCompBase acBase)
  compTransTyClosedAcc (compTyEqOpen neq _ _ _ _) _ _ = Empty.rec (neq refl)

  compSymTyClosed : {A B : RawType}
    -> Computable (typeEq [] A B)
    -> Computable (typeEq [] B A)
  compSymTyClosed {A = A} comp =
    compSymTyClosedAcc comp (<-wellfounded (closedTaskMeasure A))

  compTransTyClosed : {A B C : RawType}
    -> Computable (typeEq [] A B)
    -> Computable (typeEq [] B C)
    -> Computable (typeEq [] A C)
  compTransTyClosed {A = A} comp₁ comp₂ =
    compTransTyClosedAcc comp₁ comp₂ (<-wellfounded (closedTaskMeasure A))

  compTyEqRight : {gamma : Ctx} {A B : RawType}
    -> Computable (typeEq gamma A B)
    -> Computable (isType gamma B)
  compTyEqRight comp@(compTyEqClosedTop _ _ _ _ _) = compTyEqRightClosed comp
  compTyEqRight comp@(compTyEqClosedSigma _ _ _ _ _ _ _) = compTyEqRightClosed comp
  compTyEqRight comp@(compTyEqClosedEq _ _ _ _ _ _ _ _) = compTyEqRightClosed comp
  compTyEqRight comp@(compTyEqClosedQtr _ _ _ _ _ _) = compTyEqRightClosed comp
  compTyEqRight (compTyEqOpen neq d compA sub subEq) =
    compTyOpen
      neq
      (assocTyRight d)
      (λ sigma fits ->
        packClosedSubst fits
          (compTyEqRightClosed (ClosedSubstComp.closedComp (sub sigma fits))))
      (λ sigma tau fitsEq ->
        let
          closedσ = ClosedSubstComp.closedComp (sub sigma (fitsEqSubstLeft fitsEq))
          closedστ = ClosedEqSubstComp.closedEqComp (subEq sigma tau fitsEq)
        in
        packClosedEqSubst fitsEq
          (compTransTyClosed
            (compSymTyClosed closedσ)
            closedστ))

  computeWeakenTy : {gamma delta : Ctx} {A : RawType}
    -> Derivable (isType gamma A)
    -> CtxWF (delta ++ gamma)
    -> Computable (isType (delta ++ gamma) (wkTyBy (length delta) A))
  computeWeakenTy {gamma = []} {delta = []} {A = A} d wf =
    subst
      (λ T -> Computable (isType [] T))
      (sym (wkTyBy0 A))
      (computableTheorem d)
  computeWeakenTy {gamma = B ∷ gamma} {delta = []} d wf =
    openCompTy (weakenTy {gamma = B ∷ gamma} {delta = []} d wf)
  computeWeakenTy {gamma = B ∷ gamma} {delta = C ∷ delta} d wf =
    openCompTy (weakenTy {gamma = B ∷ gamma} {delta = C ∷ delta} d wf)
  computeWeakenTy {gamma = []} {delta = B ∷ delta} d wf =
    openCompTy (weakenTy {gamma = []} {delta = B ∷ delta} d wf)

  computeWeakenTyEq : {gamma delta : Ctx} {A B : RawType}
    -> Derivable (typeEq gamma A B)
    -> CtxWF (delta ++ gamma)
    -> Computable (typeEq (delta ++ gamma) (wkTyBy (length delta) A) (wkTyBy (length delta) B))
  computeWeakenTyEq {gamma = []} {delta = []} {A = A} {B = B} d wf =
    subst
      (λ J -> Computable J)
      (cong₂ (typeEq []) (sym (wkTyBy0 A)) (sym (wkTyBy0 B)))
      (computableTheorem d)
  computeWeakenTyEq {gamma = C ∷ gamma} {delta = []} d wf =
    openCompTyEq (weakenTyEq {gamma = C ∷ gamma} {delta = []} d wf)
  computeWeakenTyEq {gamma = C ∷ gamma} {delta = D ∷ delta} d wf =
    openCompTyEq (weakenTyEq {gamma = C ∷ gamma} {delta = D ∷ delta} d wf)
  computeWeakenTyEq {gamma = []} {delta = C ∷ delta} d wf =
    openCompTyEq (weakenTyEq {gamma = []} {delta = C ∷ delta} d wf)

  computeWeakenTm : {gamma delta : Ctx} {t : RawTerm} {A : RawType}
    -> Derivable (hasTy gamma t A)
    -> CtxWF (delta ++ gamma)
    -> Computable (hasTy (delta ++ gamma) (wkTmBy (length delta) t) (wkTyBy (length delta) A))
  computeWeakenTm {gamma = []} {delta = []} {t = t} {A = A} d wf =
    subst
      (λ J -> Computable J)
      (cong₂ (hasTy []) (sym (wkTmBy0 t)) (sym (wkTyBy0 A)))
      (computableTheorem d)
  computeWeakenTm {gamma = B ∷ gamma} {delta = []} d wf =
    openCompTm (weakenTm {gamma = B ∷ gamma} {delta = []} d wf)
  computeWeakenTm {gamma = B ∷ gamma} {delta = C ∷ delta} d wf =
    openCompTm (weakenTm {gamma = B ∷ gamma} {delta = C ∷ delta} d wf)
  computeWeakenTm {gamma = []} {delta = B ∷ delta} d wf =
    openCompTm (weakenTm {gamma = []} {delta = B ∷ delta} d wf)

  computeWeakenTmEq : {gamma delta : Ctx} {t u : RawTerm} {A : RawType}
    -> Derivable (termEq gamma t u A)
    -> CtxWF (delta ++ gamma)
    -> Computable
         (termEq (delta ++ gamma) (wkTmBy (length delta) t) (wkTmBy (length delta) u)
           (wkTyBy (length delta) A))
  computeWeakenTmEq {gamma = []} {delta = []} {t = t} {u = u} {A = A} d wf =
    subst
      (λ J -> Computable J)
      (cong₃ (termEq []) (sym (wkTmBy0 t)) (sym (wkTmBy0 u)) (sym (wkTyBy0 A)))
      (computableTheorem d)
  computeWeakenTmEq {gamma = B ∷ gamma} {delta = []} d wf =
    openCompTmEq (weakenTmEq {gamma = B ∷ gamma} {delta = []} d wf)
  computeWeakenTmEq {gamma = B ∷ gamma} {delta = C ∷ delta} d wf =
    openCompTmEq (weakenTmEq {gamma = B ∷ gamma} {delta = C ∷ delta} d wf)
  computeWeakenTmEq {gamma = []} {delta = B ∷ delta} d wf =
    openCompTmEq (weakenTmEq {gamma = []} {delta = B ∷ delta} d wf)

  computeVar : {gamma delta : Ctx} {A : RawType}
    -> CtxWF (delta ++ (A ∷ gamma))
    -> Derivable (isType gamma A)
    -> Computable
         (hasTy (delta ++ (A ∷ gamma)) (var (length delta)) (wkTyBy (suc (length delta)) A))
  computeVar {gamma = gamma} {delta = []} wf dA =
    openCompTm (varStar {gamma = gamma} {delta = []} wf dA)
  computeVar {gamma = gamma} {delta = B ∷ delta} wf dA =
    openCompTm (varStar {gamma = gamma} {delta = B ∷ delta} wf dA)

  computableTheorem : {J : JForm} -> Derivable J -> Computable J
  computableTheorem (varStar wf dA) = computeVar wf dA
  computableTheorem (weakenTy d wf) = computeWeakenTy d wf
  computableTheorem (weakenTyEq d wf) = computeWeakenTyEq d wf
  computableTheorem (weakenTm d wf) = computeWeakenTm d wf
  computableTheorem (weakenTmEq d wf) = computeWeakenTmEq d wf

  computableTheorem {J = isType (B ∷ gamma) A} d =
    compTyOpen
      nonemptyNeNil
      d
      (λ sigma fits -> packClosedSubst fits (substDerivTyComp d fits (fitsToCompFits fits)))
      (λ sigma tau fitsEq -> packClosedEqSubst fitsEq (eqSubDerivTyComp d fitsEq (fitsEqToCompFitsEq fitsEq)))
  computableTheorem {J = typeEq (B ∷ gamma) A C} d =
    compTyEqOpen
      nonemptyNeNil
      d
      (computableTheorem (assocTyLeft d))
      (λ sigma fits -> packClosedSubst fits (substDerivTyEqComp d fits (fitsToCompFits fits)))
      (λ sigma tau fitsEq -> packClosedEqSubst fitsEq (eqSubDerivTyEqComp d fitsEq (fitsEqToCompFitsEq fitsEq)))
  computableTheorem {J = hasTy (B ∷ gamma) t A} d =
    compTmOpen
      nonemptyNeNil
      d
      (computableTheorem (assocTy d))
      (λ sigma fits -> packClosedSubst fits (substDerivTmComp d fits (fitsToCompFits fits)))
      (λ sigma tau fitsEq -> packClosedEqSubst fitsEq (eqSubDerivTmComp d fitsEq (fitsEqToCompFitsEq fitsEq)))
  computableTheorem {J = termEq (B ∷ gamma) t u A} d =
    compTmEqOpen
      nonemptyNeNil
      d
      (computableTheorem (assocTmLeft d))
      (λ sigma fits -> packClosedSubst fits (substDerivTmEqComp d fits (fitsToCompFits fits)))
      (λ sigma tau fitsEq -> packClosedEqSubst fitsEq (eqSubDerivTmEqComp d fitsEq (fitsEqToCompFitsEq fitsEq)))

  computableTheorem (substTyRule {gamma = []} d fits) = substTyClosed d fits
  computableTheorem (fTop {gamma = []} wf) = compFTopClosed
  computableTheorem (fSigma {gamma = []} dA dB) =
    compFSigmaClosed (computableTheorem dA) (computableTheorem dB)
  computableTheorem (fEq {gamma = []} dA da db) =
    compFEqClosed (computableTheorem dA) (computableTheorem da) (computableTheorem db)
  computableTheorem (fQtr {gamma = []} dA) =
    compFQtrClosed (computableTheorem dA)

  computableTheorem (reflTy {gamma = []} d) =
    compReflTyClosed (computableTheorem d)
  computableTheorem (symTy {gamma = []} d) =
    compSymTyClosed (computableTheorem d)
  computableTheorem (transTy {gamma = []} dAB dBC) =
    compTransTyClosed (computableTheorem dAB) (computableTheorem dBC)
  computableTheorem (substTyEqRule {gamma = []} d fits) =
    substTyEqClosed d fits
  computableTheorem (eqSubTyRule {gamma = []} d fitsEq) =
    eqSubTyClosed d fitsEq
  computableTheorem (eqSubTyEqRule {gamma = []} d fitsEq) =
    eqSubTyEqClosed d fitsEq
  computableTheorem (fSigmaEq {gamma = []} dAC dBD) =
    let
      compAC = computableTheorem dAC
      compBD = computableTheorem dBD
      compA = compTyEqLeft compAC
      compC = compTyEqRight compAC
      compSigmaA = compFSigmaClosed compA (compTyEqLeft compBD)
      compSigmaC = compFSigmaClosed compC (compTransportFamilyTy compAC (compTyEqRight compBD))
    in
    compTyEqClosedSigma
      (fSigmaEq dAC dBD)
      compSigmaA
      compSigmaC
      evalSigma
      evalSigma
      compAC
      compBD
  computableTheorem (fEqEq {gamma = []} dAC dac dbd) =
    let
      compAC = computableTheorem dAC
      compac = computableTheorem dac
      compbd = computableTheorem dbd
      compA = compTyEqLeft compAC
      compC = compTyEqRight compAC
      compa = compTmEqLeft compac
      compb = compTmEqLeft compbd
      compcA = compTmEqRightClosed compac
      compdA = compTmEqRightClosed compbd
      compc = compConvTmClosed compcA compAC
      compd = compConvTmClosed compdA compAC
      compEqA = compFEqClosed compA compa compb
      compEqC = compFEqClosed compC compc compd
    in
    compTyEqClosedEq
      (fEqEq dAC dac dbd)
      compEqA
      compEqC
      evalEq
      evalEq
      compAC
      compac
      compbd
  computableTheorem (fQtrEq {gamma = []} dAB) =
    let
      compAB = computableTheorem dAB
    in
    compTyEqClosedQtr
      (fQtrEq dAB)
      (compFQtrClosed (compTyEqLeft compAB))
      (compFQtrClosed (compTyEqRight compAB))
      evalQtr
      evalQtr
      compAB

  computableTheorem (conv {gamma = []} d dAB) =
    compConvTmClosed (computableTheorem d) (computableTheorem dAB)
  computableTheorem (substTmRule {gamma = []} d fits) =
    substTmClosed d fits
  computableTheorem (iTop {gamma = []} wf) = compITopClosed
  computableTheorem (iSigma {gamma = []} da db dSigma) =
    compISigmaClosed
      (computableTheorem da)
      (computableTheorem db)
      (computableTheorem dSigma)
  computableTheorem (eSigma {gamma = []} dM dd dm) =
    compTmEqLeft
      (compESigmaClosed
        (computableTheorem dM)
        (compReflTm (computableTheorem dd))
        (compReflTm (computableTheorem dm)))
  computableTheorem (iEq {gamma = []} da) =
    compIEqClosed (computableTheorem da)
  computableTheorem (iQtr {gamma = []} da) =
    compIQtrClosed (computableTheorem da)
  computableTheorem (eQtr {gamma = []} dL dp dl dcoh) =
    compTmEqLeft
      (compEQtrClosed
        (computableTheorem dL)
        (compReflTm (computableTheorem dp))
        (compReflTm (computableTheorem dl))
        (computableTheorem dcoh)
        (computableTheorem dcoh))

  computableTheorem (reflTm {gamma = []} d) =
    compReflTmClosed (computableTheorem d)
  computableTheorem (symTm {gamma = []} d) =
    compSymTmClosed (computableTheorem d)
  computableTheorem (transTm {gamma = []} dtu duv) =
    compTransTmClosed (computableTheorem dtu) (computableTheorem duv)
  computableTheorem (convEq {gamma = []} dtu dAB) =
    compConvTmEqClosed (computableTheorem dtu) (computableTheorem dAB)
  computableTheorem (substTmEqRule {gamma = []} d fits) =
    substTmEqClosed d fits
  computableTheorem (eqSubTmRule {gamma = []} d fitsEq) =
    eqSubTmClosed d fitsEq
  computableTheorem (eqSubTmEqRule {gamma = []} d fitsEq) =
    eqSubTmEqClosed d fitsEq
  computableTheorem (cTop {gamma = []} d) =
    compCTopClosed (computableTheorem d)
  computableTheorem (iSigmaEq {gamma = []} dac dbd dA dB) =
    let
      compac = computableTheorem dac
      compbd = computableTheorem dbd
      compA = computableTheorem dA
      compB = computableTheorem dB
      compa = compTmEqLeft compac
      compcA = compTmEqRightClosed compac
      compb = compTmEqLeft compbd
      compdA = compTmEqRightClosed compbd
      compd = compConvTmClosed compdA (compSingleEqSubstTyClosed compB compac)
      compPairLeft = compISigmaClosed compa compb (compFSigmaClosed compA compB)
      compPairRight = compISigmaClosed compcA compd (compFSigmaClosed compA compB)
    in
    compTmEqClosedSigma
      (iSigmaEq dac dbd dA dB)
      compPairLeft
      compPairRight
      evalSigma
      evalPair
      evalPair
      compac
      compbd
  computableTheorem (eSigmaEq {gamma = []} dM dd dm) =
    compESigmaClosed
      (computableTheorem dM)
      (computableTheorem dd)
      (computableTheorem dm)
  computableTheorem (cSigma {gamma = []} dM db dc dm) =
    compCSigmaClosed
      (computableTheorem dM)
      (computableTheorem db)
      (computableTheorem dc)
      (computableTheorem dm)
  computableTheorem (iEqEq {gamma = []} d) =
    compReflTm (compIEqClosed (compTmEqLeft (computableTheorem d)))
  computableTheorem (eEqStar {gamma = []} dp dA da db) =
    compEEqClosed (computableTheorem dp)
  computableTheorem (cEq {gamma = []} dp dA da db) =
    compCEqClosed (computableTheorem dp)
  computableTheorem (iQtrEq {gamma = []} da db) =
    compIQtrEqClosed (computableTheorem da) (computableTheorem db)
  computableTheorem (eQtrEq {gamma = []} dL dp dl dcoh dcoh') =
    compEQtrClosed
      (computableTheorem dL)
      (computableTheorem dp)
      (computableTheorem dl)
      (computableTheorem dcoh)
      (computableTheorem dcoh')
  computableTheorem (cQtr {gamma = []} dL da dl dcoh) =
    compCQtrClosed
      (computableTheorem dL)
      (computableTheorem da)
      (computableTheorem dl)
      (computableTheorem dcoh)

  computableTy : {gamma : Ctx} {A : RawType}
    -> Derivable (isType gamma A)
    -> Computable (isType gamma A)
  computableTy d = computableTheorem d

  computableTyEq : {gamma : Ctx} {A B : RawType}
    -> Derivable (typeEq gamma A B)
    -> Computable (typeEq gamma A B)
  computableTyEq d = computableTheorem d

  computableTm : {gamma : Ctx} {t : RawTerm} {A : RawType}
    -> Derivable (hasTy gamma t A)
    -> Computable (hasTy gamma t A)
  computableTm d = computableTheorem d

  computableTmEq : {gamma : Ctx} {t u : RawTerm} {A : RawType}
    -> Derivable (termEq gamma t u A)
    -> Computable (termEq gamma t u A)
  computableTmEq d = computableTheorem d

CanonicalForm : JForm -> Type
CanonicalForm (isType [] A) =
  Σ[ G ∈ RawType ] (A =>t G) × Derivable (typeEq [] A G)
CanonicalForm (typeEq [] A B) =
  Σ[ G ∈ RawType ] Σ[ H ∈ RawType ] (A =>t G) × (B =>t H)
CanonicalForm (hasTy [] t A) =
  Σ[ g ∈ RawTerm ] Σ[ G ∈ RawType ] (t =>e g) × (A =>t G)
CanonicalForm (termEq [] t u A) =
  Σ[ g ∈ RawTerm ] Σ[ h ∈ RawTerm ] Σ[ G ∈ RawType ] (t =>e g) × (u =>e h) × (A =>t G)
CanonicalForm (isType (_ ∷ _) A) = Unit
CanonicalForm (typeEq (_ ∷ _) A B) = Unit
CanonicalForm (hasTy (_ ∷ _) t A) = Unit
CanonicalForm (termEq (_ ∷ _) t u A) = Unit

canonicalFormTheorem : {J : JForm} -> Derivable J -> CanonicalForm J
canonicalFormTheorem {J = isType [] A} d =
  canonicalType (computableTheorem d)
canonicalFormTheorem {J = typeEq [] A B} d =
  canonicalTypeEq (computableTheorem d)
canonicalFormTheorem {J = hasTy [] t A} d =
  canonicalTerm (computableTheorem d)
canonicalFormTheorem {J = termEq [] t u A} d =
  canonicalTermEq (computableTheorem d)
canonicalFormTheorem {J = isType (_ ∷ _) A} d = tt
canonicalFormTheorem {J = typeEq (_ ∷ _) A B} d = tt
canonicalFormTheorem {J = hasTy (_ ∷ _) t A} d = tt
canonicalFormTheorem {J = termEq (_ ∷ _) t u A} d = tt
