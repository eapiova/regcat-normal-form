
{-# OPTIONS --safe #-}

module TReg.Presupposition where

open import TReg.Prelude
open import Data.Product using (Σ ; _,_)
open import Data.List.Base using ([] ; _∷_ ; _++_ ; length)
open import Data.Nat using (ℕ ; zero ; suc)
open import Data.List.Properties using (++-assoc) renaming (length-++ to length++)
open import Data.Nat.Properties using (+-suc) renaming (+-identityʳ to +-zero)
open import TReg.Syntax
open import TReg.Context
open import TReg.Substitution
open import TReg.Evaluation
open import TReg.Derivability

fitsSubstCtxWF : {gamma delta : Ctx} {sigma : Subst}
  -> FitsSubst gamma delta sigma
  -> CtxWF gamma
fitsSubstCtxWF (fitsNil wf) = wf
fitsSubstCtxWF (fitsCons fits _) = fitsSubstCtxWF fits

fitsEqSubstCtxWF : {gamma delta : Ctx} {sigma tau : Subst}
  -> FitsEqSubst gamma delta sigma tau
  -> CtxWF gamma
fitsEqSubstCtxWF (fitsEqNil wf) = wf
fitsEqSubstCtxWF (fitsEqCons fits _) = fitsEqSubstCtxWF fits

ctxSuffixWF : {delta gamma : Ctx}
  -> CtxWF (delta ++ gamma)
  -> CtxWF gamma
ctxSuffixWF {delta = []} wf = wf
ctxSuffixWF {delta = _ ∷ delta} (wfCons wf _) = ctxSuffixWF {delta = delta} wf

ctxSuffixTy : {delta gamma : Ctx} {A : RawType}
  -> CtxWF (delta ++ (A ∷ gamma))
  -> Derivable (isType gamma A)
ctxSuffixTy {delta = []} (wfCons _ dA) = dA
ctxSuffixTy {delta = _ ∷ delta} (wfCons wf _) = ctxSuffixTy {delta = delta} wf

lengthSnoc : (delta : Ctx) (A : RawType)
  -> length (delta ++ (A ∷ [])) ≡ suc (length delta)
lengthSnoc delta A =
  length++ delta {ys = A ∷ []} ∙ +-suc (length delta) zero ∙ cong suc (+-zero (length delta))

singleSubstConsKeep : (t : RawTerm)
  -> singleSubst t ≡ consSubst t (keepSubstBy 0)
singleSubstConsKeep t = refl

keepSubstBy0Id : keepSubstBy 0 ≡ idSubst
keepSubstBy0Id = refl

keepSubstCtx : ℕ -> Ctx -> Subst
keepSubstCtx k [] = keepSubstBy k
keepSubstCtx k (_ ∷ gamma) = consSubst (var k) (keepSubstCtx (suc k) gamma)

keepSubstCtx-apply : (k : ℕ) (gamma : Ctx) (n : ℕ)
  -> applySubst (keepSubstCtx k gamma) n ≡ applySubst (keepSubstBy k) n
keepSubstCtx-apply k [] n = refl
keepSubstCtx-apply k (_ ∷ gamma) zero = cong var (sym (+-zero k))
keepSubstCtx-apply k (_ ∷ gamma) (suc n) =
  keepSubstCtx-apply (suc k) gamma n ∙ cong var (sym (+-suc k n))

keepSubstCtx-subTy : (k : ℕ) (gamma : Ctx) (A : RawType)
  -> subTy (keepSubstCtx k gamma) A ≡ subTy (keepSubstBy k) A
keepSubstCtx-subTy k gamma = subTyEq (keepSubstCtx-apply k gamma)

keepSubstCtx-subTm : (k : ℕ) (gamma : Ctx) (t : RawTerm)
  -> subTm (keepSubstCtx k gamma) t ≡ subTm (keepSubstBy k) t
keepSubstCtx-subTm k gamma = subTmEq (keepSubstCtx-apply k gamma)

singleSubstCtx : RawTerm -> Ctx -> Subst
singleSubstCtx t gamma = consSubst t (keepSubstCtx 0 gamma)

singleSubstCtx-apply : (t : RawTerm) (gamma : Ctx) (n : ℕ)
  -> applySubst (singleSubstCtx t gamma) n ≡ applySubst (singleSubst t) n
singleSubstCtx-apply t gamma zero = refl
singleSubstCtx-apply t gamma (suc n) = keepSubstCtx-apply 0 gamma n

singleSubstCtx-subTy : (t : RawTerm) (gamma : Ctx) (A : RawType)
  -> subTy (singleSubstCtx t gamma) A ≡ subTy (singleSubst t) A
singleSubstCtx-subTy t gamma = subTyEq (singleSubstCtx-apply t gamma)

singleSubstCtx-subTm : (t : RawTerm) (gamma : Ctx) (m : RawTerm)
  -> subTm (singleSubstCtx t gamma) m ≡ subTm (singleSubst t) m
singleSubstCtx-subTm t gamma = subTmEq (singleSubstCtx-apply t gamma)

sigmaCompSubCtx : RawTerm -> RawTerm -> Ctx -> Subst
sigmaCompSubCtx b c gamma = consSubst c (consSubst b (keepSubstCtx 0 gamma))

sigmaCompSubCtx-apply : (b c : RawTerm) (gamma : Ctx) (n : ℕ)
  -> applySubst (sigmaCompSubCtx b c gamma) n ≡ applySubst (sigmaCompSub b c) n
sigmaCompSubCtx-apply b c gamma zero = refl
sigmaCompSubCtx-apply b c gamma (suc zero) = refl
sigmaCompSubCtx-apply b c gamma (suc (suc n)) = keepSubstCtx-apply 0 gamma n

sigmaCompSubCtx-subTy : (b c : RawTerm) (gamma : Ctx) (A : RawType)
  -> subTy (sigmaCompSubCtx b c gamma) A ≡ subTy (sigmaCompSub b c) A
sigmaCompSubCtx-subTy b c gamma = subTyEq (sigmaCompSubCtx-apply b c gamma)

sigmaCompSubCtx-subTm : (b c : RawTerm) (gamma : Ctx) (t : RawTerm)
  -> subTm (sigmaCompSubCtx b c gamma) t ≡ subTm (sigmaCompSub b c) t
sigmaCompSubCtx-subTm b c gamma = subTmEq (sigmaCompSubCtx-apply b c gamma)

headSubstCtx : Ctx -> Subst
headSubstCtx gamma = consSubst (var zero) (keepSubstCtx 1 gamma)

headSubstCtx-apply : (gamma : Ctx) (n : ℕ)
  -> applySubst (headSubstCtx gamma) n ≡ applySubst idSubst n
headSubstCtx-apply gamma zero = refl
headSubstCtx-apply gamma (suc n) = keepSubstCtx-apply 1 gamma n

headSubstCtx-subTy : (gamma : Ctx) (A : RawType)
  -> subTy (headSubstCtx gamma) A ≡ subTy idSubst A
headSubstCtx-subTy gamma = subTyEq (headSubstCtx-apply gamma)

headSubstCtx-subTm : (gamma : Ctx) (t : RawTerm)
  -> subTm (headSubstCtx gamma) t ≡ subTm idSubst t
headSubstCtx-subTm gamma = subTmEq (headSubstCtx-apply gamma)

fitsKeep : {delta gamma : Ctx}
  -> CtxWF (delta ++ gamma)
  -> FitsSubst (delta ++ gamma) gamma (keepSubstCtx (length delta) gamma)
fitsKeep {delta = delta} {gamma = []} wf =
  fitsNil {gamma = delta ++ []} {delta = []} {sigma = keepSubstBy (length delta)} wf
fitsKeep {delta = delta} {gamma = A ∷ gamma} wf =
  fitsCons liftedTail headVar
  where
  wfTail : CtxWF (((delta ++ (A ∷ [])) ++ gamma))
  wfTail = subst CtxWF (sym (++-assoc delta (A ∷ []) gamma)) wf

  tail0 : FitsSubst (((delta ++ (A ∷ [])) ++ gamma)) gamma
    (keepSubstCtx (length (delta ++ (A ∷ []))) gamma)
  tail0 = fitsKeep {delta = delta ++ (A ∷ [])} {gamma = gamma} wfTail

  tail1 : FitsSubst (delta ++ (A ∷ gamma)) gamma
    (keepSubstCtx (length (delta ++ (A ∷ []))) gamma)
  tail1 =
    subst (λ src -> FitsSubst src gamma (keepSubstCtx (length (delta ++ (A ∷ []))) gamma))
      (++-assoc delta (A ∷ []) gamma) tail0

  liftedTail : FitsSubst (delta ++ (A ∷ gamma)) gamma
    (keepSubstCtx (suc (length delta)) gamma)
  liftedTail =
    subst (λ k -> FitsSubst (delta ++ (A ∷ gamma)) gamma (keepSubstCtx k gamma))
      (lengthSnoc delta A) tail1

  headVar : Derivable
    (hasTy (delta ++ (A ∷ gamma)) (var (length delta))
      (subTy (keepSubstCtx (suc (length delta)) gamma) A))
  headVar =
    subst (λ T -> Derivable (hasTy (delta ++ (A ∷ gamma)) (var (length delta)) T))
      (renTyKeepSubstBy (suc (length delta)) A
        ∙ sym (keepSubstCtx-subTy (suc (length delta)) gamma A))
      (varStar wf (ctxSuffixTy {delta = delta} {gamma = gamma} {A = A} wf))

fitsEqKeep : {delta gamma : Ctx}
  -> CtxWF (delta ++ gamma)
  -> FitsEqSubst (delta ++ gamma) gamma
       (keepSubstCtx (length delta) gamma)
       (keepSubstCtx (length delta) gamma)
fitsEqKeep {delta = delta} {gamma = []} wf =
  fitsEqNil {gamma = delta ++ []} {delta = []}
    {sigma = keepSubstBy (length delta)} {tau = keepSubstBy (length delta)} wf
fitsEqKeep {delta = delta} {gamma = A ∷ gamma} wf =
  fitsEqCons liftedTail (reflTm headVar)
  where
  wfTail : CtxWF (((delta ++ (A ∷ [])) ++ gamma))
  wfTail = subst CtxWF (sym (++-assoc delta (A ∷ []) gamma)) wf

  tail0 : FitsEqSubst (((delta ++ (A ∷ [])) ++ gamma)) gamma
    (keepSubstCtx (length (delta ++ (A ∷ []))) gamma)
    (keepSubstCtx (length (delta ++ (A ∷ []))) gamma)
  tail0 = fitsEqKeep {delta = delta ++ (A ∷ [])} {gamma = gamma} wfTail

  tail1 : FitsEqSubst (delta ++ (A ∷ gamma)) gamma
    (keepSubstCtx (length (delta ++ (A ∷ []))) gamma)
    (keepSubstCtx (length (delta ++ (A ∷ []))) gamma)
  tail1 =
    subst (λ src -> FitsEqSubst src gamma
      (keepSubstCtx (length (delta ++ (A ∷ []))) gamma)
      (keepSubstCtx (length (delta ++ (A ∷ []))) gamma))
      (++-assoc delta (A ∷ []) gamma) tail0

  liftedTail : FitsEqSubst (delta ++ (A ∷ gamma)) gamma
    (keepSubstCtx (suc (length delta)) gamma)
    (keepSubstCtx (suc (length delta)) gamma)
  liftedTail =
    subst (λ k -> FitsEqSubst (delta ++ (A ∷ gamma)) gamma
      (keepSubstCtx k gamma) (keepSubstCtx k gamma))
      (lengthSnoc delta A) tail1

  headVar : Derivable
    (hasTy (delta ++ (A ∷ gamma)) (var (length delta))
      (subTy (keepSubstCtx (suc (length delta)) gamma) A))
  headVar =
    subst (λ T -> Derivable (hasTy (delta ++ (A ∷ gamma)) (var (length delta)) T))
      (renTyKeepSubstBy (suc (length delta)) A
        ∙ sym (keepSubstCtx-subTy (suc (length delta)) gamma A))
      (varStar wf (ctxSuffixTy {delta = delta} {gamma = gamma} {A = A} wf))

derivToCtxWF : {J : JForm}
  -> Derivable J
  -> CtxWF (ctxOf J)
derivToCtxWF (varStar wf _) = wf
derivToCtxWF (weakenTy _ wf) = wf
derivToCtxWF (weakenTyEq _ wf) = wf
derivToCtxWF (weakenTm _ wf) = wf
derivToCtxWF (weakenTmEq _ wf) = wf
derivToCtxWF (reflTy d) = derivToCtxWF d
derivToCtxWF (reflTm d) = derivToCtxWF d
derivToCtxWF (symTy d _) = derivToCtxWF d
derivToCtxWF (symTm d _ _) = derivToCtxWF d
derivToCtxWF (transTy d _) = derivToCtxWF d
derivToCtxWF (transTm d _) = derivToCtxWF d
derivToCtxWF (conv d _) = derivToCtxWF d
derivToCtxWF (convEq d _) = derivToCtxWF d
derivToCtxWF (substTyRule _ fits) = fitsSubstCtxWF fits
derivToCtxWF (substTyEqRule _ fits) = fitsSubstCtxWF fits
derivToCtxWF (substTmRule _ fits) = fitsSubstCtxWF fits
derivToCtxWF (substTmEqRule _ fits) = fitsSubstCtxWF fits
derivToCtxWF (eqSubTyRule _ fits) = fitsEqSubstCtxWF fits
derivToCtxWF (eqSubTyEqRule _ fits) = fitsEqSubstCtxWF fits
derivToCtxWF (eqSubTmRule _ fits) = fitsEqSubstCtxWF fits
derivToCtxWF (eqSubTmEqRule _ fits) = fitsEqSubstCtxWF fits
derivToCtxWF (fTop wf) = wf
derivToCtxWF (iTop wf) = wf
derivToCtxWF (cTop d) = derivToCtxWF d
derivToCtxWF (fSigma d _) = derivToCtxWF d
derivToCtxWF (fSigmaEq d _ _) = derivToCtxWF d
derivToCtxWF (iSigma d _ _) = derivToCtxWF d
derivToCtxWF (iSigmaEq d _ _ _) = derivToCtxWF d
derivToCtxWF (eSigma _ d _) = derivToCtxWF d
derivToCtxWF (eSigmaEq _ d _ _) = derivToCtxWF d
derivToCtxWF (cSigma _ _ d _ _) = derivToCtxWF d
derivToCtxWF (fEq d _ _) = derivToCtxWF d
derivToCtxWF (fEqEq d _ _) = derivToCtxWF d
derivToCtxWF (iEq d) = derivToCtxWF d
derivToCtxWF (iEqEq d) = derivToCtxWF d
derivToCtxWF (eEqStar p _ _ _) = derivToCtxWF p
derivToCtxWF (cEq p _ _ _) = derivToCtxWF p
derivToCtxWF (fQtr d) = derivToCtxWF d
derivToCtxWF (fQtrEq d) = derivToCtxWF d
derivToCtxWF (iQtr d) = derivToCtxWF d
derivToCtxWF (iQtrEq d _) = derivToCtxWF d
derivToCtxWF (eQtr _ d _ _ _) = derivToCtxWF d
derivToCtxWF (eQtrEq _ d _ _ _ _ _ _) = derivToCtxWF d
derivToCtxWF (cQtr _ d _ _ _) = derivToCtxWF d

singleFitsSubstHelper : {gamma : Ctx} {A : RawType} {t : RawTerm}
  -> Derivable (hasTy gamma t A)
  -> FitsSubst gamma (A ∷ gamma) (singleSubstCtx t gamma)
singleFitsSubstHelper {gamma = gamma} {A = A} {t = t} d =
  fitsCons
    (fitsKeep {delta = []} {gamma = gamma} (derivToCtxWF d))
    (subst (λ T -> Derivable (hasTy gamma t T))
      (sym (keepSubstCtx-subTy 0 gamma A ∙ subTyId A))
      d)

singleFitsEqSubstHelper : {gamma : Ctx} {A : RawType} {t u : RawTerm}
  -> Derivable (termEq gamma t u A)
  -> FitsEqSubst gamma (A ∷ gamma) (singleSubstCtx t gamma) (singleSubstCtx u gamma)
singleFitsEqSubstHelper {gamma = gamma} {A = A} {t = t} {u = u} d =
  fitsEqCons
    (fitsEqKeep {delta = []} {gamma = gamma} (derivToCtxWF d))
    (subst (λ T -> Derivable (termEq gamma t u T))
      (sym (keepSubstCtx-subTy 0 gamma A ∙ subTyId A))
      d)

qtrCompFitsHelper : {gamma : Ctx} {A : RawType} {a : RawTerm}
  -> Derivable (hasTy gamma a A)
  -> FitsSubst gamma (A ∷ gamma) (singleSubstCtx a gamma)
qtrCompFitsHelper d = singleFitsSubstHelper d

sigmaCompFitsHelper : {gamma : Ctx} {A B : RawType} {b c : RawTerm}
  -> Derivable (hasTy gamma b A)
  -> Derivable (hasTy gamma c (subTy (singleSubst b) B))
  -> FitsSubst gamma (B ∷ A ∷ gamma) (sigmaCompSubCtx b c gamma)
sigmaCompFitsHelper {gamma = gamma} {A = A} {B = B} {b = b} {c = c} db dc =
  fitsCons firstStep cTyped
  where
  gammaWF : CtxWF gamma
  gammaWF = derivToCtxWF db

  base : FitsSubst gamma gamma (keepSubstCtx 0 gamma)
  base = fitsKeep {delta = []} {gamma = gamma} gammaWF

  bTyped : Derivable (hasTy gamma b (subTy (keepSubstCtx 0 gamma) A))
  bTyped =
    subst (λ T -> Derivable (hasTy gamma b T))
      (sym (keepSubstCtx-subTy 0 gamma A ∙ subTyId A))
      db

  firstStep : FitsSubst gamma (A ∷ gamma) (consSubst b (keepSubstCtx 0 gamma))
  firstStep = fitsCons base bTyped

  cTyped : Derivable (hasTy gamma c (subTy (consSubst b (keepSubstCtx 0 gamma)) B))
  cTyped =
    subst (λ T -> Derivable (hasTy gamma c T))
      (sym (subTyEq (singleSubstCtx-apply b gamma) B))
      dc

varStarTy : {gamma delta : Ctx} {A : RawType}
  -> CtxWF (delta ++ (A ∷ gamma))
  -> Derivable (isType gamma A)
  -> Derivable (isType (delta ++ (A ∷ gamma)) (wkTyBy (suc (length delta)) A))
varStarTy {gamma = gamma} {delta = delta} {A = A} wf dA =
  subst (λ Γ -> Derivable (isType Γ (wkTyBy (suc (length delta)) A)))
    (++-assoc delta (A ∷ []) gamma)
    (subst (λ n -> Derivable (isType (((delta ++ (A ∷ [])) ++ gamma)) (wkTyBy n A)))
      (lengthSnoc delta A)
      (weakenTy dA wfTail))
  where
  wfTail : CtxWF (((delta ++ (A ∷ [])) ++ gamma))
  wfTail = subst CtxWF (sym (++-assoc delta (A ∷ []) gamma)) wf

singleSubstTyHelper : {gamma : Ctx} {A B : RawType} {t : RawTerm}
  -> Derivable (isType (A ∷ gamma) B)
  -> Derivable (hasTy gamma t A)
  -> Derivable (isType gamma (subTy (singleSubst t) B))
singleSubstTyHelper {gamma = gamma} {B = B} {t = t} dB dt =
  subst (λ T -> Derivable (isType gamma T))
    (singleSubstCtx-subTy t gamma B)
    (substTyRule dB (singleFitsSubstHelper dt))

singleEqSubstTyHelper : {gamma : Ctx} {A B : RawType} {t u : RawTerm}
  -> Derivable (isType (A ∷ gamma) B)
  -> Derivable (termEq gamma t u A)
  -> Derivable (typeEq gamma (subTy (singleSubst t) B) (subTy (singleSubst u) B))
singleEqSubstTyHelper {gamma = gamma} {B = B} {t = t} {u = u} dB dtu =
  subst (λ T -> Derivable (typeEq gamma T (subTy (singleSubst u) B)))
    (singleSubstCtx-subTy t gamma B)
    (subst (λ T -> Derivable (typeEq gamma (subTy (singleSubstCtx t gamma) B) T))
      (singleSubstCtx-subTy u gamma B)
      (eqSubTyRule dB (singleFitsEqSubstHelper dtu)))

sigmaCompTyHelper : {gamma : Ctx} {A B M : RawType} {b c : RawTerm}
  -> Derivable (isType ((tySigma A B) ∷ gamma) M)
  -> Derivable (hasTy gamma b A)
  -> Derivable (hasTy gamma c (subTy (singleSubst b) B))
  -> Derivable (isType gamma (subTy (singleSubst (tmPair b c)) M))
sigmaCompTyHelper {gamma = gamma} {A = A} {B = B} {M = M} {b = b} {c = c} dM db dc =
  subst (λ T -> Derivable (isType gamma T))
    (singleSubstCtx-subTy (tmPair b c) gamma M)
    (substTyRule dM singlePairFits)
  where
  sigmaTy : Derivable (isType gamma (tySigma A B))
  sigmaTy = ctxSuffixTy {delta = []} {gamma = gamma} {A = tySigma A B} (derivToCtxWF dM)

  pairTy : Derivable (hasTy gamma (tmPair b c) (tySigma A B))
  pairTy = iSigma db dc sigmaTy

  singlePairFits : FitsSubst gamma ((tySigma A B) ∷ gamma) (singleSubstCtx (tmPair b c) gamma)
  singlePairFits = singleFitsSubstHelper pairTy

qtrCompTyHelper : {gamma : Ctx} {A L : RawType} {a : RawTerm}
  -> Derivable (isType ((tyQtr A) ∷ gamma) L)
  -> Derivable (hasTy gamma a A)
  -> Derivable (isType gamma (subTy (singleSubst (tmClass a)) L))
qtrCompTyHelper {gamma = gamma} {L = L} {a = a} dL da =
  subst (λ T -> Derivable (isType gamma T))
    (singleSubstCtx-subTy (tmClass a) gamma L)
    (substTyRule dL (singleFitsSubstHelper (iQtr da)))

headTypeTransportFits : {gamma : Ctx} {A C : RawType}
  -> Derivable (typeEq gamma A C)
  -> Derivable (isType gamma C)
  -> FitsSubst (C ∷ gamma) (A ∷ gamma) (headSubstCtx gamma)
headTypeTransportFits {gamma = gamma} {A = A} {C = C} dAC dC =
  fitsCons tail headVarA
  where
  wfGamma : CtxWF gamma
  wfGamma = derivToCtxWF dC

  wfC : CtxWF (C ∷ gamma)
  wfC = wfCons wfGamma dC

  tail : FitsSubst (C ∷ gamma) gamma (keepSubstCtx 1 gamma)
  tail = fitsKeep {delta = C ∷ []} {gamma = gamma} wfC

  headVarC : Derivable (hasTy (C ∷ gamma) (var zero) (wkTyBy 1 C))
  headVarC = varStar {delta = []} {A = C} wfC dC

  headVarA0 : Derivable (hasTy (C ∷ gamma) (var zero) (wkTyBy 1 A))
  headVarA0 =
    conv headVarC
      (symTy
        (weakenTyEq {delta = C ∷ []} dAC wfC)
        (weakenTy dC wfC))

  headVarA : Derivable (hasTy (C ∷ gamma) (var zero) (subTy (keepSubstCtx 1 gamma) A))
  headVarA =
    subst (λ T -> Derivable (hasTy (C ∷ gamma) (var zero) T))
      (renTyKeepSubstBy 1 A ∙ sym (keepSubstCtx-subTy 1 gamma A))
      headVarA0

transportFamilyTy : {gamma : Ctx} {A C D : RawType}
  -> Derivable (typeEq gamma A C)
  -> Derivable (isType gamma C)
  -> Derivable (isType (A ∷ gamma) D)
  -> Derivable (isType (C ∷ gamma) D)
transportFamilyTy {gamma = gamma} {C = C} {D = D} dAC dC dD =
  subst (λ T -> Derivable (isType (C ∷ gamma) T))
    (subTyId D)
    (subst (λ T -> Derivable (isType (C ∷ gamma) T))
      (headSubstCtx-subTy gamma D)
      (substTyRule dD (headTypeTransportFits dAC dC)))

transportFamilyTyEq : {gamma : Ctx} {A C D F : RawType}
  -> Derivable (typeEq gamma A C)
  -> Derivable (isType gamma C)
  -> Derivable (typeEq (A ∷ gamma) D F)
  -> Derivable (typeEq (C ∷ gamma) D F)
transportFamilyTyEq {gamma = gamma} {C = C} {D = D} {F = F} dAC dC dDF =
  subst
    (λ T -> Derivable (typeEq (C ∷ gamma) T F))
    (subTyId D)
    (subst
      (λ T -> Derivable (typeEq (C ∷ gamma) (subTy idSubst D) T))
      (subTyId F)
      (subst
        (λ T -> Derivable (typeEq (C ∷ gamma) T (subTy idSubst F)))
        (headSubstCtx-subTy gamma D)
        (subst
          (λ T -> Derivable (typeEq (C ∷ gamma) (subTy (headSubstCtx gamma) D) T))
          (headSubstCtx-subTy gamma F)
          (substTyEqRule dDF (headTypeTransportFits dAC dC)))))

normalizeClosedFitsEq : {sigma : Subst}
  -> FitsSubst [] [] sigma
  -> FitsEqSubst [] [] sigma idSubst
normalizeClosedFitsEq {sigma = sigma} (fitsNil wf) =
  fitsEqNil {gamma = []} {delta = []} {sigma = sigma} {tau = idSubst} wf

normalizeSingleFitsEq : {A : RawType} {sigma : Subst}
  -> FitsSubst [] (A ∷ []) sigma
  -> Σ RawTerm (λ t -> FitsEqSubst [] (A ∷ []) sigma (singleSubst t))
normalizeSingleFitsEq {A = A} (fitsCons {sigma = sigma} {t = t} (fitsNil wf) dt) =
  t ,
  subst
    (λ tau -> FitsEqSubst [] (A ∷ []) (consSubst t sigma) tau)
    (sym (singleSubstConsKeep t))
    (fitsEqCons
      {gamma = []} {delta = []} {sigma = sigma} {tau = keepSubstBy 0} {A = A} {t = t} {u = t}
      (fitsEqNil {gamma = []} {delta = []} {sigma = sigma} {tau = keepSubstBy 0} wf)
      (reflTm dt))

normalizeSingleEqFitsEq : {A : RawType} {sigma tau : Subst}
  -> FitsEqSubst [] (A ∷ []) sigma tau
  -> Σ RawTerm (λ u -> FitsEqSubst [] (A ∷ []) sigma (singleSubst u))
normalizeSingleEqFitsEq {A = A} (fitsEqCons {sigma = sigma} {tau = tau} {t = t} {u = u} (fitsEqNil wf) dtu) =
  u ,
  subst
    (λ tau' -> FitsEqSubst [] (A ∷ []) (consSubst t sigma) tau')
    (sym (singleSubstConsKeep u))
    (fitsEqCons
      {gamma = []} {delta = []} {sigma = sigma} {tau = keepSubstBy 0} {A = A} {t = t} {u = u}
      (fitsEqNil {gamma = []} {delta = []} {sigma = sigma} {tau = keepSubstBy 0} wf)
      dtu)

normalizeSigmaFitsEq
  : {A B : RawType} {sigma : Subst}
  -> FitsSubst [] (B ∷ A ∷ []) sigma
  -> Σ RawTerm (λ b -> Σ RawTerm (λ c -> FitsEqSubst [] (B ∷ A ∷ []) sigma (sigmaCompSub b c)))
normalizeSigmaFitsEq {A = A} {B = B} (fitsCons {sigma = sigmaA} {t = c} inner dc) with inner
... | fitsCons {sigma = sigma} {t = b} (fitsNil wf) db =
  b , c ,
  fitsEqCons
    {gamma = []} {delta = A ∷ []} {sigma = consSubst b sigma} {tau = consSubst b idSubst}
    {A = B} {t = c} {u = c}
    (fitsEqCons
      {gamma = []} {delta = []} {sigma = sigma} {tau = idSubst}
      {A = A} {t = b} {u = b}
      (fitsEqNil {gamma = []} {delta = []} {sigma = sigma} {tau = idSubst} wf)
      (reflTm db))
    (reflTm dc)

normalizeClosedTy : {A : RawType} {sigma : Subst}
  -> Derivable (isType [] A)
  -> FitsSubst [] [] sigma
  -> Derivable (typeEq [] (subTy sigma A) A)
normalizeClosedTy {A = A} {sigma = sigma} dA fits =
  subst
    (λ T -> Derivable (typeEq [] (subTy sigma A) T))
    (subTyId A)
    (eqSubTyRule dA (normalizeClosedFitsEq fits))

normalizeClosedTyEq : {A B : RawType} {sigma : Subst}
  -> Derivable (typeEq [] A B)
  -> FitsSubst [] [] sigma
  -> Derivable (typeEq [] (subTy sigma A) B)
normalizeClosedTyEq {A = A} {B = B} {sigma = sigma} dAB fits =
  subst
    (λ T -> Derivable (typeEq [] (subTy sigma A) T))
    (subTyId B)
    (eqSubTyEqRule dAB (normalizeClosedFitsEq fits))

normalizeClosedTm : {A : RawType} {t : RawTerm} {sigma : Subst}
  -> Derivable (hasTy [] t A)
  -> FitsSubst [] [] sigma
  -> Derivable (termEq [] (subTm sigma t) t (subTy sigma A))
normalizeClosedTm {A = A} {t = t} {sigma = sigma} dt fits =
  subst
    (λ u -> Derivable (termEq [] (subTm sigma t) u (subTy sigma A)))
    (subTmId t)
    (eqSubTmRule dt (normalizeClosedFitsEq fits))

normalizeClosedTmEq : {A : RawType} {t u : RawTerm} {sigma : Subst}
  -> Derivable (termEq [] t u A)
  -> FitsSubst [] [] sigma
  -> Derivable (termEq [] (subTm sigma t) u (subTy sigma A))
normalizeClosedTmEq {A = A} {t = t} {u = u} {sigma = sigma} dtu fits =
  subst
    (λ u' -> Derivable (termEq [] (subTm sigma t) u' (subTy sigma A)))
    (subTmId u)
    (eqSubTmEqRule dtu (normalizeClosedFitsEq fits))

normalizeSingleTy : {A D : RawType} {sigma : Subst}
  -> Derivable (isType (A ∷ []) D)
  -> FitsSubst [] (A ∷ []) sigma
  -> Σ RawTerm (λ t -> Derivable (typeEq [] (subTy sigma D) (subTy (singleSubst t) D)))
normalizeSingleTy dD fits with normalizeSingleFitsEq fits
... | t , fitsEq = t , eqSubTyRule dD fitsEq

normalizeSingleTyEq : {A D F : RawType} {sigma : Subst}
  -> Derivable (typeEq (A ∷ []) D F)
  -> FitsSubst [] (A ∷ []) sigma
  -> Σ RawTerm (λ t -> Derivable (typeEq [] (subTy sigma D) (subTy (singleSubst t) F)))
normalizeSingleTyEq dDF fits with normalizeSingleFitsEq fits
... | t , fitsEq = t , eqSubTyEqRule dDF fitsEq

normalizeSingleTm : {A D : RawType} {m : RawTerm} {sigma : Subst}
  -> Derivable (hasTy (A ∷ []) m D)
  -> FitsSubst [] (A ∷ []) sigma
  -> Σ RawTerm
       (λ t -> Derivable (termEq [] (subTm sigma m) (subTm (singleSubst t) m) (subTy sigma D)))
normalizeSingleTm dm fits with normalizeSingleFitsEq fits
... | t , fitsEq = t , eqSubTmRule dm fitsEq

normalizeSingleTmEq : {A D : RawType} {m m' : RawTerm} {sigma : Subst}
  -> Derivable (termEq (A ∷ []) m m' D)
  -> FitsSubst [] (A ∷ []) sigma
  -> Σ RawTerm
       (λ t -> Derivable (termEq [] (subTm sigma m) (subTm (singleSubst t) m') (subTy sigma D)))
normalizeSingleTmEq dmm' fits with normalizeSingleFitsEq fits
... | t , fitsEq = t , eqSubTmEqRule dmm' fitsEq

normalizeSigmaTy : {A B D : RawType} {sigma : Subst}
  -> Derivable (isType (B ∷ A ∷ []) D)
  -> FitsSubst [] (B ∷ A ∷ []) sigma
  -> Σ RawTerm (λ b -> Σ RawTerm (λ c -> Derivable (typeEq [] (subTy sigma D) (subTy (sigmaCompSub b c) D))))
normalizeSigmaTy dD fits with normalizeSigmaFitsEq fits
... | b , c , fitsEq = b , c , eqSubTyRule dD fitsEq

normalizeSigmaTyEq : {A B D F : RawType} {sigma : Subst}
  -> Derivable (typeEq (B ∷ A ∷ []) D F)
  -> FitsSubst [] (B ∷ A ∷ []) sigma
  -> Σ RawTerm (λ b -> Σ RawTerm (λ c -> Derivable (typeEq [] (subTy sigma D) (subTy (sigmaCompSub b c) F))))
normalizeSigmaTyEq dDF fits with normalizeSigmaFitsEq fits
... | b , c , fitsEq = b , c , eqSubTyEqRule dDF fitsEq

normalizeSigmaTm : {A B D : RawType} {m : RawTerm} {sigma : Subst}
  -> Derivable (hasTy (B ∷ A ∷ []) m D)
  -> FitsSubst [] (B ∷ A ∷ []) sigma
  -> Σ RawTerm
       (λ b -> Σ RawTerm
         (λ c -> Derivable (termEq [] (subTm sigma m) (subTm (sigmaCompSub b c) m) (subTy sigma D))))
normalizeSigmaTm dm fits with normalizeSigmaFitsEq fits
... | b , c , fitsEq = b , c , eqSubTmRule dm fitsEq

normalizeSigmaTmEq : {A B D : RawType} {m m' : RawTerm} {sigma : Subst}
  -> Derivable (termEq (B ∷ A ∷ []) m m' D)
  -> FitsSubst [] (B ∷ A ∷ []) sigma
  -> Σ RawTerm
       (λ b -> Σ RawTerm
         (λ c -> Derivable (termEq [] (subTm sigma m) (subTm (sigmaCompSub b c) m') (subTy sigma D))))
normalizeSigmaTmEq dmm' fits with normalizeSigmaFitsEq fits
... | b , c , fitsEq = b , c , eqSubTmEqRule dmm' fitsEq

mutual
  assocTy : {gamma : Ctx} {t : RawTerm} {A : RawType}
    -> Derivable (hasTy gamma t A)
    -> Derivable (isType gamma A)
  assocTy (varStar wf dA) = varStarTy wf dA
  assocTy (weakenTm d wf) = weakenTy (assocTy d) wf
  assocTy (conv _ dAB) = assocTyRight dAB
  assocTy (substTmRule d fits) = substTyRule (assocTy d) fits
  assocTy (iTop wf) = fTop wf
  assocTy (iSigma _ _ dSigma) = dSigma
  assocTy (eSigma dM dd _) = singleSubstTyHelper dM dd
  assocTy (iEq d) = fEq (assocTy d) d d
  assocTy (iQtr d) = fQtr (assocTy d)
  assocTy (eQtr dL dp _ _ _) = singleSubstTyHelper dL dp

  assocTyLeft : {gamma : Ctx} {A B : RawType}
    -> Derivable (typeEq gamma A B)
    -> Derivable (isType gamma A)
  assocTyLeft (weakenTyEq d wf) = weakenTy (assocTyLeft d) wf
  assocTyLeft (reflTy d) = d
  assocTyLeft (symTy _ dB) = dB
  assocTyLeft (transTy d _) = assocTyLeft d
  assocTyLeft (substTyEqRule d fits) = substTyRule (assocTyLeft d) fits
  assocTyLeft (eqSubTyRule d fits) = substTyRule d (fitsEqSubstLeft fits)
  assocTyLeft (eqSubTyEqRule d fits) = substTyRule (assocTyLeft d) (fitsEqSubstLeft fits)
  assocTyLeft (fSigmaEq dAC dB _) = fSigma (assocTyLeft dAC) dB
  assocTyLeft (fEqEq dAC dac dbd) =
    fEq (assocTyLeft dAC) (assocTmLeft dac) (assocTmLeft dbd)
  assocTyLeft (fQtrEq d) = fQtr (assocTyLeft d)

  assocTyRight : {gamma : Ctx} {A B : RawType}
    -> Derivable (typeEq gamma A B)
    -> Derivable (isType gamma B)
  assocTyRight (weakenTyEq d wf) = weakenTy (assocTyRight d) wf
  assocTyRight (reflTy d) = d
  assocTyRight (symTy d _) = assocTyLeft d
  assocTyRight (transTy _ d) = assocTyRight d
  assocTyRight (substTyEqRule d fits) = substTyRule (assocTyRight d) fits
  assocTyRight (eqSubTyRule d fits) =
    substTyRule d (fitsEqSubstRight (derivToCtxWF d) fits)
  assocTyRight (eqSubTyEqRule d fits) =
    substTyRule (assocTyRight d) (fitsEqSubstRight (derivToCtxWF d) fits)
  assocTyRight (fSigmaEq dAC _ dBD) =
    fSigma (assocTyRight dAC)
      (transportFamilyTy dAC (assocTyRight dAC) (assocTyRight dBD))
  assocTyRight (fEqEq dAC dac dbd) =
    fEq (assocTyRight dAC)
      (conv (assocTmRight dac) dAC)
      (conv (assocTmRight dbd) dAC)
  assocTyRight (fQtrEq d) = fQtr (assocTyRight d)

  assocTmLeft : {gamma : Ctx} {t u : RawTerm} {A : RawType}
    -> Derivable (termEq gamma t u A)
    -> Derivable (hasTy gamma t A)
  assocTmLeft (weakenTmEq d wf) = weakenTm (assocTmLeft d) wf
  assocTmLeft (reflTm d) = d
  assocTmLeft (symTm _ du _) = du
  assocTmLeft (transTm d _) = assocTmLeft d
  assocTmLeft (convEq d dAB) = conv (assocTmLeft d) dAB
  assocTmLeft (substTmEqRule d fits) = substTmRule (assocTmLeft d) fits
  assocTmLeft (eqSubTmRule d fits) = substTmRule d (fitsEqSubstLeft fits)
  assocTmLeft (eqSubTmEqRule d fits) = substTmRule (assocTmLeft d) (fitsEqSubstLeft fits)
  assocTmLeft (cTop d) = d
  assocTmLeft (iSigmaEq d1 d2 dA dB) =
    iSigma (assocTmLeft d1) (assocTmLeft d2) (fSigma dA dB)
  assocTmLeft (eSigmaEq dM dd dmL _) =
    eSigma dM (assocTmLeft dd) dmL
  assocTmLeft (cSigma dM dSigma db dc dm) =
    eSigma dM (iSigma db dc dSigma) dm
  assocTmLeft (iEqEq d) = iEq (assocTmLeft d)
  assocTmLeft (eEqStar _ _ da _) = da
  assocTmLeft (cEq p _ _ _) = p
  assocTmLeft (iQtrEq da _) = iQtr da
  assocTmLeft (eQtrEq dL dp dBranch dlL _ _ coh _) =
    eQtr dL (assocTmLeft dp) dBranch dlL coh
  assocTmLeft (cQtr dL da dBranch dl coh) =
    eQtr dL (iQtr da) dBranch dl coh

  assocTmRight : {gamma : Ctx} {t u : RawTerm} {A : RawType}
    -> Derivable (termEq gamma t u A)
    -> Derivable (hasTy gamma u A)
  assocTmRight (weakenTmEq d wf) = weakenTm (assocTmRight d) wf
  assocTmRight (reflTm d) = d
  assocTmRight (symTm d _ _) = assocTmLeft d
  assocTmRight (transTm _ d) = assocTmRight d
  assocTmRight (convEq d dAB) = conv (assocTmRight d) dAB
  assocTmRight (substTmEqRule d fits) = substTmRule (assocTmRight d) fits
  assocTmRight (eqSubTmRule d fits) =
    conv
      (substTmRule d (fitsEqSubstRight (derivToCtxWF d) fits))
      (symTy
        (eqSubTyRule (assocTy d) fits)
        (substTyRule (assocTy d) (fitsEqSubstRight (derivToCtxWF d) fits)))
  assocTmRight (eqSubTmEqRule d fits) =
    conv
      (substTmRule (assocTmRight d) (fitsEqSubstRight (derivToCtxWF d) fits))
      (symTy
        (eqSubTyRule (assocTmTy d) fits)
        (substTyRule (assocTmTy d) (fitsEqSubstRight (derivToCtxWF d) fits)))
  assocTmRight (cTop d) = iTop (derivToCtxWF d)
  assocTmRight (iSigmaEq d1 d2 dA dB) =
    iSigma
      (assocTmRight d1)
      (conv (assocTmRight d2) (singleEqSubstTyHelper dB d1))
      (fSigma dA dB)
  assocTmRight (eSigmaEq dM dd _ dm) =
    conv
      (eSigma dM (assocTmRight dd) (assocTmRight dm))
      (symTy
        (singleEqSubstTyHelper dM dd)
        (singleSubstTyHelper dM (assocTmRight dd)))
  assocTmRight (cSigma {gamma = gamma} {A = A} {B = B} {M = M} {b = b} {c = c} {m = m} dM _ db dc dm) =
    subst
      (λ T -> Derivable (hasTy gamma (subTm (sigmaCompSub b c) m) T))
      (sigmaBranchTyComp b c M)
      (subst
        (λ T -> Derivable (hasTy gamma (subTm (sigmaCompSub b c) m) T))
        (sigmaCompSubCtx-subTy b c gamma (sigmaBranchTy M))
        (subst
          (λ u -> Derivable (hasTy gamma u (subTy (sigmaCompSubCtx b c gamma) (sigmaBranchTy M))))
          (sigmaCompSubCtx-subTm b c gamma m)
          (substTmRule dm (sigmaCompFitsHelper db dc))))
  assocTmRight (iEqEq d) =
    conv
      (iEq (assocTmRight d))
      (fEqEq
        (reflTy (assocTmTy d))
        (symTm d (assocTmRight d) (assocTmTy d))
        (symTm d (assocTmRight d) (assocTmTy d)))
  assocTmRight (eEqStar _ _ _ db) = db
  assocTmRight (cEq p dA da db) =
    conv (iEq da) (fEqEq (reflTy dA) (reflTm da) (eEqStar p dA da db))
  assocTmRight (iQtrEq _ db) = iQtr db
  assocTmRight (eQtrEq dL dp dBranch _ dlR _ _ coh') =
    conv
      (eQtr dL (assocTmRight dp) dBranch dlR coh')
      (symTy
        (singleEqSubstTyHelper dL dp)
        (singleSubstTyHelper dL (assocTmRight dp)))
  assocTmRight (cQtr {gamma = gamma} {L = L} {a = a} {l = l} dL da _ dl _) =
    subst
      (λ T -> Derivable (hasTy gamma (subTm (qtrCompSub a) l) T))
      (qtrBranchTyComp a L)
      (subst
        (λ T -> Derivable (hasTy gamma (subTm (qtrCompSub a) l) T))
        (singleSubstCtx-subTy a gamma (qtrBranchTy L))
        (subst
          (λ u -> Derivable (hasTy gamma u (subTy (singleSubstCtx a gamma) (qtrBranchTy L))))
          (singleSubstCtx-subTm a gamma l)
          (substTmRule dl (qtrCompFitsHelper da))))

  assocTmTy : {gamma : Ctx} {t u : RawTerm} {A : RawType}
    -> Derivable (termEq gamma t u A)
    -> Derivable (isType gamma A)
  assocTmTy (weakenTmEq d wf) = weakenTy (assocTmTy d) wf
  assocTmTy (reflTm d) = assocTy d
  assocTmTy (symTm d _ _) = assocTmTy d
  assocTmTy (transTm d _) = assocTmTy d
  assocTmTy (convEq _ dAB) = assocTyRight dAB
  assocTmTy (substTmEqRule d fits) = substTyRule (assocTmTy d) fits
  assocTmTy (eqSubTmRule d fits) = substTyRule (assocTy d) (fitsEqSubstLeft fits)
  assocTmTy (eqSubTmEqRule d fits) = substTyRule (assocTmTy d) (fitsEqSubstLeft fits)
  assocTmTy (cTop d) = fTop (derivToCtxWF d)
  assocTmTy (iSigmaEq _ _ dA dB) = fSigma dA dB
  assocTmTy (eSigmaEq dM dd _ _) = singleSubstTyHelper dM (assocTmLeft dd)
  assocTmTy (cSigma dM _ db dc _) = sigmaCompTyHelper dM db dc
  assocTmTy (iEqEq d) = fEq (assocTmTy d) (assocTmLeft d) (assocTmLeft d)
  assocTmTy (eEqStar _ dA _ _) = dA
  assocTmTy (cEq _ dA da db) = fEq dA da db
  assocTmTy (iQtrEq da _) = fQtr (assocTy da)
  assocTmTy (eQtrEq dL dp _ _ _ _ _ _) = singleSubstTyHelper dL (assocTmLeft dp)
  assocTmTy (cQtr dL da _ _ _) = qtrCompTyHelper dL da

  fitsEqSubstLeft : {gamma delta : Ctx} {sigma tau : Subst}
    -> FitsEqSubst gamma delta sigma tau
    -> FitsSubst gamma delta sigma
  fitsEqSubstLeft {gamma = gamma} {sigma = sigma} {tau = tau} (fitsEqNil wf) =
    fitsNil {gamma = gamma} {delta = []} {sigma = sigma} wf
  fitsEqSubstLeft (fitsEqCons fits dtu) =
    fitsCons (fitsEqSubstLeft fits) (assocTmLeft dtu)

  fitsEqSubstRight : {gamma delta : Ctx} {sigma tau : Subst}
    -> CtxWF delta
    -> FitsEqSubst gamma delta sigma tau
    -> FitsSubst gamma delta tau
  fitsEqSubstRight {gamma = gamma} {sigma = sigma} {tau = tau} _ (fitsEqNil wf) =
    fitsNil {gamma = gamma} {delta = []} {sigma = tau} wf
  fitsEqSubstRight (wfCons wfDelta dA) (fitsEqCons fits dtu) =
    fitsCons
      (fitsEqSubstRight wfDelta fits)
      (conv (assocTmRight dtu) (eqSubTyRule dA fits))
