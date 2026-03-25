{-# OPTIONS --cubical --guardedness #-}

module TReg.Presupposition where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma using (Σ ; _,_)
open import Cubical.Data.List.Base using ([] ; _∷_ ; _++_ ; length)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.List.Properties using (++-assoc ; length++)
open import Cubical.Data.Nat.Properties using (+-zero ; +-suc)
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
  length++ delta (A ∷ []) ∙ +-suc (length delta) zero ∙ cong suc (+-zero (length delta))

consKeepSubstBy : (k : ℕ)
  -> consSubst (var k) (keepSubstBy (suc k)) ≡ keepSubstBy k
consKeepSubstBy k = funExt λ where
  zero -> cong var (sym (+-zero k))
  (suc n) -> cong var (sym (+-suc k n))

singleSubstConsKeep : (t : RawTerm)
  -> singleSubst t ≡ consSubst t (keepSubstBy 0)
singleSubstConsKeep t = funExt λ where
  zero -> refl
  (suc n) -> refl

keepSubstBy0Id : keepSubstBy 0 ≡ idSubst
keepSubstBy0Id = funExt λ where
  zero -> refl
  (suc n) -> refl

fitsKeep : {delta gamma : Ctx}
  -> CtxWF (delta ++ gamma)
  -> FitsSubst (delta ++ gamma) gamma (keepSubstBy (length delta))
fitsKeep {delta = delta} {gamma = []} wf =
  fitsNil {gamma = delta ++ []} {delta = []} {sigma = keepSubstBy (length delta)} wf
fitsKeep {delta = delta} {gamma = A ∷ gamma} wf =
  subst (λ sigma -> FitsSubst (delta ++ (A ∷ gamma)) (A ∷ gamma) sigma)
    (consKeepSubstBy (length delta))
    (fitsCons liftedTail headVar)
  where
  wfTail : CtxWF (((delta ++ (A ∷ [])) ++ gamma))
  wfTail = subst CtxWF (sym (++-assoc delta (A ∷ []) gamma)) wf

  tail0 : FitsSubst (((delta ++ (A ∷ [])) ++ gamma)) gamma
    (keepSubstBy (length (delta ++ (A ∷ []))))
  tail0 = fitsKeep {delta = delta ++ (A ∷ [])} {gamma = gamma} wfTail

  tail1 : FitsSubst (delta ++ (A ∷ gamma)) gamma
    (keepSubstBy (length (delta ++ (A ∷ []))))
  tail1 =
    subst (λ src -> FitsSubst src gamma (keepSubstBy (length (delta ++ (A ∷ [])))))
      (++-assoc delta (A ∷ []) gamma) tail0

  liftedTail : FitsSubst (delta ++ (A ∷ gamma)) gamma
    (keepSubstBy (suc (length delta)))
  liftedTail =
    subst (λ sigma -> FitsSubst (delta ++ (A ∷ gamma)) gamma sigma)
      (cong keepSubstBy (lengthSnoc delta A)) tail1

  headVar : Derivable
    (hasTy (delta ++ (A ∷ gamma)) (var (length delta))
      (subTy (keepSubstBy (suc (length delta))) A))
  headVar =
    subst (λ T -> Derivable (hasTy (delta ++ (A ∷ gamma)) (var (length delta)) T))
      (renTyKeepSubstBy (suc (length delta)) A)
      (varStar wf (ctxSuffixTy {delta = delta} {gamma = gamma} {A = A} wf))

fitsEqKeep : {delta gamma : Ctx}
  -> CtxWF (delta ++ gamma)
  -> FitsEqSubst (delta ++ gamma) gamma (keepSubstBy (length delta)) (keepSubstBy (length delta))
fitsEqKeep {delta = delta} {gamma = []} wf =
  fitsEqNil {gamma = delta ++ []} {delta = []}
    {sigma = keepSubstBy (length delta)} {tau = keepSubstBy (length delta)} wf
fitsEqKeep {delta = delta} {gamma = A ∷ gamma} wf =
  subst (λ sigma -> FitsEqSubst (delta ++ (A ∷ gamma)) (A ∷ gamma) sigma sigma)
    (consKeepSubstBy (length delta))
    (fitsEqCons liftedTail (reflTm headVar))
  where
  wfTail : CtxWF (((delta ++ (A ∷ [])) ++ gamma))
  wfTail = subst CtxWF (sym (++-assoc delta (A ∷ []) gamma)) wf

  tail0 : FitsEqSubst (((delta ++ (A ∷ [])) ++ gamma)) gamma
    (keepSubstBy (length (delta ++ (A ∷ []))))
    (keepSubstBy (length (delta ++ (A ∷ []))))
  tail0 = fitsEqKeep {delta = delta ++ (A ∷ [])} {gamma = gamma} wfTail

  tail1 : FitsEqSubst (delta ++ (A ∷ gamma)) gamma
    (keepSubstBy (length (delta ++ (A ∷ []))))
    (keepSubstBy (length (delta ++ (A ∷ []))))
  tail1 =
    subst (λ src -> FitsEqSubst src gamma
      (keepSubstBy (length (delta ++ (A ∷ []))))
      (keepSubstBy (length (delta ++ (A ∷ [])))))
      (++-assoc delta (A ∷ []) gamma) tail0

  liftedTail : FitsEqSubst (delta ++ (A ∷ gamma)) gamma
    (keepSubstBy (suc (length delta)))
    (keepSubstBy (suc (length delta)))
  liftedTail =
    subst (λ sigma -> FitsEqSubst (delta ++ (A ∷ gamma)) gamma sigma sigma)
      (cong keepSubstBy (lengthSnoc delta A)) tail1

  headVar : Derivable
    (hasTy (delta ++ (A ∷ gamma)) (var (length delta))
      (subTy (keepSubstBy (suc (length delta))) A))
  headVar =
    subst (λ T -> Derivable (hasTy (delta ++ (A ∷ gamma)) (var (length delta)) T))
      (renTyKeepSubstBy (suc (length delta)) A)
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
derivToCtxWF (symTy d) = derivToCtxWF d
derivToCtxWF (symTm d) = derivToCtxWF d
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
derivToCtxWF (fSigmaEq d _) = derivToCtxWF d
derivToCtxWF (iSigma d _ _) = derivToCtxWF d
derivToCtxWF (iSigmaEq d _ _ _) = derivToCtxWF d
derivToCtxWF (eSigma _ d _) = derivToCtxWF d
derivToCtxWF (eSigmaEq _ d _) = derivToCtxWF d
derivToCtxWF (cSigma _ d _ _) = derivToCtxWF d
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
derivToCtxWF (eQtr _ d _ _) = derivToCtxWF d
derivToCtxWF (eQtrEq _ d _ _ _) = derivToCtxWF d
derivToCtxWF (cQtr _ d _ _) = derivToCtxWF d

singleFitsSubstHelper : {gamma : Ctx} {A : RawType} {t : RawTerm}
  -> Derivable (hasTy gamma t A)
  -> FitsSubst gamma (A ∷ gamma) (singleSubst t)
singleFitsSubstHelper {gamma = gamma} {A = A} {t = t} d =
  subst (λ sigma -> FitsSubst gamma (A ∷ gamma) sigma)
    (sym (singleSubstConsKeep t))
    (fitsCons
      (fitsKeep {delta = []} {gamma = gamma} (derivToCtxWF d))
      (subst (λ T -> Derivable (hasTy gamma t T))
        (sym (subTyId A) ∙ sym (cong (λ sigma -> subTy sigma A) keepSubstBy0Id))
        d))

singleFitsEqSubstHelper : {gamma : Ctx} {A : RawType} {t u : RawTerm}
  -> Derivable (termEq gamma t u A)
  -> FitsEqSubst gamma (A ∷ gamma) (singleSubst t) (singleSubst u)
singleFitsEqSubstHelper {gamma = gamma} {A = A} {t = t} {u = u} d =
  subst (λ sigma -> FitsEqSubst gamma (A ∷ gamma) sigma (singleSubst u))
    (sym (singleSubstConsKeep t))
    (subst (λ tau -> FitsEqSubst gamma (A ∷ gamma) (consSubst t (keepSubstBy 0)) tau)
      (sym (singleSubstConsKeep u))
      (fitsEqCons
        (fitsEqKeep {delta = []} {gamma = gamma} (derivToCtxWF d))
        (subst (λ T -> Derivable (termEq gamma t u T))
          (sym (subTyId A) ∙ sym (cong (λ sigma -> subTy sigma A) keepSubstBy0Id))
          d)))

qtrCompFitsHelper : {gamma : Ctx} {A : RawType} {a : RawTerm}
  -> Derivable (hasTy gamma a A)
  -> FitsSubst gamma (A ∷ gamma) (qtrCompSub a)
qtrCompFitsHelper {gamma = gamma} {A = A} {a = a} d =
  subst (λ sigma -> FitsSubst gamma (A ∷ gamma) sigma)
    (singleSubstConsKeep a ∙ cong (consSubst a) keepSubstBy0Id)
    (singleFitsSubstHelper d)

sigmaCompFitsHelper : {gamma : Ctx} {A B : RawType} {b c : RawTerm}
  -> Derivable (hasTy gamma b A)
  -> Derivable (hasTy gamma c (subTy (singleSubst b) B))
  -> FitsSubst gamma (B ∷ A ∷ gamma) (sigmaCompSub b c)
sigmaCompFitsHelper {gamma = gamma} {A = A} {B = B} {b = b} {c = c} db dc =
  subst (λ sigma -> FitsSubst gamma (B ∷ A ∷ gamma) sigma)
    finalPath
    (fitsCons firstStep cTyped)
  where
  gammaWF : CtxWF gamma
  gammaWF = derivToCtxWF db

  base : FitsSubst gamma gamma (keepSubstBy 0)
  base = fitsKeep {delta = []} {gamma = gamma} gammaWF

  bTyped : Derivable (hasTy gamma b (subTy (keepSubstBy 0) A))
  bTyped =
    subst (λ T -> Derivable (hasTy gamma b T))
      (sym (subTyId A) ∙ sym (cong (λ sigma -> subTy sigma A) keepSubstBy0Id))
      db

  firstStep : FitsSubst gamma (A ∷ gamma) (consSubst b (keepSubstBy 0))
  firstStep = fitsCons base bTyped

  cTyped : Derivable (hasTy gamma c (subTy (consSubst b (keepSubstBy 0)) B))
  cTyped =
    subst (λ T -> Derivable (hasTy gamma c T))
      (cong (λ sigma -> subTy sigma B) (singleSubstConsKeep b))
      dc

  finalPath : consSubst c (consSubst b (keepSubstBy 0)) ≡ sigmaCompSub b c
  finalPath = cong (consSubst c) (cong (consSubst b) keepSubstBy0Id)

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
singleSubstTyHelper dB dt =
  substTyRule dB (singleFitsSubstHelper dt)

singleEqSubstTyHelper : {gamma : Ctx} {A B : RawType} {t u : RawTerm}
  -> Derivable (isType (A ∷ gamma) B)
  -> Derivable (termEq gamma t u A)
  -> Derivable (typeEq gamma (subTy (singleSubst t) B) (subTy (singleSubst u) B))
singleEqSubstTyHelper dB dtu =
  eqSubTyRule dB (singleFitsEqSubstHelper dtu)

sigmaCompTyHelper : {gamma : Ctx} {A B M : RawType} {b c : RawTerm}
  -> Derivable (isType ((tySigma A B) ∷ gamma) M)
  -> Derivable (hasTy gamma b A)
  -> Derivable (hasTy gamma c (subTy (singleSubst b) B))
  -> Derivable (isType gamma (subTy (singleSubst (tmPair b c)) M))
sigmaCompTyHelper {gamma = gamma} {A = A} {B = B} {b = b} {c = c} dM db dc =
  substTyRule dM singlePairFits
  where
  sigmaTy : Derivable (isType gamma (tySigma A B))
  sigmaTy = ctxSuffixTy {delta = []} {gamma = gamma} {A = tySigma A B} (derivToCtxWF dM)

  pairTy : Derivable (hasTy gamma (tmPair b c) (tySigma A B))
  pairTy = iSigma db dc sigmaTy

  singlePairFits : FitsSubst gamma ((tySigma A B) ∷ gamma) (singleSubst (tmPair b c))
  singlePairFits = singleFitsSubstHelper pairTy

qtrCompTyHelper : {gamma : Ctx} {A L : RawType} {a : RawTerm}
  -> Derivable (isType ((tyQtr A) ∷ gamma) L)
  -> Derivable (hasTy gamma a A)
  -> Derivable (isType gamma (subTy (singleSubst (tmClass a)) L))
qtrCompTyHelper dL da =
  substTyRule dL (singleFitsSubstHelper (iQtr da))

headTypeTransportFits : {gamma : Ctx} {A C : RawType}
  -> Derivable (typeEq gamma A C)
  -> Derivable (isType gamma C)
  -> FitsSubst (C ∷ gamma) (A ∷ gamma) idSubst
headTypeTransportFits {gamma = gamma} {A = A} {C = C} dAC dC =
  subst (λ sigma -> FitsSubst (C ∷ gamma) (A ∷ gamma) sigma)
    (consKeepSubstBy 0 ∙ keepSubstBy0Id)
    (fitsCons tail headVarA)
  where
  wfGamma : CtxWF gamma
  wfGamma = derivToCtxWF dC

  wfC : CtxWF (C ∷ gamma)
  wfC = wfCons wfGamma dC

  tail : FitsSubst (C ∷ gamma) gamma (keepSubstBy 1)
  tail = fitsKeep {delta = C ∷ []} {gamma = gamma} wfC

  headVarC : Derivable (hasTy (C ∷ gamma) (var zero) (wkTyBy 1 C))
  headVarC = varStar {delta = []} {A = C} wfC dC

  headVarA0 : Derivable (hasTy (C ∷ gamma) (var zero) (wkTyBy 1 A))
  headVarA0 = conv headVarC (symTy (weakenTyEq {delta = C ∷ []} dAC wfC))

  headVarA : Derivable (hasTy (C ∷ gamma) (var zero) (subTy (keepSubstBy 1) A))
  headVarA =
    subst (λ T -> Derivable (hasTy (C ∷ gamma) (var zero) T))
      (renTyKeepSubstBy 1 A)
      headVarA0

transportFamilyTy : {gamma : Ctx} {A C D : RawType}
  -> Derivable (typeEq gamma A C)
  -> Derivable (isType gamma C)
  -> Derivable (isType (A ∷ gamma) D)
  -> Derivable (isType (C ∷ gamma) D)
transportFamilyTy {gamma = gamma} {C = C} {D = D} dAC dC dD =
  subst (λ T -> Derivable (isType (C ∷ gamma) T))
    (subTyId D)
    (substTyRule dD (headTypeTransportFits dAC dC))

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
      (substTyEqRule dDF (headTypeTransportFits dAC dC)))

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
  assocTy (eQtr dL dp _ _) = singleSubstTyHelper dL dp

  assocTyLeft : {gamma : Ctx} {A B : RawType}
    -> Derivable (typeEq gamma A B)
    -> Derivable (isType gamma A)
  assocTyLeft (weakenTyEq d wf) = weakenTy (assocTyLeft d) wf
  assocTyLeft (reflTy d) = d
  assocTyLeft (symTy d) = assocTyRight d
  assocTyLeft (transTy d _) = assocTyLeft d
  assocTyLeft (substTyEqRule d fits) = substTyRule (assocTyLeft d) fits
  assocTyLeft (eqSubTyRule d fits) = substTyRule d (fitsEqSubstLeft fits)
  assocTyLeft (eqSubTyEqRule d fits) = substTyRule (assocTyLeft d) (fitsEqSubstLeft fits)
  assocTyLeft (fSigmaEq dAC dBD) = fSigma (assocTyLeft dAC) (assocTyLeft dBD)
  assocTyLeft (fEqEq dAC dac dbd) =
    fEq (assocTyLeft dAC) (assocTmLeft dac) (assocTmLeft dbd)
  assocTyLeft (fQtrEq d) = fQtr (assocTyLeft d)

  assocTyRight : {gamma : Ctx} {A B : RawType}
    -> Derivable (typeEq gamma A B)
    -> Derivable (isType gamma B)
  assocTyRight (weakenTyEq d wf) = weakenTy (assocTyRight d) wf
  assocTyRight (reflTy d) = d
  assocTyRight (symTy d) = assocTyLeft d
  assocTyRight (transTy _ d) = assocTyRight d
  assocTyRight (substTyEqRule d fits) = substTyRule (assocTyRight d) fits
  assocTyRight (eqSubTyRule d fits) =
    substTyRule d (fitsEqSubstRight (derivToCtxWF d) fits)
  assocTyRight (eqSubTyEqRule d fits) =
    substTyRule (assocTyRight d) (fitsEqSubstRight (derivToCtxWF d) fits)
  assocTyRight (fSigmaEq dAC dBD) =
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
  assocTmLeft (symTm d) = assocTmRight d
  assocTmLeft (transTm d _) = assocTmLeft d
  assocTmLeft (convEq d dAB) = conv (assocTmLeft d) dAB
  assocTmLeft (substTmEqRule d fits) = substTmRule (assocTmLeft d) fits
  assocTmLeft (eqSubTmRule d fits) = substTmRule d (fitsEqSubstLeft fits)
  assocTmLeft (eqSubTmEqRule d fits) = substTmRule (assocTmLeft d) (fitsEqSubstLeft fits)
  assocTmLeft (cTop d) = d
  assocTmLeft (iSigmaEq d1 d2 dA dB) =
    iSigma (assocTmLeft d1) (assocTmLeft d2) (fSigma dA dB)
  assocTmLeft (eSigmaEq dM dd dm) =
    eSigma dM (assocTmLeft dd) (assocTmLeft dm)
  assocTmLeft (cSigma {gamma = gamma} {A = A} {B = B} dM db dc dm) =
    eSigma dM (iSigma db dc sigmaTy) dm
    where
    sigmaTy : Derivable (isType gamma (tySigma A B))
    sigmaTy = ctxSuffixTy {delta = []} {gamma = gamma} {A = tySigma A B} (derivToCtxWF dM)
  assocTmLeft (iEqEq d) = iEq (assocTmLeft d)
  assocTmLeft (eEqStar _ _ da _) = da
  assocTmLeft (cEq p _ _ _) = p
  assocTmLeft (iQtrEq da _) = iQtr da
  assocTmLeft (eQtrEq dL dp dl coh _) =
    eQtr dL (assocTmLeft dp) (assocTmLeft dl) coh
  assocTmLeft (cQtr dL da dl coh) =
    eQtr dL (iQtr da) dl coh

  assocTmRight : {gamma : Ctx} {t u : RawTerm} {A : RawType}
    -> Derivable (termEq gamma t u A)
    -> Derivable (hasTy gamma u A)
  assocTmRight (weakenTmEq d wf) = weakenTm (assocTmRight d) wf
  assocTmRight (reflTm d) = d
  assocTmRight (symTm d) = assocTmLeft d
  assocTmRight (transTm _ d) = assocTmRight d
  assocTmRight (convEq d dAB) = conv (assocTmRight d) dAB
  assocTmRight (substTmEqRule d fits) = substTmRule (assocTmRight d) fits
  assocTmRight (eqSubTmRule d fits) =
    conv
      (substTmRule d (fitsEqSubstRight (derivToCtxWF d) fits))
      (symTy (eqSubTyRule (assocTy d) fits))
  assocTmRight (eqSubTmEqRule d fits) =
    conv
      (substTmRule (assocTmRight d) (fitsEqSubstRight (derivToCtxWF d) fits))
      (symTy (eqSubTyRule (assocTmTy d) fits))
  assocTmRight (cTop d) = iTop (derivToCtxWF d)
  assocTmRight (iSigmaEq d1 d2 dA dB) =
    iSigma
      (assocTmRight d1)
      (conv (assocTmRight d2) (singleEqSubstTyHelper dB d1))
      (fSigma dA dB)
  assocTmRight (eSigmaEq dM dd dm) =
    conv
      (eSigma dM (assocTmRight dd) (assocTmRight dm))
      (symTy (singleEqSubstTyHelper dM dd))
  assocTmRight (cSigma {gamma = gamma} {A = A} {B = B} {M = M} {b = b} {c = c} {m = m} dM db dc dm) =
    subst
      (λ T -> Derivable (hasTy gamma (subTm (sigmaCompSub b c) m) T))
      (sigmaBranchTyComp b c M)
      (substTmRule dm (sigmaCompFitsHelper db dc))
  assocTmRight (iEqEq d) =
    conv
      (iEq (assocTmRight d))
      (fEqEq (reflTy (assocTmTy d)) (symTm d) (symTm d))
  assocTmRight (eEqStar _ _ _ db) = db
  assocTmRight (cEq p dA da db) =
    conv (iEq da) (fEqEq (reflTy dA) (reflTm da) (eEqStar p dA da db))
  assocTmRight (iQtrEq _ db) = iQtr db
  assocTmRight (eQtrEq dL dp dl _ coh') =
    conv
      (eQtr dL (assocTmRight dp) (assocTmRight dl) coh')
      (symTy (singleEqSubstTyHelper dL dp))
  assocTmRight (cQtr {gamma = gamma} {L = L} {a = a} {l = l} dL da dl _) =
    subst
      (λ T -> Derivable (hasTy gamma (subTm (qtrCompSub a) l) T))
      (qtrBranchTyComp a L)
      (substTmRule dl (qtrCompFitsHelper da))

  assocTmTy : {gamma : Ctx} {t u : RawTerm} {A : RawType}
    -> Derivable (termEq gamma t u A)
    -> Derivable (isType gamma A)
  assocTmTy (weakenTmEq d wf) = weakenTy (assocTmTy d) wf
  assocTmTy (reflTm d) = assocTy d
  assocTmTy (symTm d) = assocTmTy d
  assocTmTy (transTm d _) = assocTmTy d
  assocTmTy (convEq _ dAB) = assocTyRight dAB
  assocTmTy (substTmEqRule d fits) = substTyRule (assocTmTy d) fits
  assocTmTy (eqSubTmRule d fits) = substTyRule (assocTy d) (fitsEqSubstLeft fits)
  assocTmTy (eqSubTmEqRule d fits) = substTyRule (assocTmTy d) (fitsEqSubstLeft fits)
  assocTmTy (cTop d) = fTop (derivToCtxWF d)
  assocTmTy (iSigmaEq _ _ dA dB) = fSigma dA dB
  assocTmTy (eSigmaEq dM dd _) = singleSubstTyHelper dM (assocTmLeft dd)
  assocTmTy (cSigma dM db dc _) = sigmaCompTyHelper dM db dc
  assocTmTy (iEqEq d) = fEq (assocTmTy d) (assocTmLeft d) (assocTmLeft d)
  assocTmTy (eEqStar _ dA _ _) = dA
  assocTmTy (cEq _ dA da db) = fEq dA da db
  assocTmTy (iQtrEq da _) = fQtr (assocTy da)
  assocTmTy (eQtrEq dL dp _ _ _) = singleSubstTyHelper dL (assocTmLeft dp)
  assocTmTy (cQtr dL da _ _) = qtrCompTyHelper dL da

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
