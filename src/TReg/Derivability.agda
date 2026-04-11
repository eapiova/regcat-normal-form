
{-# OPTIONS --safe #-}

module TReg.Derivability where

open import Cubical.Foundations.Prelude
open import Cubical.Data.List.Base using (List ; [] ; _∷_ ; _++_ ; length)
open import Cubical.Data.Nat using (zero ; suc)

open import TReg.Syntax
open import TReg.Context
open import TReg.Substitution
open import TReg.Evaluation

sigmaMotSub : Subst
sigmaMotSub = replace0By 2 (tmPair (var (suc zero)) (var zero))

sigmaBranchTy : RawType -> RawType
sigmaBranchTy M = subTy sigmaMotSub M

qtrBranchSub : Subst
qtrBranchSub = replace0By 1 (tmClass (var zero))

qtrCohSub : Subst
qtrCohSub = replace0By 2 (tmClass (var (suc zero)))

qtrBranchTy : RawType -> RawType
qtrBranchTy L = subTy qtrBranchSub L

qtrCohTy : RawType -> RawType
qtrCohTy L = subTy qtrCohSub L

qtrSecondBranchRen : Ren
qtrSecondBranchRen = keep0RenBy 1

mutual
  data Derivable : JForm -> Type where
    varStar : {gamma delta : Ctx} {A : RawType}
      -> CtxWF (delta ++ (A ∷ gamma))
      -> Derivable (isType gamma A)
      -> Derivable
           (hasTy (delta ++ (A ∷ gamma)) (var (length delta)) (wkTyBy (suc (length delta)) A))

    weakenTy : {gamma delta : Ctx} {A : RawType}
      -> Derivable (isType gamma A)
      -> CtxWF (delta ++ gamma)
      -> Derivable (isType (delta ++ gamma) (wkTyBy (length delta) A))

    weakenTyEq : {gamma delta : Ctx} {A B : RawType}
      -> Derivable (typeEq gamma A B)
      -> CtxWF (delta ++ gamma)
      -> Derivable (typeEq (delta ++ gamma) (wkTyBy (length delta) A) (wkTyBy (length delta) B))

    weakenTm : {gamma delta : Ctx} {t : RawTerm} {A : RawType}
      -> Derivable (hasTy gamma t A)
      -> CtxWF (delta ++ gamma)
      -> Derivable (hasTy (delta ++ gamma) (wkTmBy (length delta) t) (wkTyBy (length delta) A))

    weakenTmEq : {gamma delta : Ctx} {t u : RawTerm} {A : RawType}
      -> Derivable (termEq gamma t u A)
      -> CtxWF (delta ++ gamma)
      -> Derivable
           (termEq (delta ++ gamma) (wkTmBy (length delta) t) (wkTmBy (length delta) u)
             (wkTyBy (length delta) A))

    reflTy : {gamma : Ctx} {A : RawType}
      -> Derivable (isType gamma A)
      -> Derivable (typeEq gamma A A)

    reflTm : {gamma : Ctx} {t : RawTerm} {A : RawType}
      -> Derivable (hasTy gamma t A)
      -> Derivable (termEq gamma t t A)

    symTy : {gamma : Ctx} {A B : RawType}
      -> Derivable (typeEq gamma A B)
      -> Derivable (isType gamma B)
      -> Derivable (typeEq gamma B A)

    symTm : {gamma : Ctx} {t u : RawTerm} {A : RawType}
      -> Derivable (termEq gamma t u A)
      -> Derivable (hasTy gamma u A)
      -> Derivable (isType gamma A)
      -> Derivable (termEq gamma u t A)

    transTy : {gamma : Ctx} {A B C : RawType}
      -> Derivable (typeEq gamma A B)
      -> Derivable (typeEq gamma B C)
      -> Derivable (typeEq gamma A C)

    transTm : {gamma : Ctx} {t u v : RawTerm} {A : RawType}
      -> Derivable (termEq gamma t u A)
      -> Derivable (termEq gamma u v A)
      -> Derivable (termEq gamma t v A)

    conv : {gamma : Ctx} {t : RawTerm} {A B : RawType}
      -> Derivable (hasTy gamma t A)
      -> Derivable (typeEq gamma A B)
      -> Derivable (hasTy gamma t B)

    convEq : {gamma : Ctx} {t u : RawTerm} {A B : RawType}
      -> Derivable (termEq gamma t u A)
      -> Derivable (typeEq gamma A B)
      -> Derivable (termEq gamma t u B)

    substTyRule : {gamma delta : Ctx} {sigma : Subst} {A : RawType}
      -> Derivable (isType delta A)
      -> FitsSubst gamma delta sigma
      -> Derivable (isType gamma (subTy sigma A))

    substTyEqRule : {gamma delta : Ctx} {sigma : Subst} {A B : RawType}
      -> Derivable (typeEq delta A B)
      -> FitsSubst gamma delta sigma
      -> Derivable (typeEq gamma (subTy sigma A) (subTy sigma B))

    substTmRule : {gamma delta : Ctx} {sigma : Subst} {t : RawTerm} {A : RawType}
      -> Derivable (hasTy delta t A)
      -> FitsSubst gamma delta sigma
      -> Derivable (hasTy gamma (subTm sigma t) (subTy sigma A))

    substTmEqRule : {gamma delta : Ctx} {sigma : Subst} {t u : RawTerm} {A : RawType}
      -> Derivable (termEq delta t u A)
      -> FitsSubst gamma delta sigma
      -> Derivable (termEq gamma (subTm sigma t) (subTm sigma u) (subTy sigma A))

    eqSubTyRule : {gamma delta : Ctx} {sigma tau : Subst} {A : RawType}
      -> Derivable (isType delta A)
      -> FitsEqSubst gamma delta sigma tau
      -> Derivable (typeEq gamma (subTy sigma A) (subTy tau A))

    eqSubTyEqRule : {gamma delta : Ctx} {sigma tau : Subst} {A B : RawType}
      -> Derivable (typeEq delta A B)
      -> FitsEqSubst gamma delta sigma tau
      -> Derivable (typeEq gamma (subTy sigma A) (subTy tau B))

    eqSubTmRule : {gamma delta : Ctx} {sigma tau : Subst} {t : RawTerm} {A : RawType}
      -> Derivable (hasTy delta t A)
      -> FitsEqSubst gamma delta sigma tau
      -> Derivable (termEq gamma (subTm sigma t) (subTm tau t) (subTy sigma A))

    eqSubTmEqRule : {gamma delta : Ctx} {sigma tau : Subst} {t u : RawTerm} {A : RawType}
      -> Derivable (termEq delta t u A)
      -> FitsEqSubst gamma delta sigma tau
      -> Derivable (termEq gamma (subTm sigma t) (subTm tau u) (subTy sigma A))

    fTop : {gamma : Ctx}
      -> CtxWF gamma
      -> Derivable (isType gamma tyTop)

    iTop : {gamma : Ctx}
      -> CtxWF gamma
      -> Derivable (hasTy gamma tmStar tyTop)

    cTop : {gamma : Ctx} {t : RawTerm}
      -> Derivable (hasTy gamma t tyTop)
      -> Derivable (termEq gamma t tmStar tyTop)

    fSigma : {gamma : Ctx} {A B : RawType}
      -> Derivable (isType gamma A)
      -> Derivable (isType (A ∷ gamma) B)
      -> Derivable (isType gamma (tySigma A B))

    fSigmaEq : {gamma : Ctx} {A B C D : RawType}
      -> Derivable (typeEq gamma A C)
      -> Derivable (isType (A ∷ gamma) B)
      -> Derivable (typeEq (A ∷ gamma) B D)
      -> Derivable (typeEq gamma (tySigma A B) (tySigma C D))

    iSigma : {gamma : Ctx} {a b : RawTerm} {A B : RawType}
      -> Derivable (hasTy gamma a A)
      -> Derivable (hasTy gamma b (subTy (singleSubst a) B))
      -> Derivable (isType gamma (tySigma A B))
      -> Derivable (hasTy gamma (tmPair a b) (tySigma A B))

    iSigmaEq : {gamma : Ctx} {a b c d : RawTerm} {A B : RawType}
      -> Derivable (termEq gamma a c A)
      -> Derivable (termEq gamma b d (subTy (singleSubst a) B))
      -> Derivable (isType gamma A)
      -> Derivable (isType (A ∷ gamma) B)
      -> Derivable (termEq gamma (tmPair a b) (tmPair c d) (tySigma A B))

    eSigma : {gamma : Ctx} {A B M : RawType} {d m : RawTerm}
      -> Derivable (isType ((tySigma A B) ∷ gamma) M)
      -> Derivable (hasTy gamma d (tySigma A B))
      -> Derivable (hasTy (B ∷ A ∷ gamma) m (sigmaBranchTy M))
      -> Derivable (hasTy gamma (tmElSigma d m) (subTy (singleSubst d) M))

    eSigmaEq : {gamma : Ctx} {A B M : RawType} {d d' m m' : RawTerm}
      -> Derivable (isType ((tySigma A B) ∷ gamma) M)
      -> Derivable (termEq gamma d d' (tySigma A B))
      -> Derivable (hasTy (B ∷ A ∷ gamma) m (sigmaBranchTy M))
      -> Derivable (termEq (B ∷ A ∷ gamma) m m' (sigmaBranchTy M))
      -> Derivable
           (termEq gamma (tmElSigma d m) (tmElSigma d' m') (subTy (singleSubst d) M))

    cSigma : {gamma : Ctx} {A B M : RawType} {b c m : RawTerm}
      -> Derivable (isType ((tySigma A B) ∷ gamma) M)
      -> Derivable (isType gamma (tySigma A B))
      -> Derivable (hasTy gamma b A)
      -> Derivable (hasTy gamma c (subTy (singleSubst b) B))
      -> Derivable (hasTy (B ∷ A ∷ gamma) m (sigmaBranchTy M))
      -> Derivable
           (termEq gamma (tmElSigma (tmPair b c) m) (subTm (sigmaCompSub b c) m)
             (subTy (singleSubst (tmPair b c)) M))

    fEq : {gamma : Ctx} {A : RawType} {a b : RawTerm}
      -> Derivable (isType gamma A)
      -> Derivable (hasTy gamma a A)
      -> Derivable (hasTy gamma b A)
      -> Derivable (isType gamma (tyEq A a b))

    fEqEq : {gamma : Ctx} {A C : RawType} {a b c d : RawTerm}
      -> Derivable (typeEq gamma A C)
      -> Derivable (termEq gamma a c A)
      -> Derivable (termEq gamma b d A)
      -> Derivable (typeEq gamma (tyEq A a b) (tyEq C c d))

    iEq : {gamma : Ctx} {A : RawType} {a : RawTerm}
      -> Derivable (hasTy gamma a A)
      -> Derivable (hasTy gamma tmR (tyEq A a a))

    iEqEq : {gamma : Ctx} {A : RawType} {a b : RawTerm}
      -> Derivable (termEq gamma a b A)
      -> Derivable (termEq gamma tmR tmR (tyEq A a a))

    eEqStar : {gamma : Ctx} {A : RawType} {a b p : RawTerm}
      -> Derivable (hasTy gamma p (tyEq A a b))
      -> Derivable (isType gamma A)
      -> Derivable (hasTy gamma a A)
      -> Derivable (hasTy gamma b A)
      -> Derivable (termEq gamma a b A)

    cEq : {gamma : Ctx} {A : RawType} {a b p : RawTerm}
      -> Derivable (hasTy gamma p (tyEq A a b))
      -> Derivable (isType gamma A)
      -> Derivable (hasTy gamma a A)
      -> Derivable (hasTy gamma b A)
      -> Derivable (termEq gamma p tmR (tyEq A a b))

    fQtr : {gamma : Ctx} {A : RawType}
      -> Derivable (isType gamma A)
      -> Derivable (isType gamma (tyQtr A))

    fQtrEq : {gamma : Ctx} {A B : RawType}
      -> Derivable (typeEq gamma A B)
      -> Derivable (typeEq gamma (tyQtr A) (tyQtr B))

    iQtr : {gamma : Ctx} {A : RawType} {a : RawTerm}
      -> Derivable (hasTy gamma a A)
      -> Derivable (hasTy gamma (tmClass a) (tyQtr A))

    iQtrEq : {gamma : Ctx} {A : RawType} {a b : RawTerm}
      -> Derivable (hasTy gamma a A)
      -> Derivable (hasTy gamma b A)
      -> Derivable (termEq gamma (tmClass a) (tmClass b) (tyQtr A))

    eQtr : {gamma : Ctx} {A L : RawType} {l p : RawTerm}
      -> Derivable (isType ((tyQtr A) ∷ gamma) L)
      -> Derivable (hasTy gamma p (tyQtr A))
      -> Derivable (isType (A ∷ gamma) (qtrBranchTy L))
      -> Derivable (hasTy (A ∷ gamma) l (qtrBranchTy L))
      -> Derivable
           (termEq (wkTyBy 1 A ∷ A ∷ gamma)
             (wkTmBy 1 l)
             (renTm qtrSecondBranchRen l)
             (qtrCohTy L))
      -> Derivable (hasTy gamma (tmElQtr l p) (subTy (singleSubst p) L))

    eQtrEq : {gamma : Ctx} {A L : RawType} {l l' p p' : RawTerm}
      -> Derivable (isType ((tyQtr A) ∷ gamma) L)
      -> Derivable (termEq gamma p p' (tyQtr A))
      -> Derivable (isType (A ∷ gamma) (qtrBranchTy L))
      -> Derivable (hasTy (A ∷ gamma) l (qtrBranchTy L))
      -> Derivable (hasTy (A ∷ gamma) l' (qtrBranchTy L))
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
      -> Derivable (termEq gamma (tmElQtr l p) (tmElQtr l' p') (subTy (singleSubst p) L))

    cQtr : {gamma : Ctx} {A L : RawType} {a l : RawTerm}
      -> Derivable (isType ((tyQtr A) ∷ gamma) L)
      -> Derivable (hasTy gamma a A)
      -> Derivable (isType (A ∷ gamma) (qtrBranchTy L))
      -> Derivable (hasTy (A ∷ gamma) l (qtrBranchTy L))
      -> Derivable
           (termEq (wkTyBy 1 A ∷ A ∷ gamma)
             (wkTmBy 1 l)
             (renTm qtrSecondBranchRen l)
             (qtrCohTy L))
      -> Derivable
           (termEq gamma (tmElQtr l (tmClass a)) (subTm (qtrCompSub a) l)
             (subTy (singleSubst (tmClass a)) L))

  data CtxWF : Ctx -> Type where
    wfNil : CtxWF []
    wfCons : {gamma : Ctx} {A : RawType}
      -> CtxWF gamma
      -> Derivable (isType gamma A)
      -> CtxWF (A ∷ gamma)

  data FitsSubst : Ctx -> Ctx -> Subst -> Type where
    fitsNil : {gamma delta : Ctx} {sigma : Subst}
      -> CtxWF gamma
      -> FitsSubst gamma [] sigma
    fitsCons : {gamma delta : Ctx} {sigma : Subst} {A : RawType} {t : RawTerm}
      -> FitsSubst gamma delta sigma
      -> Derivable (hasTy gamma t (subTy sigma A))
      -> FitsSubst gamma (A ∷ delta) (consSubst t sigma)

  data FitsEqSubst : Ctx -> Ctx -> Subst -> Subst -> Type where
    fitsEqNil : {gamma delta : Ctx} {sigma tau : Subst}
      -> CtxWF gamma
      -> FitsEqSubst gamma [] sigma tau
    fitsEqCons : {gamma delta : Ctx} {sigma tau : Subst} {A : RawType} {t u : RawTerm}
      -> FitsEqSubst gamma delta sigma tau
      -> Derivable (termEq gamma t u (subTy sigma A))
      -> FitsEqSubst gamma (A ∷ delta) (consSubst t sigma) (consSubst u tau)
