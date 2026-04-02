{-# OPTIONS --safe #-}

module TReg.Computability where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Empty.Base using (⊥)
open import Cubical.Data.List.Base using ([] ; _∷_)

open import TReg.Syntax
open import TReg.Context
open import TReg.Substitution
open import TReg.Evaluation
open import TReg.Derivability

closedSubJ : Subst -> JForm -> JForm
closedSubJ sigma (isType gamma A) = isType [] (subTy sigma A)
closedSubJ sigma (typeEq gamma A B) = typeEq [] (subTy sigma A) (subTy sigma B)
closedSubJ sigma (hasTy gamma t A) = hasTy [] (subTm sigma t) (subTy sigma A)
closedSubJ sigma (termEq gamma t u A) =
  termEq [] (subTm sigma t) (subTm sigma u) (subTy sigma A)

closedEqSubJ : Subst -> Subst -> JForm -> JForm
closedEqSubJ sigma tau (isType gamma A) = typeEq [] (subTy sigma A) (subTy tau A)
closedEqSubJ sigma tau (typeEq gamma A B) = typeEq [] (subTy sigma A) (subTy tau B)
closedEqSubJ sigma tau (hasTy gamma t A) =
  termEq [] (subTm sigma t) (subTm tau t) (subTy sigma A)
closedEqSubJ sigma tau (termEq gamma t u A) =
  termEq [] (subTm sigma t) (subTm tau u) (subTy sigma A)

data Computable : JForm -> Type where
  compTyClosedTop : {A : RawType}
    -> Derivable (isType [] A)
    -> A =>t tyTop
    -> Derivable (typeEq [] A tyTop)
    -> Computable (isType [] A)

  compTyClosedSigma : {A B C : RawType}
    -> Derivable (isType [] A)
    -> A =>t tySigma B C
    -> Derivable (typeEq [] A (tySigma B C))
    -> Computable (isType [] B)
    -> Derivable (isType (B ∷ []) C)
    -> Computable (isType [] A)

  compTyClosedEq : {A B : RawType} {a b : RawTerm}
    -> Derivable (isType [] A)
    -> A =>t tyEq B a b
    -> Derivable (typeEq [] A (tyEq B a b))
    -> Computable (isType [] B)
    -> Computable (hasTy [] a B)
    -> Computable (hasTy [] b B)
    -> Computable (isType [] A)

  compTyClosedQtr : {A B : RawType}
    -> Derivable (isType [] A)
    -> A =>t tyQtr B
    -> Derivable (typeEq [] A (tyQtr B))
    -> Computable (isType [] B)
    -> Computable (isType [] A)

  compTyEqClosedTop : {A B : RawType}
    -> Derivable (typeEq [] A B)
    -> Computable (isType [] A)
    -> Computable (isType [] B)
    -> A =>t tyTop
    -> B =>t tyTop
    -> Computable (typeEq [] A B)

  compTyEqClosedSigma : {A B C D E F : RawType}
    -> Derivable (typeEq [] A B)
    -> Computable (isType [] A)
    -> Computable (isType [] B)
    -> A =>t tySigma C D
    -> B =>t tySigma E F
    -> Computable (typeEq [] C E)
    -> Derivable (typeEq (C ∷ []) D F)
    -> Computable (typeEq [] A B)

  compTyEqClosedEq : {A B C D : RawType} {a b c d : RawTerm}
    -> Derivable (typeEq [] A B)
    -> Computable (isType [] A)
    -> Computable (isType [] B)
    -> A =>t tyEq C a b
    -> B =>t tyEq D c d
    -> Computable (typeEq [] C D)
    -> Computable (termEq [] a c C)
    -> Computable (termEq [] b d C)
    -> Computable (typeEq [] A B)

  compTyEqClosedQtr : {A B C D : RawType}
    -> Derivable (typeEq [] A B)
    -> Computable (isType [] A)
    -> Computable (isType [] B)
    -> A =>t tyQtr C
    -> B =>t tyQtr D
    -> Computable (typeEq [] C D)
    -> Computable (typeEq [] A B)

  compTmClosedTop : {a : RawTerm} {A : RawType}
    -> Derivable (hasTy [] a A)
    -> Computable (isType [] A)
    -> A =>t tyTop
    -> a =>e tmStar
    -> Derivable (termEq [] a tmStar A)
    -> Computable (hasTy [] a A)

  compTmClosedSigma : {t a b : RawTerm} {A B G : RawType}
    -> Derivable (hasTy [] t G)
    -> Computable (isType [] G)
    -> G =>t tySigma A B
    -> t =>e tmPair a b
    -> Derivable (termEq [] t (tmPair a b) G)
    -> Computable (hasTy [] a A)
    -> Computable (hasTy [] b (subTy (singleSubst a) B))
    -> Computable (hasTy [] t G)

  compTmClosedEq : {t a b : RawTerm} {A G : RawType}
    -> Derivable (hasTy [] t G)
    -> Computable (isType [] G)
    -> G =>t tyEq A a b
    -> t =>e tmR
    -> Derivable (termEq [] t tmR G)
    -> Computable (termEq [] a b A)
    -> Computable (hasTy [] t G)

  compTmClosedQtr : {t a : RawTerm} {A G : RawType}
    -> Derivable (hasTy [] t G)
    -> Computable (isType [] G)
    -> G =>t tyQtr A
    -> t =>e tmClass a
    -> Derivable (termEq [] t (tmClass a) G)
    -> Computable (hasTy [] a A)
    -> Computable (hasTy [] t G)

  compTmEqClosedTop : {a b : RawTerm} {A : RawType}
    -> Derivable (termEq [] a b A)
    -> Computable (hasTy [] a A)
    -> Computable (hasTy [] b A)
    -> A =>t tyTop
    -> a =>e tmStar
    -> b =>e tmStar
    -> Computable (termEq [] a b A)

  compTmEqClosedSigma : {t u a b c d : RawTerm} {A B G : RawType}
    -> Derivable (termEq [] t u G)
    -> Computable (hasTy [] t G)
    -> Computable (hasTy [] u G)
    -> G =>t tySigma A B
    -> t =>e tmPair a b
    -> u =>e tmPair c d
    -> Computable (termEq [] a c A)
    -> Computable (termEq [] b d (subTy (singleSubst a) B))
    -> Computable (termEq [] t u G)

  compTmEqClosedEq : {t u a b : RawTerm} {A G : RawType}
    -> Derivable (termEq [] t u G)
    -> Computable (hasTy [] t G)
    -> Computable (hasTy [] u G)
    -> G =>t tyEq A a b
    -> t =>e tmR
    -> u =>e tmR
    -> Computable (termEq [] a b A)
    -> Computable (termEq [] t u G)

  compTmEqClosedQtr : {t u a b : RawTerm} {A G : RawType}
    -> Derivable (termEq [] t u G)
    -> Computable (hasTy [] t G)
    -> Computable (hasTy [] u G)
    -> G =>t tyQtr A
    -> t =>e tmClass a
    -> u =>e tmClass b
    -> Computable (hasTy [] a A)
    -> Computable (hasTy [] b A)
    -> Computable (termEq [] t u G)

data ComputableFits : {gamma : Ctx} {sigma : Subst}
  -> FitsSubst [] gamma sigma -> Type where
  compFitsNil : {sigma : Subst} {wf : CtxWF []}
    -> ComputableFits (fitsNil {gamma = []} {delta = []} {sigma = sigma} wf)
  compFitsCons : {gamma : Ctx} {sigma : Subst} {A : RawType} {t : RawTerm}
      {fits : FitsSubst [] gamma sigma}
      {dt : Derivable (hasTy [] t (subTy sigma A))}
    -> ComputableFits fits
    -> Computable (hasTy [] t (subTy sigma A))
    -> ComputableFits (fitsCons fits dt)

data ComputableFitsEq : {gamma : Ctx} {sigma tau : Subst}
  -> FitsEqSubst [] gamma sigma tau -> Type where
  compFitsEqNil : {sigma tau : Subst} {wf : CtxWF []}
    -> ComputableFitsEq (fitsEqNil {gamma = []} {delta = []} {sigma = sigma} {tau = tau} wf)
  compFitsEqCons : {gamma : Ctx} {sigma tau : Subst} {A : RawType} {t u : RawTerm}
      {fitsEq : FitsEqSubst [] gamma sigma tau}
      {dtu : Derivable (termEq [] t u (subTy sigma A))}
    -> ComputableFitsEq fitsEq
    -> Computable (termEq [] t u (subTy sigma A))
    -> ComputableFitsEq (fitsEqCons fitsEq dtu)

data HypComputable : JForm -> Type where
  hypTyOpen : {gamma : Ctx} {A : RawType}
    -> ((gamma ≡ []) -> ⊥)
    -> Derivable (isType gamma A)
    -> ((sigma : Subst) (fits : FitsSubst [] gamma sigma)
         -> ComputableFits fits
         -> Computable (closedSubJ sigma (isType gamma A)))
    -> ((sigma tau : Subst) (fitsEq : FitsEqSubst [] gamma sigma tau)
         -> ComputableFitsEq fitsEq
         -> Computable (closedEqSubJ sigma tau (isType gamma A)))
    -> HypComputable (isType gamma A)

  hypTyEqOpen : {gamma : Ctx} {A B : RawType}
    -> ((gamma ≡ []) -> ⊥)
    -> Derivable (typeEq gamma A B)
    -> HypComputable (isType gamma A)
    -> ((sigma : Subst) (fits : FitsSubst [] gamma sigma)
         -> ComputableFits fits
         -> Computable (closedSubJ sigma (typeEq gamma A B)))
    -> ((sigma tau : Subst) (fitsEq : FitsEqSubst [] gamma sigma tau)
         -> ComputableFitsEq fitsEq
         -> Computable (closedEqSubJ sigma tau (typeEq gamma A B)))
    -> HypComputable (typeEq gamma A B)

  hypTmOpen : {gamma : Ctx} {t : RawTerm} {A : RawType}
    -> ((gamma ≡ []) -> ⊥)
    -> Derivable (hasTy gamma t A)
    -> HypComputable (isType gamma A)
    -> ((sigma : Subst) (fits : FitsSubst [] gamma sigma)
         -> ComputableFits fits
         -> Computable (closedSubJ sigma (hasTy gamma t A)))
    -> ((sigma tau : Subst) (fitsEq : FitsEqSubst [] gamma sigma tau)
         -> ComputableFitsEq fitsEq
         -> Computable (closedEqSubJ sigma tau (hasTy gamma t A)))
    -> HypComputable (hasTy gamma t A)

  hypTmEqOpen : {gamma : Ctx} {t u : RawTerm} {A : RawType}
    -> ((gamma ≡ []) -> ⊥)
    -> Derivable (termEq gamma t u A)
    -> HypComputable (hasTy gamma t A)
    -> ((sigma : Subst) (fits : FitsSubst [] gamma sigma)
         -> ComputableFits fits
         -> Computable (closedSubJ sigma (termEq gamma t u A)))
    -> ((sigma tau : Subst) (fitsEq : FitsEqSubst [] gamma sigma tau)
         -> ComputableFitsEq fitsEq
         -> Computable (closedEqSubJ sigma tau (termEq gamma t u A)))
    -> HypComputable (termEq gamma t u A)
