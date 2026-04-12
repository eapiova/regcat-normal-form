{-# OPTIONS --safe #-}

module TReg.Computability where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Empty.Base using (⊥)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Sigma using (Σ-syntax)
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

-- Computable: closures take raw FitsSubst only (no ComputableFits).
-- This avoids strict positivity issues. ComputableFits is defined post-mutual
-- and the conversion fitsToCompFits is also post-mutual.

data Computable (n : ℕ) : JForm -> Type where
  compTyClosedTop : {A : RawType}
    -> Derivable (isType [] A)
    -> A =>t tyTop
    -> Derivable (typeEq [] A tyTop)
    -> Computable n (isType [] A)

  compTyClosedSigma : {A B C : RawType}
    -> Derivable (isType [] A)
    -> A =>t tySigma B C
    -> Derivable (typeEq [] A (tySigma B C))
    -> Computable n (isType [] B)
    -> Derivable (isType (B ∷ []) C)
    -> Computable n (isType [] A)

  compTyClosedEq : {A B : RawType} {a b : RawTerm}
    -> Derivable (isType [] A)
    -> A =>t tyEq B a b
    -> Derivable (typeEq [] A (tyEq B a b))
    -> Computable n (isType [] B)
    -> Computable n (hasTy [] a B)
    -> Computable n (hasTy [] b B)
    -> Computable n (isType [] A)

  compTyClosedQtr : {A B : RawType}
    -> Derivable (isType [] A)
    -> A =>t tyQtr B
    -> Derivable (typeEq [] A (tyQtr B))
    -> Computable n (isType [] B)
    -> Computable n (isType [] A)

  compTyEqClosedTop : {A B : RawType}
    -> Derivable (typeEq [] A B)
    -> Computable n (isType [] A)
    -> Computable n (isType [] B)
    -> A =>t tyTop
    -> B =>t tyTop
    -> Computable n (typeEq [] A B)

  compTyEqClosedSigma : {A B C D E F : RawType}
    -> Derivable (typeEq [] A B)
    -> Computable n (isType [] A)
    -> Computable n (isType [] B)
    -> A =>t tySigma C D
    -> B =>t tySigma E F
    -> Computable n (typeEq [] C E)
    -> Derivable (typeEq (C ∷ []) D F)
    -> Computable n (typeEq [] A B)

  compTyEqClosedEq : {A B C D : RawType} {a b c d : RawTerm}
    -> Derivable (typeEq [] A B)
    -> Computable n (isType [] A)
    -> Computable n (isType [] B)
    -> A =>t tyEq C a b
    -> B =>t tyEq D c d
    -> Computable n (typeEq [] C D)
    -> Computable n (termEq [] a c C)
    -> Computable n (termEq [] b d C)
    -> Computable n (typeEq [] A B)

  compTyEqClosedQtr : {A B C D : RawType}
    -> Derivable (typeEq [] A B)
    -> Computable n (isType [] A)
    -> Computable n (isType [] B)
    -> A =>t tyQtr C
    -> B =>t tyQtr D
    -> Computable n (typeEq [] C D)
    -> Computable n (typeEq [] A B)

  compTmClosedTop : {a : RawTerm} {A : RawType}
    -> Derivable (hasTy [] a A)
    -> Computable n (isType [] A)
    -> A =>t tyTop
    -> a =>e tmStar
    -> Derivable (termEq [] a tmStar A)
    -> Computable n (hasTy [] a A)

  compTmClosedSigma : {t a b : RawTerm} {A B G : RawType}
    -> Derivable (hasTy [] t G)
    -> Computable n (isType [] G)
    -> G =>t tySigma A B
    -> t =>e tmPair a b
    -> Derivable (termEq [] t (tmPair a b) G)
    -> Computable n (hasTy [] a A)
    -> Computable n (hasTy [] b (subTy (singleSubst a) B))
    -> Computable n (hasTy [] t G)

  compTmClosedEq : {t a b : RawTerm} {A G : RawType}
    -> Derivable (hasTy [] t G)
    -> Computable n (isType [] G)
    -> G =>t tyEq A a b
    -> t =>e tmR
    -> Derivable (termEq [] t tmR G)
    -> Computable n (termEq [] a b A)
    -> Computable n (hasTy [] t G)

  compTmClosedQtr : {t a : RawTerm} {A G : RawType}
    -> Derivable (hasTy [] t G)
    -> Computable n (isType [] G)
    -> G =>t tyQtr A
    -> t =>e tmClass a
    -> Derivable (termEq [] t (tmClass a) G)
    -> Computable n (hasTy [] a A)
    -> Computable n (hasTy [] t G)

  compTmEqClosedTop : {a b : RawTerm} {A : RawType}
    -> Derivable (termEq [] a b A)
    -> Computable n (hasTy [] a A)
    -> Computable n (hasTy [] b A)
    -> A =>t tyTop
    -> a =>e tmStar
    -> b =>e tmStar
    -> Computable n (termEq [] a b A)

  compTmEqClosedSigma : {t u a b c d : RawTerm} {A B G : RawType}
    -> Derivable (termEq [] t u G)
    -> Computable n (hasTy [] t G)
    -> Computable n (hasTy [] u G)
    -> G =>t tySigma A B
    -> t =>e tmPair a b
    -> u =>e tmPair c d
    -> Computable n (termEq [] a c A)
    -> Computable n (termEq [] b d (subTy (singleSubst a) B))
    -> Computable n (termEq [] t u G)

  compTmEqClosedEq : {t u a b : RawTerm} {A G : RawType}
    -> Derivable (termEq [] t u G)
    -> Computable n (hasTy [] t G)
    -> Computable n (hasTy [] u G)
    -> G =>t tyEq A a b
    -> t =>e tmR
    -> u =>e tmR
    -> Computable n (termEq [] a b A)
    -> Computable n (termEq [] t u G)

  compTmEqClosedQtr : {t u a b : RawTerm} {A G : RawType}
    -> Derivable (termEq [] t u G)
    -> Computable n (hasTy [] t G)
    -> Computable n (hasTy [] u G)
    -> G =>t tyQtr A
    -> t =>e tmClass a
    -> u =>e tmClass b
    -> Computable n (hasTy [] a A)
    -> Computable n (hasTy [] b A)
    -> Computable n (termEq [] t u G)

-- ComputableFits / ComputableFitsEq: defined OUTSIDE the data block.
-- Contains Computable n — strictly positive (no function types).

data ComputableFits (n : ℕ) : {gamma : Ctx} {sigma : Subst}
  -> FitsSubst [] gamma sigma -> Type where
  compFitsNil : {sigma : Subst} {delta : Ctx} {wf : CtxWF []}
    -> ComputableFits n (fitsNil {gamma = []} {delta = delta} {sigma = sigma} wf)
  compFitsCons : {gamma : Ctx} {sigma : Subst} {A : RawType} {t : RawTerm}
      {fits : FitsSubst [] gamma sigma}
      {dt : Derivable (hasTy [] t (subTy sigma A))}
    -> ComputableFits n fits
    -> Computable n (hasTy [] t (subTy sigma A))
    -> ComputableFits n (fitsCons fits dt)

data ComputableFitsEq (n : ℕ) : {gamma : Ctx} {sigma tau : Subst}
  -> FitsEqSubst [] gamma sigma tau -> Type where
  compFitsEqNil : {sigma tau : Subst} {delta : Ctx} {wf : CtxWF []}
    -> ComputableFitsEq n (fitsEqNil {gamma = []} {delta = delta} {sigma = sigma} {tau = tau} wf)
  compFitsEqCons : {gamma : Ctx} {sigma tau : Subst} {A : RawType} {t u : RawTerm}
      {fitsEq : FitsEqSubst [] gamma sigma tau}
      {dtu : Derivable (termEq [] t u (subTy sigma A))}
    -> ComputableFitsEq n fitsEq
    -> Computable n (termEq [] t u (subTy sigma A))
    -> ComputableFitsEq n (fitsEqCons fitsEq dtu)

-- HypComputable: level-split design.
-- Closures take ComputableFits n (level n), produce Computable (suc n).
-- HypComputable only exists at level (suc n).
-- This breaks the termination cycle: composeCompFits at level n
-- cannot cycle back through closures that produce level (suc n).
-- Defined OUTSIDE the Computable data, so no positivity issue.
data HypComputable : ℕ -> JForm -> Type where
  hypTyOpen : {n : ℕ} {gamma : Ctx} {A : RawType}
    -> ((gamma ≡ []) -> ⊥)
    -> Derivable (isType gamma A)
    -> ((sigma : Subst) (fits : FitsSubst [] gamma sigma)
         -> ComputableFits n fits
         -> Computable n (closedSubJ sigma (isType gamma A)))
    -> ((sigma tau : Subst) (fitsEq : FitsEqSubst [] gamma sigma tau)
         -> ComputableFitsEq n fitsEq
         -> Computable n (closedEqSubJ sigma tau (isType gamma A)))
    -> HypComputable (suc n) (isType gamma A)

  hypTyEqOpen : {n : ℕ} {gamma : Ctx} {A B : RawType}
    -> ((gamma ≡ []) -> ⊥)
    -> Derivable (typeEq gamma A B)
    -> HypComputable (suc n) (isType gamma A)
    -> ((sigma : Subst) (fits : FitsSubst [] gamma sigma)
         -> ComputableFits n fits
         -> Computable n (closedSubJ sigma (typeEq gamma A B)))
    -> ((sigma tau : Subst) (fitsEq : FitsEqSubst [] gamma sigma tau)
         -> ComputableFitsEq n fitsEq
         -> Computable n (closedEqSubJ sigma tau (typeEq gamma A B)))
    -> HypComputable (suc n) (typeEq gamma A B)

  hypTmOpen : {n : ℕ} {gamma : Ctx} {t : RawTerm} {A : RawType}
    -> ((gamma ≡ []) -> ⊥)
    -> Derivable (hasTy gamma t A)
    -> HypComputable (suc n) (isType gamma A)
    -> ((sigma : Subst) (fits : FitsSubst [] gamma sigma)
         -> ComputableFits n fits
         -> Computable n (closedSubJ sigma (hasTy gamma t A)))
    -> ((sigma tau : Subst) (fitsEq : FitsEqSubst [] gamma sigma tau)
         -> ComputableFitsEq n fitsEq
         -> Computable n (closedEqSubJ sigma tau (hasTy gamma t A)))
    -> HypComputable (suc n) (hasTy gamma t A)

  hypTmEqOpen : {n : ℕ} {gamma : Ctx} {t u : RawTerm} {A : RawType}
    -> ((gamma ≡ []) -> ⊥)
    -> Derivable (termEq gamma t u A)
    -> HypComputable (suc n) (hasTy gamma t A)
    -> ((sigma : Subst) (fits : FitsSubst [] gamma sigma)
         -> ComputableFits n fits
         -> Computable n (closedSubJ sigma (termEq gamma t u A)))
    -> ((sigma tau : Subst) (fitsEq : FitsEqSubst [] gamma sigma tau)
         -> ComputableFitsEq n fitsEq
         -> Computable n (closedEqSubJ sigma tau (termEq gamma t u A)))
    -> HypComputable (suc n) (termEq gamma t u A)

-- Level lifting: Computable n → Computable (suc n).
-- n is a phantom parameter (never pattern-matched), so this is structural
-- on the Computable argument. Used at HypComputable closure boundaries
-- where SCC 2 returns Computable n but the closure needs Computable (suc n).
liftComputable : {n : ℕ} {J : JForm} → Computable n J → Computable (suc n) J
liftComputable (compTyClosedTop d ev eq) = compTyClosedTop d ev eq
liftComputable (compTyClosedSigma d ev eq compB dC) =
  compTyClosedSigma d ev eq (liftComputable compB) dC
liftComputable (compTyClosedEq d ev eq compB compa compb) =
  compTyClosedEq d ev eq (liftComputable compB) (liftComputable compa) (liftComputable compb)
liftComputable (compTyClosedQtr d ev eq compB) =
  compTyClosedQtr d ev eq (liftComputable compB)
liftComputable (compTyEqClosedTop d compA compB evA evB) =
  compTyEqClosedTop d (liftComputable compA) (liftComputable compB) evA evB
liftComputable (compTyEqClosedSigma d compA compB evA evB compCE dDF) =
  compTyEqClosedSigma d (liftComputable compA) (liftComputable compB) evA evB (liftComputable compCE) dDF
liftComputable (compTyEqClosedEq d compA compB evA evB compCD compac compbd) =
  compTyEqClosedEq d (liftComputable compA) (liftComputable compB) evA evB
    (liftComputable compCD) (liftComputable compac) (liftComputable compbd)
liftComputable (compTyEqClosedQtr d compA compB evA evB compCD) =
  compTyEqClosedQtr d (liftComputable compA) (liftComputable compB) evA evB (liftComputable compCD)
liftComputable (compTmClosedTop d compA ev evT eq) =
  compTmClosedTop d (liftComputable compA) ev evT eq
liftComputable (compTmClosedSigma d compG ev evP eq compa compb) =
  compTmClosedSigma d (liftComputable compG) ev evP eq (liftComputable compa) (liftComputable compb)
liftComputable (compTmClosedEq d compG ev evR eq compab) =
  compTmClosedEq d (liftComputable compG) ev evR eq (liftComputable compab)
liftComputable (compTmClosedQtr d compG ev evC eq compa) =
  compTmClosedQtr d (liftComputable compG) ev evC eq (liftComputable compa)
liftComputable (compTmEqClosedTop d compa compb evA eva evb) =
  compTmEqClosedTop d (liftComputable compa) (liftComputable compb) evA eva evb
liftComputable (compTmEqClosedSigma d compt compu ev evt evu compac compbd) =
  compTmEqClosedSigma d (liftComputable compt) (liftComputable compu) ev evt evu
    (liftComputable compac) (liftComputable compbd)
liftComputable (compTmEqClosedEq d compt compu ev evt evu compab) =
  compTmEqClosedEq d (liftComputable compt) (liftComputable compu) ev evt evu (liftComputable compab)
liftComputable (compTmEqClosedQtr d compt compu ev evt evu compa compb) =
  compTmEqClosedQtr d (liftComputable compt) (liftComputable compu) ev evt evu
    (liftComputable compa) (liftComputable compb)

liftComputableFits : {n : ℕ} {gamma : Ctx} {sigma : Subst}
  {fits : FitsSubst [] gamma sigma}
  → ComputableFits n fits → ComputableFits (suc n) fits
liftComputableFits compFitsNil = compFitsNil
liftComputableFits (compFitsCons cf comp) =
  compFitsCons (liftComputableFits cf) (liftComputable comp)

liftComputableFitsEq : {n : ℕ} {gamma : Ctx} {sigma tau : Subst}
  {fitsEq : FitsEqSubst [] gamma sigma tau}
  → ComputableFitsEq n fitsEq → ComputableFitsEq (suc n) fitsEq
liftComputableFitsEq compFitsEqNil = compFitsEqNil
liftComputableFitsEq (compFitsEqCons cf comp) =
  compFitsEqCons (liftComputableFitsEq cf) (liftComputable comp)

-- Bundle types
CompFitsBundle : ℕ -> Ctx -> Subst -> Type
CompFitsBundle n gamma sigma =
  Σ[ fits ∈ FitsSubst [] gamma sigma ] ComputableFits n fits

CompFitsEqBundle : ℕ -> Ctx -> Subst -> Subst -> Type
CompFitsEqBundle n gamma sigma tau =
  Σ[ fitsEq ∈ FitsEqSubst [] gamma sigma tau ] ComputableFitsEq n fitsEq
