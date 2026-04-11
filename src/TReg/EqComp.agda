
{-# OPTIONS --safe #-}

module TReg.EqComp where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.List.Base using ([])

open import TReg.Syntax
open import TReg.Context
open import TReg.Evaluation
open import TReg.Derivability
open import TReg.Computability
open import TReg.Inversion
open import TReg.Presupposition
open import TReg.Structural

compFEqClosed : {n : ℕ} {A : RawType} {a b : RawTerm}
  -> Computable n (isType [] A)
  -> Computable n (hasTy [] a A)
  -> Computable n (hasTy [] b A)
  -> Computable n (isType [] (tyEq A a b))
compFEqClosed compA compa compb =
  compTyClosedEq
    (fEq (compToDerivable compA) (compToDerivable compa) (compToDerivable compb))
    evalEq
    (reflTy (fEq (compToDerivable compA) (compToDerivable compa) (compToDerivable compb)))
    compA
    compa
    compb

compIEqClosed : {n : ℕ} {A : RawType} {a : RawTerm}
  -> Computable n (hasTy [] a A)
  -> Computable n (hasTy [] tmR (tyEq A a a))
compIEqClosed compa =
  compTmClosedEq
    (iEq (compToDerivable compa))
    (compFEqClosed (compTmToCompTy compa) compa compa)
    evalEq
    evalR
    (reflTm (iEq (compToDerivable compa)))
    (compReflTmClosed compa)

compEEqClosed : {n : ℕ} {A : RawType} {a b p : RawTerm}
  -> Computable n (hasTy [] p (tyEq A a b))
  -> Computable n (termEq [] a b A)
compEEqClosed {A = A} {a = a} {b = b}
  (compTmClosedEq _ _ (evalEq {A = A} {a = a} {b = b}) _ _ compab) =
  compab

compCEqClosed : {n : ℕ} {A : RawType} {a b p : RawTerm}
  -> Computable n (hasTy [] p (tyEq A a b))
  -> Computable n (termEq [] p tmR (tyEq A a b))
compCEqClosed {A = A} {a = a} {b = b}
  compp@(compTmClosedEq dp compEqTy (evalEq {A = A} {a = a} {b = b}) evp _ compab) =
  compTmEqClosedEq
    (cEq dp dA da db)
    compp
    compEqRefl
    evalEq
    evp
    evalR
    compab
  where
  compa : Computable _ (hasTy [] a A)
  compa = compTmEqLeft compab

  dA : Derivable (isType [] A)
  dA = compToDerivable (compTmToCompTy compa)

  da : Derivable (hasTy [] a A)
  da = compToDerivable compa

  db : Derivable (hasTy [] b A)
  db = assocTmRight (compToDerivable compab)

  dEqTy : Derivable (typeEq [] (tyEq A a a) (tyEq A a b))
  dEqTy = fEqEq (reflTy dA) (reflTm da) (compToDerivable compab)

  dEqRefl : Derivable (hasTy [] tmR (tyEq A a b))
  dEqRefl = conv (iEq da) dEqTy

  compEqRefl : Computable _ (hasTy [] tmR (tyEq A a b))
  compEqRefl =
    compTmClosedEq
      dEqRefl
      compEqTy
      evalEq
      evalR
      (cEq dEqRefl dA da db)
      compab
