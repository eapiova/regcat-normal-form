
{-# OPTIONS --safe #-}

module TReg.TopComp where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.List.Base using ([])

open import TReg.Syntax
open import TReg.Context
open import TReg.Evaluation
open import TReg.Derivability
open import TReg.Computability

compFTopClosed : {n : ℕ} -> Computable n (isType [] tyTop)
compFTopClosed =
  compTyClosedTop
    (fTop wfNil)
    evalTop
    (reflTy (fTop wfNil))

compITopClosed : {n : ℕ} -> Computable n (hasTy [] tmStar tyTop)
compITopClosed =
  compTmClosedTop
    (iTop wfNil)
    compFTopClosed
    evalTop
    evalStar
    (reflTm (iTop wfNil))

compCTopClosed : {n : ℕ} {t : RawTerm}
  -> Computable n (hasTy [] t tyTop)
  -> Computable n (termEq [] t tmStar tyTop)
compCTopClosed comp@(compTmClosedTop d _ evA evt _) =
  compTmEqClosedTop
    (cTop d)
    comp
    compITopClosed
    evA
    evt
    evalStar
