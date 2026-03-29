
{-# OPTIONS --safe #-}

module TReg.TopComp where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Empty.Base as Empty using (rec)
open import Cubical.Data.List.Base using ([])

open import TReg.Syntax
open import TReg.Context
open import TReg.Evaluation
open import TReg.Derivability
open import TReg.Computability

compFTopClosed : Computable (isType [] tyTop)
compFTopClosed =
  compTyClosedTop
    (fTop wfNil)
    evalTop
    (reflTy (fTop wfNil))

compITopClosed : Computable (hasTy [] tmStar tyTop)
compITopClosed =
  compTmClosedTop
    (iTop wfNil)
    compFTopClosed
    evalTop
    evalStar
    (reflTm (iTop wfNil))

compCTopClosed : {t : RawTerm}
  -> Computable (hasTy [] t tyTop)
  -> Computable (termEq [] t tmStar tyTop)
compCTopClosed comp@(compTmClosedTop d _ evA evt _) =
  compTmEqClosedTop
    (cTop d)
    comp
    compITopClosed
    evA
    evt
    evalStar
compCTopClosed (compTmOpen neq _ _ _ _) = Empty.rec (neq refl)
