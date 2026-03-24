{-# OPTIONS --cubical --guardedness #-}

module TReg.Context where

open import Cubical.Foundations.Prelude
open import Cubical.Data.List.Base using (List ; [] ; _∷_ ; _++_ ; length)

open import TReg.Syntax

Ctx : Type
Ctx = List RawType

data JForm : Type where
  isType : Ctx -> RawType -> JForm
  typeEq : Ctx -> RawType -> RawType -> JForm
  hasTy : Ctx -> RawTerm -> RawType -> JForm
  termEq : Ctx -> RawTerm -> RawTerm -> RawType -> JForm

ctxOf : JForm -> Ctx
ctxOf (isType gamma _) = gamma
ctxOf (typeEq gamma _ _) = gamma
ctxOf (hasTy gamma _ _) = gamma
ctxOf (termEq gamma _ _ _) = gamma

data CtxWFBy (IsType : Ctx -> RawType -> Type) : Ctx -> Type where
  wfNil : CtxWFBy IsType []
  wfCons : {gamma : Ctx} {A : RawType}
    -> CtxWFBy IsType gamma
    -> IsType gamma A
    -> CtxWFBy IsType (A ∷ gamma)
