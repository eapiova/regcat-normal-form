{-# OPTIONS --safe #-}

module TReg.Syntax where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc)

mutual
  data RawType : Type where
    tyTop : RawType
    tySigma : RawType -> RawType -> RawType
    tyEq : RawType -> RawTerm -> RawTerm -> RawType
    tyQtr : RawType -> RawType

  data RawTerm : Type where
    var : ℕ -> RawTerm
    tmStar : RawTerm
    tmPair : RawTerm -> RawTerm -> RawTerm
    tmElSigma : RawTerm -> RawTerm -> RawTerm
    tmR : RawTerm
    tmEq : RawType -> RawTerm -> RawTerm
    tmClass : RawTerm -> RawTerm
    tmElQtr : RawTerm -> RawTerm -> RawTerm
