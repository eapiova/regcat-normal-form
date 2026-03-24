{-# OPTIONS --cubical --guardedness #-}

module TReg.Evaluation where

open import Cubical.Foundations.Prelude

open import TReg.Syntax
open import TReg.Substitution

infix 40 _=>t_ _=>e_

data _=>t_ : RawType -> RawType -> Type where
  evalTop : tyTop =>t tyTop
  evalSigma : {A B : RawType} -> tySigma A B =>t tySigma A B
  evalEq : {A : RawType} {a b : RawTerm} -> tyEq A a b =>t tyEq A a b
  evalQtr : {A : RawType} -> tyQtr A =>t tyQtr A

sigmaCompSub : RawTerm -> RawTerm -> Subst
sigmaCompSub a b = consSubst b (consSubst a idSubst)

qtrCompSub : RawTerm -> Subst
qtrCompSub a = consSubst a idSubst

data _=>e_ : RawTerm -> RawTerm -> Type where
  evalStar : tmStar =>e tmStar
  evalPair : {a b : RawTerm} -> tmPair a b =>e tmPair a b
  evalR : tmR =>e tmR
  evalEqTm : {A : RawType} {a : RawTerm} -> tmEq A a =>e tmEq A a
  evalClass : {a : RawTerm} -> tmClass a =>e tmClass a
  evalElSigma : {d m b c g : RawTerm}
    -> d =>e tmPair b c
    -> subTm (sigmaCompSub b c) m =>e g
    -> tmElSigma d m =>e g
  evalElQtr : {l p a g : RawTerm}
    -> p =>e tmClass a
    -> subTm (qtrCompSub a) l =>e g
    -> tmElQtr l p =>e g
