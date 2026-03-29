{-# OPTIONS --safe #-}

module TReg.Evaluation where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Empty.Base as Empty using (rec)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_)
open import Cubical.Data.Nat.Order using (_<_ ; suc-≤-suc ; ≤SumLeft ; ≤SumRight ; <-wellfounded)
open import Cubical.Induction.WellFounded using (Acc ; acc)

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

tmPairFst : RawTerm -> RawTerm
tmPairFst (tmPair a _) = a
tmPairFst _ = tmStar

tmPairSnd : RawTerm -> RawTerm
tmPairSnd (tmPair _ b) = b
tmPairSnd _ = tmStar

tmPairInj₁ : {a b c d : RawTerm} -> tmPair a b ≡ tmPair c d -> a ≡ c
tmPairInj₁ p = cong tmPairFst p

tmPairInj₂ : {a b c d : RawTerm} -> tmPair a b ≡ tmPair c d -> b ≡ d
tmPairInj₂ p = cong tmPairSnd p

tmClassRepr : RawTerm -> RawTerm
tmClassRepr (tmClass a) = a
tmClassRepr _ = tmStar

tmClassInj : {a b : RawTerm} -> tmClass a ≡ tmClass b -> a ≡ b
tmClassInj p = cong tmClassRepr p

-- Size measure for evaluation proofs
evalSize : {t g : RawTerm} -> t =>e g -> ℕ
evalSize evalStar = 0
evalSize evalPair = 0
evalSize evalR = 0
evalSize evalEqTm = 0
evalSize evalClass = 0
evalSize (evalElSigma evd evm) = suc (evalSize evd + evalSize evm)
evalSize (evalElQtr evp evl) = suc (evalSize evp + evalSize evl)

private
  evalDetTmAcc : {t g g' : RawTerm}
    -> (ev₁ : t =>e g) -> Acc _<_ (evalSize ev₁) -> (ev₂ : t =>e g') -> g ≡ g'
  evalDetTmAcc evalStar _ evalStar = refl
  evalDetTmAcc evalPair _ evalPair = refl
  evalDetTmAcc evalR _ evalR = refl
  evalDetTmAcc evalEqTm _ evalEqTm = refl
  evalDetTmAcc evalClass _ evalClass = refl
  evalDetTmAcc
    {g = g} {g' = g'}
    (evalElSigma {m = m} {b = b} {c = c} evd₁ evm₁) (acc step)
    (evalElSigma {b = b'} {c = c'} evd₂ evm₂) =
    let
      acD : Acc _<_ (evalSize evd₁)
      acD = step (evalSize evd₁) (suc-≤-suc (≤SumLeft {evalSize evd₁} {evalSize evm₁}))
      pairEq = evalDetTmAcc evd₁ acD evd₂
      bEq = tmPairInj₁ pairEq
      cEq = tmPairInj₂ pairEq
      srcEq = cong₂ (λ x y -> subTm (sigmaCompSub x y) m) bEq cEq
      acM : Acc _<_ (evalSize evm₁)
      acM = step (evalSize evm₁) (suc-≤-suc (≤SumRight {evalSize evm₁} {evalSize evd₁}))
    in
    evalDetTmAcc evm₁ acM (subst (λ x -> x =>e g') (sym srcEq) evm₂)
  evalDetTmAcc
    {g = g} {g' = g'}
    (evalElQtr {l = l} {a = a} evp₁ evl₁) (acc step)
    (evalElQtr {a = a'} evp₂ evl₂) =
    let
      acP : Acc _<_ (evalSize evp₁)
      acP = step (evalSize evp₁) (suc-≤-suc (≤SumLeft {evalSize evp₁} {evalSize evl₁}))
      classEq = evalDetTmAcc evp₁ acP evp₂
      aEq = tmClassInj classEq
      srcEq = cong (λ x -> subTm (qtrCompSub x) l) aEq
      acL : Acc _<_ (evalSize evl₁)
      acL = step (evalSize evl₁) (suc-≤-suc (≤SumRight {evalSize evl₁} {evalSize evp₁}))
    in
    evalDetTmAcc evl₁ acL (subst (λ x -> x =>e g') (sym srcEq) evl₂)

evalDetTm : {t g g' : RawTerm} -> t =>e g -> t =>e g' -> g ≡ g'
evalDetTm ev₁ ev₂ = evalDetTmAcc ev₁ (<-wellfounded (evalSize ev₁)) ev₂
