{-# OPTIONS --safe #-}

module Tait.Evaluation where

open import Tait.Prelude
open import Data.Empty as Empty using () renaming (⊥-elim to rec)
open import Data.Nat using (ℕ ; zero ; suc ; _+_)
open import Data.Nat.Base using (_<_) renaming (s≤s to suc-≤-suc)
open import Data.Nat.Properties using ()
  renaming (m≤m+n to ≤SumLeft ; m≤n+m to ≤SumRight)
open import Data.Nat.Induction using () renaming (<-wellFounded to <-wellfounded)
open import Induction.WellFounded using (Acc ; acc)

open import Tait.Syntax
open import Tait.Substitution

infix 40 _=>t_ _=>e_

data _=>t_ : RawType -> RawType -> Type where
  evalTop : tyTop =>t tyTop
  evalSigma : {A B : RawType} -> tySigma A B =>t tySigma A B

sigmaCompSub : RawTerm -> RawTerm -> Subst
sigmaCompSub a b = consSubst b (consSubst a idSubst)

data _=>e_ : RawTerm -> RawTerm -> Type where
  evalStar : tmStar =>e tmStar
  evalPair : {a b : RawTerm} -> tmPair a b =>e tmPair a b
  evalElSigma : {d m b c g : RawTerm}
    -> d =>e tmPair b c
    -> subTm (sigmaCompSub b c) m =>e g
    -> tmElSigma d m =>e g

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

-- Size measure for evaluation proofs
evalSize : {t g : RawTerm} -> t =>e g -> ℕ
evalSize evalStar = 0
evalSize evalPair = 0
evalSize (evalElSigma evd evm) = suc (evalSize evd + evalSize evm)

private
  evalDetTmAcc : {t g g' : RawTerm}
    -> (ev₁ : t =>e g) -> Acc _<_ (evalSize ev₁) -> (ev₂ : t =>e g') -> g ≡ g'
  evalDetTmAcc evalStar _ evalStar = refl
  evalDetTmAcc evalPair _ evalPair = refl
  evalDetTmAcc
    {g = g} {g' = g'}
    (evalElSigma {m = m} {b = b} {c = c} evd₁ evm₁) (acc step)
    (evalElSigma {b = b'} {c = c'} evd₂ evm₂) =
    let
      acD : Acc _<_ (evalSize evd₁)
      acD = step (suc-≤-suc (≤SumLeft (evalSize evd₁) (evalSize evm₁)))
      pairEq = evalDetTmAcc evd₁ acD evd₂
      bEq = tmPairInj₁ pairEq
      cEq = tmPairInj₂ pairEq
      srcEq = cong₂ (λ x y -> subTm (sigmaCompSub x y) m) bEq cEq
      acM : Acc _<_ (evalSize evm₁)
      acM = step (suc-≤-suc (≤SumRight (evalSize evm₁) (evalSize evd₁)))
    in
    evalDetTmAcc evm₁ acM (subst (λ x -> x =>e g') (sym srcEq) evm₂)

evalDetTm : {t g g' : RawTerm} -> t =>e g -> t =>e g' -> g ≡ g'
evalDetTm ev₁ ev₂ = evalDetTmAcc ev₁ (<-wellfounded (evalSize ev₁)) ev₂
