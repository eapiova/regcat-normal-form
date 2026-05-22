{-# OPTIONS --safe #-}

module Tait.CompLemmas where

open import Tait.Prelude
open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ ; zero ; suc ; _<_)
open import Data.Nat.Induction using () renaming (<-wellFounded to <-wf)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit using (tt)
open import Induction.WellFounded using (Acc ; acc)

open import Tait.Syntax
open import Tait.Substitution
open import Tait.Measure
open import Tait.Evaluation
open import Tait.Computable

evalResultValue : {t g : RawTerm} -> t =>e g -> g =>e g
evalResultValue evalStar = evalStar
evalResultValue evalPair = evalPair
evalResultValue evalR = evalR
evalResultValue evalEqTm = evalEqTm
evalResultValue evalClass = evalClass
evalResultValue (evalElSigma evd evm) = evalResultValue evm
evalResultValue (evalElQtr evp evl) = evalResultValue evl

eval-=>e-back : {t g h : RawTerm} -> t =>e g -> g =>e h -> t =>e h
eval-=>e-back {t} ev evgh =
  subst (λ x -> t =>e x) (evalDetTm (evalResultValue ev) evgh) ev

eval-=>e-fwd : {t g h : RawTerm} -> t =>e g -> t =>e h -> g =>e h
eval-=>e-fwd {g = g} ev evth =
  subst (λ x -> g =>e x) (evalDetTm ev evth) (evalResultValue ev)

compTm-=>e-back : {A : RawType} {t g : RawTerm}
  -> t =>e g -> Computable A g -> Computable A t
compTm-=>e-back {A = tyTop} ev cg = eval-=>e-back ev cg
compTm-=>e-back {A = tySigma A B} ev cg =
  let a , b , evg , ca , cb = computableSigma-elim cg in
  computableSigma-intro (a , b , eval-=>e-back ev evg , ca , cb)
compTm-=>e-back {A = tyEq A a b} ev cg =
  let evg , cab = computableEq-elim cg in
  computableEq-intro (eval-=>e-back ev evg , cab)
compTm-=>e-back {A = tyQtr A} ev cg =
  let a , evg , ca = computableQtr-elim cg in
  computableQtr-intro (a , eval-=>e-back ev evg , ca)

compTm-=>e-fwd : {A : RawType} {t g : RawTerm}
  -> t =>e g -> Computable A t -> Computable A g
compTm-=>e-fwd {A = tyTop} ev ct = eval-=>e-fwd ev ct
compTm-=>e-fwd {A = tySigma A B} ev ct =
  let a , b , evt , ca , cb = computableSigma-elim ct in
  computableSigma-intro (a , b , eval-=>e-fwd ev evt , ca , cb)
compTm-=>e-fwd {A = tyEq A a b} ev ct =
  let evt , cab = computableEq-elim ct in
  computableEq-intro (eval-=>e-fwd ev evt , cab)
compTm-=>e-fwd {A = tyQtr A} ev ct =
  let a , evt , ca = computableQtr-elim ct in
  computableQtr-intro (a , eval-=>e-fwd ev evt , ca)

singleSubst-apply-cong : {a b : RawTerm}
  -> a ≡ b -> (n : ℕ)
  -> applySubst (singleSubst a) n ≡ applySubst (singleSubst b) n
singleSubst-apply-cong p zero = p
singleSubst-apply-cong p (suc n) = refl

tmAcc-ty-subst : (A B : RawType)
    (pA : Acc _<_ (tyDepth A)) (pB : Acc _<_ (tyDepth B)) (t : RawTerm)
  -> A ≡ B -> ComputableTmAcc A pA t -> ComputableTmAcc B pB t
tmAcc-ty-subst A .A pA pB t refl c =
  ComputableTmAcc-cast A pA pB t c

tmEqAcc-ty-subst : (A B : RawType)
    (pA : Acc _<_ (tyDepth A)) (pB : Acc _<_ (tyDepth B))
    (t u : RawTerm)
  -> A ≡ B -> ComputableTmEqAcc A pA t u -> ComputableTmEqAcc B pB t u
tmEqAcc-ty-subst A .A pA pB t u refl c =
  ComputableTmEqAcc-cast A pA pB t u c

tyEqAcc-ty-subst : (A A' B B' : RawType)
    (pA : Acc _<_ (tyDepth A)) (pA' : Acc _<_ (tyDepth A'))
    (pB : Acc _<_ (tyDepth B)) (pB' : Acc _<_ (tyDepth B'))
  -> A ≡ A' -> B ≡ B'
  -> ComputableTyEqAcc A B pA pB
  -> ComputableTyEqAcc A' B' pA' pB'
tyEqAcc-ty-subst A .A B .B pA pA' pB pB' refl refl c =
  ComputableTyEqAcc-cast A B pA pA' pB pB' c

mutual
  compTm-convAcc : (A B : RawType)
      (pA : Acc _<_ (tyDepth A)) (pB : Acc _<_ (tyDepth B)) {t : RawTerm}
    -> ComputableTyEqAcc A B pA pB
    -> ComputableTmAcc A pA t
    -> ComputableTmAcc B pB t
  compTm-convAcc tyTop tyTop pA pB eq ct = ct
  compTm-convAcc tyTop (tySigma C D) pA pB eq ct = ⊥-elim eq
  compTm-convAcc tyTop (tyEq C c d) pA pB eq ct = ⊥-elim eq
  compTm-convAcc tyTop (tyQtr C) pA pB eq ct = ⊥-elim eq
  compTm-convAcc (tySigma A B) tyTop pA pB eq ct = ⊥-elim eq
  compTm-convAcc (tySigma A B) (tySigma C D) (acc rsAB) (acc rsCD) (eqAC , eqBD) ct =
    let
      a , b , evt , ca , cb = ct
      ctyA = proj₁ (compTyEq-sidesAcc A C
        (rsAB (tyDepth-fst<Sigma A B)) (rsCD (tyDepth-fst<Sigma C D)) eqAC)
      eqAA = compTmEq-reflAcc A (rsAB (tyDepth-fst<Sigma A B)) ctyA ca
      eqBaDa = eqBD a a eqAA
    in
    a , b , evt ,
    compTm-convAcc A C
      (rsAB (tyDepth-fst<Sigma A B)) (rsCD (tyDepth-fst<Sigma C D))
      eqAC ca ,
    compTm-convAcc (subTy (singleSubst a) B) (subTy (singleSubst a) D)
      (rsAB (subTy-snd< A B a)) (rsCD (subTy-snd< C D a))
      eqBaDa cb
  compTm-convAcc (tySigma A B) (tyEq C c d) pA pB eq ct = ⊥-elim eq
  compTm-convAcc (tySigma A B) (tyQtr C) pA pB eq ct = ⊥-elim eq
  compTm-convAcc (tyEq A a b) tyTop pA pB eq ct = ⊥-elim eq
  compTm-convAcc (tyEq A a b) (tySigma C D) pA pB eq ct = ⊥-elim eq
  compTm-convAcc (tyEq A a b) (tyEq C c d) (acc rsL) (acc rsR) (eqAC , eqac , eqbd) (evt , eqab) =
    let
      pA = rsL (tyDepth-base<Eq A a b)
      pC = rsR (tyDepth-base<Eq C c d)
      eqcb = compTmEq-transAcc A pA (compTmEq-symAcc A pA eqac) eqab
      eqcd = compTmEq-transAcc A pA eqcb eqbd
    in
    evt , compTmEq-convAcc A C pA pC eqAC eqcd
  compTm-convAcc (tyEq A a b) (tyQtr C) pA pB eq ct = ⊥-elim eq
  compTm-convAcc (tyQtr A) tyTop pA pB eq ct = ⊥-elim eq
  compTm-convAcc (tyQtr A) (tySigma C D) pA pB eq ct = ⊥-elim eq
  compTm-convAcc (tyQtr A) (tyEq C c d) pA pB eq ct = ⊥-elim eq
  compTm-convAcc (tyQtr A) (tyQtr C) (acc rsL) (acc rsR) eqAC (a , evt , ca) =
    a , evt ,
    compTm-convAcc A C
      (rsL (tyDepth-base<Qtr A)) (rsR (tyDepth-base<Qtr C))
      eqAC ca

  compTmEq-reflAcc : (A : RawType) (pA : Acc _<_ (tyDepth A)) {t : RawTerm}
    -> ComputableTyAcc A pA
    -> ComputableTmAcc A pA t
    -> ComputableTmEqAcc A pA t t
  compTmEq-reflAcc tyTop pA cty ct = ct , ct
  compTmEq-reflAcc (tySigma A B) (acc rs) (ctyA , fam) ct =
    let
      a , b , evt , ca , cb = ct
      eqAA = compTmEq-reflAcc A (rs (tyDepth-fst<Sigma A B)) ctyA ca
      tyBB = fam a a eqAA
      ctyB = proj₁ (compTyEq-sidesAcc (subTy (singleSubst a) B) (subTy (singleSubst a) B)
        (rs (subTy-snd< A B a)) (rs (subTy-snd< A B a)) tyBB)
    in
    a , b , a , b , evt , evt ,
    eqAA ,
    compTmEq-reflAcc (subTy (singleSubst a) B) (rs (subTy-snd< A B a)) ctyB cb ,
    tyBB
  compTmEq-reflAcc (tyEq A a b) (acc rs) cty (evt , eqab) = evt , evt , eqab
  compTmEq-reflAcc (tyQtr A) (acc rs) ctyA (a , evt , ca) =
    let eqAA = compTmEq-reflAcc A (rs (tyDepth-base<Qtr A)) ctyA ca in
    a , a , evt , evt , eqAA , eqAA

  compTmEq-symAcc : (A : RawType) (pA : Acc _<_ (tyDepth A)) {t u : RawTerm}
    -> ComputableTmEqAcc A pA t u
    -> ComputableTmEqAcc A pA u t
  compTmEq-symAcc tyTop pA (evt , evu) = evu , evt
  compTmEq-symAcc (tySigma A B) (acc rs) eq =
    let
      a , b , c , d , evt , evu , eqAC , eqBD , tyBD = eq
      tyDB =
        compTyEq-symAcc (subTy (singleSubst a) B) (subTy (singleSubst c) B)
          (rs (subTy-snd< A B a)) (rs (subTy-snd< A B c)) tyBD
      eqDB =
        compTmEq-convAcc (subTy (singleSubst a) B) (subTy (singleSubst c) B)
          (rs (subTy-snd< A B a)) (rs (subTy-snd< A B c))
          tyBD
          (compTmEq-symAcc (subTy (singleSubst a) B) (rs (subTy-snd< A B a)) eqBD)
    in
    c , d , a , b , evu , evt ,
    compTmEq-symAcc A (rs (tyDepth-fst<Sigma A B)) eqAC ,
    eqDB ,
    tyDB
  compTmEq-symAcc (tyEq A a b) (acc rs) (evt , evu , eqab) =
    evu , evt , eqab
  compTmEq-symAcc (tyQtr A) (acc rs) (a , b , evt , evu , caa , cbb) =
    b , a , evu , evt , cbb , caa

  compTmEq-transAcc : (A : RawType) (pA : Acc _<_ (tyDepth A))
      {t u v : RawTerm}
    -> ComputableTmEqAcc A pA t u
    -> ComputableTmEqAcc A pA u v
    -> ComputableTmEqAcc A pA t v
  compTmEq-transAcc tyTop pA (evt , evu) (evu' , evv) = evt , evv
  compTmEq-transAcc (tySigma A B) (acc rs) eq₁ eq₂ =
    let
      a , b , c , d , evt , evu₁ , eqAC , eqBD , tyBD = eq₁
      e , f , g , h , evu₂ , evv , eqEG , eqFH , tyFH = eq₂
      pairEq = evalDetTm evu₁ evu₂
      cEq = tmPairInj₁ pairEq
      dEq = tmPairInj₂ pairEq
      pA = rs (tyDepth-fst<Sigma A B)
      pBa = rs (subTy-snd< A B a)
      pBc = rs (subTy-snd< A B c)
      pBe = rs (subTy-snd< A B e)
      pBg = rs (subTy-snd< A B g)
      eqCG =
        subst
          (λ x -> ComputableTmEqAcc A pA x g)
          (sym cEq)
          eqEG
      eqDH-e =
        subst
          (λ x -> ComputableTmEqAcc (subTy (singleSubst e) B) pBe x h)
          (sym dEq)
          eqFH
      eToC = subTyEq (singleSubst-apply-cong (sym cEq)) B
      eqDH-c =
        tmEqAcc-ty-subst
          (subTy (singleSubst e) B) (subTy (singleSubst c) B)
          pBe pBc
          d h
          eToC
          eqDH-e
      eqDH-a =
        compTmEq-convAcc (subTy (singleSubst c) B) (subTy (singleSubst a) B)
          pBc pBa
          (compTyEq-symAcc (subTy (singleSubst a) B) (subTy (singleSubst c) B)
            pBa pBc tyBD)
          eqDH-c
      tyFH-c =
        tyEqAcc-ty-subst
          (subTy (singleSubst e) B) (subTy (singleSubst c) B)
          (subTy (singleSubst g) B) (subTy (singleSubst g) B)
          pBe pBc pBg pBg
          eToC refl tyFH
      tyBH =
        compTyEq-transAcc (subTy (singleSubst a) B) (subTy (singleSubst c) B)
          (subTy (singleSubst g) B)
          pBa pBc pBg
          tyBD tyFH-c
    in
    a , b , g , h , evt , evv ,
    compTmEq-transAcc A pA eqAC eqCG ,
    compTmEq-transAcc (subTy (singleSubst a) B) pBa eqBD eqDH-a ,
    tyBH
  compTmEq-transAcc (tyEq A a b) (acc rs) (evt , evu , eqab) (evu' , evv , eqab') =
    evt , evv , eqab
  compTmEq-transAcc (tyQtr A) (acc rs) (a , b , evt , evu , caa , cbb) (c , d , evu' , evv , ccc , cdd) =
    a , d , evt , evv , caa , cdd

  compTmEq-sidesAcc : (A : RawType) (pA : Acc _<_ (tyDepth A)) {t u : RawTerm}
    -> ComputableTmEqAcc A pA t u
    -> ComputableTmAcc A pA t × ComputableTmAcc A pA u
  compTmEq-sidesAcc tyTop pA (evt , evu) = evt , evu
  compTmEq-sidesAcc (tySigma A B) (acc rs) eq =
    let
      a , b , c , d , evt , evu , eqAC , eqBD , tyBD = eq
      ca , cc = compTmEq-sidesAcc A (rs (tyDepth-fst<Sigma A B)) eqAC
      cb , cd = compTmEq-sidesAcc (subTy (singleSubst a) B) (rs (subTy-snd< A B a)) eqBD
      cd' =
        compTm-convAcc (subTy (singleSubst a) B) (subTy (singleSubst c) B)
          (rs (subTy-snd< A B a)) (rs (subTy-snd< A B c))
          tyBD cd
    in
    (a , b , evt , ca , cb) ,
    (c , d , evu , cc , cd')
  compTmEq-sidesAcc (tyEq A a b) (acc rs) (evt , evu , eqab) =
    (evt , eqab) , (evu , eqab)
  compTmEq-sidesAcc (tyQtr A) (acc rs) (a , b , evt , evu , caa , cbb) =
    let
      ca = proj₁ (compTmEq-sidesAcc A (rs (tyDepth-base<Qtr A)) caa)
      cb = proj₁ (compTmEq-sidesAcc A (rs (tyDepth-base<Qtr A)) cbb)
    in
    (a , evt , ca) , (b , evu , cb)

  compTmEq-convAcc : (A B : RawType)
      (pA : Acc _<_ (tyDepth A)) (pB : Acc _<_ (tyDepth B))
      {t u : RawTerm}
    -> ComputableTyEqAcc A B pA pB
    -> ComputableTmEqAcc A pA t u
    -> ComputableTmEqAcc B pB t u
  compTmEq-convAcc tyTop tyTop pA pB eq etu = etu
  compTmEq-convAcc tyTop (tySigma C D) pA pB eq etu = ⊥-elim eq
  compTmEq-convAcc tyTop (tyEq C c d) pA pB eq etu = ⊥-elim eq
  compTmEq-convAcc tyTop (tyQtr C) pA pB eq etu = ⊥-elim eq
  compTmEq-convAcc (tySigma A B) tyTop pA pB eq etu = ⊥-elim eq
  compTmEq-convAcc (tySigma A B) (tySigma C D) (acc rsAB) (acc rsCD) (eqAC , eqBD) etu =
    let
      a , b , c , d , evt , evu , eqA , eqB , tyB = etu
      pA = rsAB (tyDepth-fst<Sigma A B)
      pC = rsCD (tyDepth-fst<Sigma C D)
      pBa = rsAB (subTy-snd< A B a)
      pBc = rsAB (subTy-snd< A B c)
      pDa = rsCD (subTy-snd< C D a)
      pDc = rsCD (subTy-snd< C D c)
      eqAA = compTmEq-transAcc A pA eqA (compTmEq-symAcc A pA eqA)
      eqCC = compTmEq-transAcc A pA (compTmEq-symAcc A pA eqA) eqA
      tyBaDa = eqBD a a eqAA
      tyBcDc = eqBD c c eqCC
      tyDaBa =
        compTyEq-symAcc (subTy (singleSubst a) B) (subTy (singleSubst a) D)
          pBa pDa tyBaDa
      tyBaDc =
        compTyEq-transAcc (subTy (singleSubst a) B) (subTy (singleSubst c) B)
          (subTy (singleSubst c) D)
          pBa pBc pDc
          tyB tyBcDc
      tyDaDc =
        compTyEq-transAcc (subTy (singleSubst a) D) (subTy (singleSubst a) B)
          (subTy (singleSubst c) D)
          pDa pBa pDc
          tyDaBa tyBaDc
    in
    a , b , c , d , evt , evu ,
    compTmEq-convAcc A C pA pC eqAC eqA ,
    compTmEq-convAcc (subTy (singleSubst a) B) (subTy (singleSubst a) D)
      pBa pDa tyBaDa eqB ,
    tyDaDc
  compTmEq-convAcc (tySigma A B) (tyEq C c d) pA pB eq etu = ⊥-elim eq
  compTmEq-convAcc (tySigma A B) (tyQtr C) pA pB eq etu = ⊥-elim eq
  compTmEq-convAcc (tyEq A a b) tyTop pA pB eq etu = ⊥-elim eq
  compTmEq-convAcc (tyEq A a b) (tySigma C D) pA pB eq etu = ⊥-elim eq
  compTmEq-convAcc (tyEq A a b) (tyEq C c d) (acc rsL) (acc rsR) (eqAC , eqac , eqbd) (evt , evu , eqab) =
    let
      pA = rsL (tyDepth-base<Eq A a b)
      pC = rsR (tyDepth-base<Eq C c d)
      eqcb = compTmEq-transAcc A pA (compTmEq-symAcc A pA eqac) eqab
      eqcd = compTmEq-transAcc A pA eqcb eqbd
    in
    evt , evu , compTmEq-convAcc A C pA pC eqAC eqcd
  compTmEq-convAcc (tyEq A a b) (tyQtr C) pA pB eq etu = ⊥-elim eq
  compTmEq-convAcc (tyQtr A) tyTop pA pB eq etu = ⊥-elim eq
  compTmEq-convAcc (tyQtr A) (tySigma C D) pA pB eq etu = ⊥-elim eq
  compTmEq-convAcc (tyQtr A) (tyEq C c d) pA pB eq etu = ⊥-elim eq
  compTmEq-convAcc (tyQtr A) (tyQtr C) (acc rsL) (acc rsR) eqAC (a , b , evt , evu , caa , cbb) =
    a , b , evt , evu ,
    compTmEq-convAcc A C
      (rsL (tyDepth-base<Qtr A)) (rsR (tyDepth-base<Qtr C))
      eqAC caa ,
    compTmEq-convAcc A C
      (rsL (tyDepth-base<Qtr A)) (rsR (tyDepth-base<Qtr C))
      eqAC cbb

  compTyEq-reflAcc : (A : RawType) (pA : Acc _<_ (tyDepth A))
    -> ComputableTyAcc A pA
    -> ComputableTyEqAcc A A pA pA
  compTyEq-reflAcc tyTop pA ct = tt
  compTyEq-reflAcc (tySigma A B) (acc rs) (ctA , fam) =
    compTyEq-reflAcc A (rs (tyDepth-fst<Sigma A B)) ctA ,
    λ a c eq -> fam a c eq
  compTyEq-reflAcc (tyEq A a b) (acc rs) (ctA , ca , cb) =
    let
      pA = rs (tyDepth-base<Eq A a b)
      ca' = ComputableTmAcc-cast A (<-wf (tyDepth A)) pA a ca
      cb' = ComputableTmAcc-cast A (<-wf (tyDepth A)) pA b cb
    in
    compTyEq-reflAcc A (rs (tyDepth-base<Eq A a b)) ctA ,
    compTmEq-reflAcc A pA ctA ca' ,
    compTmEq-reflAcc A pA ctA cb'
  compTyEq-reflAcc (tyQtr A) (acc rs) ctA =
    compTyEq-reflAcc A (rs (tyDepth-base<Qtr A)) ctA

  compTyEq-symAcc : (A B : RawType)
      (pA : Acc _<_ (tyDepth A)) (pB : Acc _<_ (tyDepth B))
    -> ComputableTyEqAcc A B pA pB
    -> ComputableTyEqAcc B A pB pA
  compTyEq-symAcc tyTop tyTop pA pB eq = tt
  compTyEq-symAcc tyTop (tySigma C D) pA pB eq = ⊥-elim eq
  compTyEq-symAcc tyTop (tyEq C c d) pA pB eq = ⊥-elim eq
  compTyEq-symAcc tyTop (tyQtr C) pA pB eq = ⊥-elim eq
  compTyEq-symAcc (tySigma A B) tyTop pA pB eq = ⊥-elim eq
  compTyEq-symAcc (tySigma A B) (tySigma C D) (acc rsAB) (acc rsCD) (eqAC , eqBD) =
    let
      pA = rsAB (tyDepth-fst<Sigma A B)
      pC = rsCD (tyDepth-fst<Sigma C D)
      eqCA = compTyEq-symAcc A C pA pC eqAC
    in
    eqCA ,
    λ c a eqCAca ->
      let
        eqAac = compTmEq-convAcc C A pC pA eqCA (compTmEq-symAcc C pC eqCAca)
      in
      compTyEq-symAcc (subTy (singleSubst a) B) (subTy (singleSubst c) D)
        (rsAB (subTy-snd< A B a)) (rsCD (subTy-snd< C D c))
        (eqBD a c eqAac)
  compTyEq-symAcc (tySigma A B) (tyEq C c d) pA pB eq = ⊥-elim eq
  compTyEq-symAcc (tySigma A B) (tyQtr C) pA pB eq = ⊥-elim eq
  compTyEq-symAcc (tyEq A a b) tyTop pA pB eq = ⊥-elim eq
  compTyEq-symAcc (tyEq A a b) (tySigma C D) pA pB eq = ⊥-elim eq
  compTyEq-symAcc (tyEq A a b) (tyEq C c d) (acc rsL) (acc rsR) (eqAC , eqac , eqbd) =
    let
      pA = rsL (tyDepth-base<Eq A a b)
      pC = rsR (tyDepth-base<Eq C c d)
      eqCA = compTyEq-symAcc A C pA pC eqAC
    in
    eqCA ,
    compTmEq-convAcc A C pA pC eqAC (compTmEq-symAcc A pA eqac) ,
    compTmEq-convAcc A C pA pC eqAC (compTmEq-symAcc A pA eqbd)
  compTyEq-symAcc (tyEq A a b) (tyQtr C) pA pB eq = ⊥-elim eq
  compTyEq-symAcc (tyQtr A) tyTop pA pB eq = ⊥-elim eq
  compTyEq-symAcc (tyQtr A) (tySigma C D) pA pB eq = ⊥-elim eq
  compTyEq-symAcc (tyQtr A) (tyEq C c d) pA pB eq = ⊥-elim eq
  compTyEq-symAcc (tyQtr A) (tyQtr C) (acc rsL) (acc rsR) eqAC =
    compTyEq-symAcc A C
      (rsL (tyDepth-base<Qtr A)) (rsR (tyDepth-base<Qtr C))
      eqAC

  compTyEq-transAcc : (A B C : RawType)
      (pA : Acc _<_ (tyDepth A)) (pB : Acc _<_ (tyDepth B)) (pC : Acc _<_ (tyDepth C))
    -> ComputableTyEqAcc A B pA pB
    -> ComputableTyEqAcc B C pB pC
    -> ComputableTyEqAcc A C pA pC
  compTyEq-transAcc tyTop tyTop tyTop pA pB pC eqAB eqBC = tt
  compTyEq-transAcc tyTop tyTop (tySigma E F) pA pB pC eqAB eqBC = ⊥-elim eqBC
  compTyEq-transAcc tyTop tyTop (tyEq E e f) pA pB pC eqAB eqBC = ⊥-elim eqBC
  compTyEq-transAcc tyTop tyTop (tyQtr E) pA pB pC eqAB eqBC = ⊥-elim eqBC
  compTyEq-transAcc tyTop (tySigma C D) E pA pB pC eqAB eqBC = ⊥-elim eqAB
  compTyEq-transAcc tyTop (tyEq C c d) E pA pB pC eqAB eqBC = ⊥-elim eqAB
  compTyEq-transAcc tyTop (tyQtr C) E pA pB pC eqAB eqBC = ⊥-elim eqAB
  compTyEq-transAcc (tySigma A B) tyTop E pA pB pC eqAB eqBC = ⊥-elim eqAB
  compTyEq-transAcc (tySigma A B) (tySigma C D) tyTop pA pB pC eqAB eqBC = ⊥-elim eqBC
  compTyEq-transAcc
    (tySigma A B) (tySigma C D) (tySigma E F)
    (acc rsAB) (acc rsCD) (acc rsEF)
    (eqAC , eqBD) (eqCE , eqDF) =
    let
      pA = rsAB (tyDepth-fst<Sigma A B)
      pC = rsCD (tyDepth-fst<Sigma C D)
      pE = rsEF (tyDepth-fst<Sigma E F)
      eqAE = compTyEq-transAcc A C E pA pC pE eqAC eqCE
    in
    eqAE ,
    λ a e eqAae ->
      let
        eqAaa = compTmEq-transAcc A pA eqAae (compTmEq-symAcc A pA eqAae)
        eqCae = compTmEq-convAcc A C pA pC eqAC eqAae
        eqCee = compTmEq-transAcc C pC (compTmEq-symAcc C pC eqCae) eqCae
      in
      compTyEq-transAcc (subTy (singleSubst a) B) (subTy (singleSubst e) D)
        (subTy (singleSubst e) F)
        (rsAB (subTy-snd< A B a))
        (rsCD (subTy-snd< C D e))
        (rsEF (subTy-snd< E F e))
        (eqBD a e eqAae)
        (eqDF e e eqCee)
  compTyEq-transAcc (tySigma A B) (tySigma C D) (tyEq E e f) pA pB pC eqAB eqBC = ⊥-elim eqBC
  compTyEq-transAcc (tySigma A B) (tySigma C D) (tyQtr E) pA pB pC eqAB eqBC = ⊥-elim eqBC
  compTyEq-transAcc (tySigma A B) (tyEq C c d) E pA pB pC eqAB eqBC = ⊥-elim eqAB
  compTyEq-transAcc (tySigma A B) (tyQtr C) E pA pB pC eqAB eqBC = ⊥-elim eqAB
  compTyEq-transAcc (tyEq A a b) tyTop E pA pB pC eqAB eqBC = ⊥-elim eqAB
  compTyEq-transAcc (tyEq A a b) (tySigma C D) E pA pB pC eqAB eqBC = ⊥-elim eqAB
  compTyEq-transAcc (tyEq A a b) (tyEq C c d) tyTop pA pB pC eqAB eqBC = ⊥-elim eqBC
  compTyEq-transAcc (tyEq A a b) (tyEq C c d) (tySigma E F) pA pB pC eqAB eqBC = ⊥-elim eqBC
  compTyEq-transAcc
    (tyEq A a b) (tyEq C c d) (tyEq E e f)
    (acc rsAB) (acc rsCD) (acc rsEF)
    (eqAC , eqac , eqbd) (eqCE , eqce , eqdf) =
    let
      pA = rsAB (tyDepth-base<Eq A a b)
      pC = rsCD (tyDepth-base<Eq C c d)
      pE = rsEF (tyDepth-base<Eq E e f)
      eqAE = compTyEq-transAcc A C E pA pC pE eqAC eqCE
      eqceA =
        compTmEq-convAcc C A pC pA
          (compTyEq-symAcc A C pA pC eqAC)
          eqce
      eqdfA =
        compTmEq-convAcc C A pC pA
          (compTyEq-symAcc A C pA pC eqAC)
          eqdf
    in
    eqAE ,
    compTmEq-transAcc A pA eqac eqceA ,
    compTmEq-transAcc A pA eqbd eqdfA
  compTyEq-transAcc (tyEq A a b) (tyEq C c d) (tyQtr E) pA pB pC eqAB eqBC = ⊥-elim eqBC
  compTyEq-transAcc (tyEq A a b) (tyQtr C) E pA pB pC eqAB eqBC = ⊥-elim eqAB
  compTyEq-transAcc (tyQtr A) tyTop E pA pB pC eqAB eqBC = ⊥-elim eqAB
  compTyEq-transAcc (tyQtr A) (tySigma C D) E pA pB pC eqAB eqBC = ⊥-elim eqAB
  compTyEq-transAcc (tyQtr A) (tyEq C c d) E pA pB pC eqAB eqBC = ⊥-elim eqAB
  compTyEq-transAcc (tyQtr A) (tyQtr C) tyTop pA pB pC eqAB eqBC = ⊥-elim eqBC
  compTyEq-transAcc (tyQtr A) (tyQtr C) (tySigma E F) pA pB pC eqAB eqBC = ⊥-elim eqBC
  compTyEq-transAcc (tyQtr A) (tyQtr C) (tyEq E e f) pA pB pC eqAB eqBC = ⊥-elim eqBC
  compTyEq-transAcc (tyQtr A) (tyQtr C) (tyQtr E) (acc rsA) (acc rsC) (acc rsE) eqAC eqCE =
    compTyEq-transAcc A C E
      (rsA (tyDepth-base<Qtr A))
      (rsC (tyDepth-base<Qtr C))
      (rsE (tyDepth-base<Qtr E))
      eqAC eqCE

  compTyEq-sidesAcc : (A B : RawType)
      (pA : Acc _<_ (tyDepth A)) (pB : Acc _<_ (tyDepth B))
    -> ComputableTyEqAcc A B pA pB
    -> ComputableTyAcc A pA × ComputableTyAcc B pB
  compTyEq-sidesAcc tyTop tyTop pA pB eq = tt , tt
  compTyEq-sidesAcc tyTop (tySigma C D) pA pB eq = ⊥-elim eq
  compTyEq-sidesAcc tyTop (tyEq C c d) pA pB eq = ⊥-elim eq
  compTyEq-sidesAcc tyTop (tyQtr C) pA pB eq = ⊥-elim eq
  compTyEq-sidesAcc (tySigma A B) tyTop pA pB eq = ⊥-elim eq
  compTyEq-sidesAcc (tySigma A B) (tySigma C D) (acc rsAB) (acc rsCD) (eqAC , eqBD) =
    let
      pA = rsAB (tyDepth-fst<Sigma A B)
      pC = rsCD (tyDepth-fst<Sigma C D)
      ctyA , ctyC = compTyEq-sidesAcc A C pA pC eqAC
      leftFam =
        λ a c eqAac ->
          let
            eqAcc = compTmEq-transAcc A pA (compTmEq-symAcc A pA eqAac) eqAac
            tyBaDc = eqBD a c eqAac
            tyBcDc = eqBD c c eqAcc
          in
          compTyEq-transAcc (subTy (singleSubst a) B) (subTy (singleSubst c) D)
            (subTy (singleSubst c) B)
            (rsAB (subTy-snd< A B a))
            (rsCD (subTy-snd< C D c))
            (rsAB (subTy-snd< A B c))
            tyBaDc
            (compTyEq-symAcc (subTy (singleSubst c) B) (subTy (singleSubst c) D)
              (rsAB (subTy-snd< A B c)) (rsCD (subTy-snd< C D c))
              tyBcDc)
      rightFam =
        λ c d eqCcd ->
          let
            eqCA = compTyEq-symAcc A C pA pC eqAC
            eqAcd = compTmEq-convAcc C A pC pA eqCA eqCcd
            eqAcc = compTmEq-transAcc A pA eqAcd (compTmEq-symAcc A pA eqAcd)
            tyBcDd = eqBD c d eqAcd
            tyBcDc = eqBD c c eqAcc
          in
          compTyEq-transAcc (subTy (singleSubst c) D) (subTy (singleSubst c) B)
            (subTy (singleSubst d) D)
            (rsCD (subTy-snd< C D c))
            (rsAB (subTy-snd< A B c))
            (rsCD (subTy-snd< C D d))
            (compTyEq-symAcc (subTy (singleSubst c) B) (subTy (singleSubst c) D)
              (rsAB (subTy-snd< A B c)) (rsCD (subTy-snd< C D c))
              tyBcDc)
            tyBcDd
    in
    (ctyA , leftFam) , (ctyC , rightFam)
  compTyEq-sidesAcc (tySigma A B) (tyEq C c d) pA pB eq = ⊥-elim eq
  compTyEq-sidesAcc (tySigma A B) (tyQtr C) pA pB eq = ⊥-elim eq
  compTyEq-sidesAcc (tyEq A a b) tyTop pA pB eq = ⊥-elim eq
  compTyEq-sidesAcc (tyEq A a b) (tySigma C D) pA pB eq = ⊥-elim eq
  compTyEq-sidesAcc (tyEq A a b) (tyEq C c d) (acc rsL) (acc rsR) (eqAC , eqac , eqbd) =
    let
      pA = rsL (tyDepth-base<Eq A a b)
      pC = rsR (tyDepth-base<Eq C c d)
      ctyA , ctyC = compTyEq-sidesAcc A C pA pC eqAC
      ca , ccA = compTmEq-sidesAcc A pA eqac
      cb , cdA = compTmEq-sidesAcc A pA eqbd
      cc = compTm-convAcc A C pA pC eqAC ccA
      cd = compTm-convAcc A C pA pC eqAC cdA
      ca' = ComputableTmAcc-cast A pA (<-wf (tyDepth A)) a ca
      cb' = ComputableTmAcc-cast A pA (<-wf (tyDepth A)) b cb
      cc' = ComputableTmAcc-cast C pC (<-wf (tyDepth C)) c cc
      cd' = ComputableTmAcc-cast C pC (<-wf (tyDepth C)) d cd
    in
    (ctyA , ca' , cb') , (ctyC , cc' , cd')
  compTyEq-sidesAcc (tyEq A a b) (tyQtr C) pA pB eq = ⊥-elim eq
  compTyEq-sidesAcc (tyQtr A) tyTop pA pB eq = ⊥-elim eq
  compTyEq-sidesAcc (tyQtr A) (tySigma C D) pA pB eq = ⊥-elim eq
  compTyEq-sidesAcc (tyQtr A) (tyEq C c d) pA pB eq = ⊥-elim eq
  compTyEq-sidesAcc (tyQtr A) (tyQtr C) (acc rsL) (acc rsR) eqAC =
    compTyEq-sidesAcc A C
      (rsL (tyDepth-base<Qtr A)) (rsR (tyDepth-base<Qtr C))
      eqAC

compTm-conv : {A B : RawType} {t : RawTerm}
  -> ComputableTyEq A B -> Computable A t -> Computable B t
compTm-conv {A} {B} eq ct =
  compTm-convAcc A B (<-wf (tyDepth A)) (<-wf (tyDepth B)) eq ct

compTmEq-refl : {A : RawType} {t : RawTerm}
  -> ComputableTy A -> Computable A t -> ComputableTmEq A t t
compTmEq-refl {A} cty ct = compTmEq-reflAcc A (<-wf (tyDepth A)) cty ct

compTmEq-sym : {A : RawType} {t u : RawTerm}
  -> ComputableTmEq A t u -> ComputableTmEq A u t
compTmEq-sym {A} eq = compTmEq-symAcc A (<-wf (tyDepth A)) eq

compTmEq-trans : {A : RawType} {t u v : RawTerm}
  -> ComputableTmEq A t u -> ComputableTmEq A u v -> ComputableTmEq A t v
compTmEq-trans {A} eq₁ eq₂ =
  compTmEq-transAcc A (<-wf (tyDepth A)) eq₁ eq₂

compTmEq-sides : {A : RawType} {t u : RawTerm}
  -> ComputableTmEq A t u -> Computable A t × Computable A u
compTmEq-sides {A} eq =
  compTmEq-sidesAcc A (<-wf (tyDepth A)) eq

compTmEq-conv : {A B : RawType} {t u : RawTerm}
  -> ComputableTyEq A B -> ComputableTmEq A t u -> ComputableTmEq B t u
compTmEq-conv {A} {B} eq etu =
  compTmEq-convAcc A B (<-wf (tyDepth A)) (<-wf (tyDepth B)) eq etu

compTyEq-refl : {A : RawType} -> ComputableTy A -> ComputableTyEq A A
compTyEq-refl {A} ct = compTyEq-reflAcc A (<-wf (tyDepth A)) ct

compTyEq-sym : {A B : RawType} -> ComputableTyEq A B -> ComputableTyEq B A
compTyEq-sym {A} {B} eq =
  compTyEq-symAcc A B (<-wf (tyDepth A)) (<-wf (tyDepth B)) eq

compTyEq-trans : {A B C : RawType}
  -> ComputableTyEq A B -> ComputableTyEq B C -> ComputableTyEq A C
compTyEq-trans {A} {B} {C} eqAB eqBC =
  compTyEq-transAcc A B C
    (<-wf (tyDepth A)) (<-wf (tyDepth B)) (<-wf (tyDepth C))
    eqAB eqBC

compTyEq-sides : {A B : RawType}
  -> ComputableTyEq A B -> ComputableTy A × ComputableTy B
compTyEq-sides {A} {B} eq =
  compTyEq-sidesAcc A B (<-wf (tyDepth A)) (<-wf (tyDepth B)) eq
