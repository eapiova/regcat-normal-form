{-# OPTIONS --safe #-}

module Tait.CompLemmas where

open import Tait.Prelude
open import Data.Empty using (⊥-elim)
open import Data.Nat using (_<_)
open import Data.Nat.Induction using () renaming (<-wellFounded to <-wf)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit using (tt)
open import Induction.WellFounded using (Acc ; acc)

open import Tait.Syntax
open import Tait.Substitution
open import Tait.Measure
open import Tait.Evaluation
open import Tait.Computable

subTyConst : (sigma tau : Subst) (A : RawType) -> subTy sigma A ≡ subTy tau A
subTyConst sigma tau tyTop = refl
subTyConst sigma tau (tySigma A B) =
  cong₂ tySigma
    (subTyConst sigma tau A)
    (subTyConst (liftSubst sigma) (liftSubst tau) B)

evalResultValue : {t g : RawTerm} -> t =>e g -> g =>e g
evalResultValue evalStar = evalStar
evalResultValue evalPair = evalPair
evalResultValue (evalElSigma evd evm) = evalResultValue evm

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

compTm-=>e-fwd : {A : RawType} {t g : RawTerm}
  -> t =>e g -> Computable A t -> Computable A g
compTm-=>e-fwd {A = tyTop} ev ct = eval-=>e-fwd ev ct
compTm-=>e-fwd {A = tySigma A B} ev ct =
  let a , b , evt , ca , cb = computableSigma-elim ct in
  computableSigma-intro (a , b , eval-=>e-fwd ev evt , ca , cb)

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

compTm-convAcc : (A B : RawType)
    (pA : Acc _<_ (tyDepth A)) (pB : Acc _<_ (tyDepth B)) {t : RawTerm}
  -> ComputableTyEqAcc A B pA pB
  -> ComputableTmAcc A pA t
  -> ComputableTmAcc B pB t
compTm-convAcc tyTop tyTop pA pB eq ct = ct
compTm-convAcc tyTop (tySigma C D) pA pB eq ct = ⊥-elim eq
compTm-convAcc (tySigma A B) tyTop pA pB eq ct = ⊥-elim eq
compTm-convAcc (tySigma A B) (tySigma C D) (acc rsAB) (acc rsCD) {t} (eqAC , eqBD) ct =
  let
    a , b , evt , ca , cb = ct
    caCanonical =
      ComputableTmAcc-cast A
        (rsAB (tyDepth-fst<Sigma A B)) (<-wf (tyDepth A)) a ca
  in
  a , b , evt ,
  compTm-convAcc A C
    (rsAB (tyDepth-fst<Sigma A B)) (rsCD (tyDepth-fst<Sigma C D))
    eqAC ca ,
  compTm-convAcc (subTy (singleSubst a) B) (subTy (singleSubst a) D)
    (rsAB (subTy-snd< A B a)) (rsCD (subTy-snd< C D a))
    (eqBD a caCanonical) cb

compTm-conv : {A B : RawType} {t : RawTerm}
  -> ComputableTyEq A B -> Computable A t -> Computable B t
compTm-conv {A} {B} eq ct =
  compTm-convAcc A B (<-wf (tyDepth A)) (<-wf (tyDepth B)) eq ct

compTmEq-reflAcc : (A : RawType) (pA : Acc _<_ (tyDepth A)) {t : RawTerm}
  -> ComputableTmAcc A pA t
  -> ComputableTmEqAcc A pA t t
compTmEq-reflAcc tyTop pA ct = ct , ct
compTmEq-reflAcc (tySigma A B) (acc rs) ct =
  let a , b , evt , ca , cb = ct in
  a , b , a , b , evt , evt ,
  compTmEq-reflAcc A (rs (tyDepth-fst<Sigma A B)) ca ,
  compTmEq-reflAcc (subTy (singleSubst a) B) (rs (subTy-snd< A B a)) cb

compTmEq-refl : {A : RawType} {t : RawTerm}
  -> Computable A t -> ComputableTmEq A t t
compTmEq-refl {A} ct = compTmEq-reflAcc A (<-wf (tyDepth A)) ct

compTmEq-symAcc : (A : RawType) (pA : Acc _<_ (tyDepth A)) {t u : RawTerm}
  -> ComputableTmEqAcc A pA t u
  -> ComputableTmEqAcc A pA u t
compTmEq-symAcc tyTop pA (evt , evu) = evu , evt
compTmEq-symAcc (tySigma A B) (acc rs) eq =
  let
    a , b , c , d , evt , evu , eqAC , eqBD = eq
    eqDB =
      compTmEq-symAcc (subTy (singleSubst a) B) (rs (subTy-snd< A B a)) eqBD
    eqDB' =
      tmEqAcc-ty-subst
        (subTy (singleSubst a) B) (subTy (singleSubst c) B)
        (rs (subTy-snd< A B a)) (rs (subTy-snd< A B c))
        d b
        (subTyConst (singleSubst a) (singleSubst c) B)
        eqDB
  in
  c , d , a , b , evu , evt ,
  compTmEq-symAcc A (rs (tyDepth-fst<Sigma A B)) eqAC ,
  eqDB'

compTmEq-sym : {A : RawType} {t u : RawTerm}
  -> ComputableTmEq A t u -> ComputableTmEq A u t
compTmEq-sym {A} eq = compTmEq-symAcc A (<-wf (tyDepth A)) eq

compTmEq-transAcc : (A : RawType) (pA : Acc _<_ (tyDepth A))
    {t u v : RawTerm}
  -> ComputableTmEqAcc A pA t u
  -> ComputableTmEqAcc A pA u v
  -> ComputableTmEqAcc A pA t v
compTmEq-transAcc tyTop pA (evt , evu) (evu' , evv) = evt , evv
compTmEq-transAcc (tySigma A B) (acc rs) eq₁ eq₂ =
  let
    a , b , c , d , evt , evu₁ , eqAC , eqBD = eq₁
    e , f , g , h , evu₂ , evv , eqEG , eqFH = eq₂
    pairEq = evalDetTm evu₁ evu₂
    cEq = tmPairInj₁ pairEq
    dEq = tmPairInj₂ pairEq
    eqCG =
      subst
        (λ x -> ComputableTmEqAcc A (rs (tyDepth-fst<Sigma A B)) x g)
        (sym cEq)
        eqEG
    eqDH-e =
      subst
        (λ x -> ComputableTmEqAcc (subTy (singleSubst e) B)
                  (rs (subTy-snd< A B e)) x h)
        (sym dEq)
        eqFH
    eqDH-c =
      tmEqAcc-ty-subst
        (subTy (singleSubst e) B) (subTy (singleSubst c) B)
        (rs (subTy-snd< A B e)) (rs (subTy-snd< A B c))
        d h
        (subTyConst (singleSubst e) (singleSubst c) B)
        eqDH-e
    eqDH-a =
      tmEqAcc-ty-subst
        (subTy (singleSubst c) B) (subTy (singleSubst a) B)
        (rs (subTy-snd< A B c)) (rs (subTy-snd< A B a))
        d h
        (subTyConst (singleSubst c) (singleSubst a) B)
        eqDH-c
  in
  a , b , g , h , evt , evv ,
  compTmEq-transAcc A (rs (tyDepth-fst<Sigma A B)) eqAC eqCG ,
  compTmEq-transAcc (subTy (singleSubst a) B) (rs (subTy-snd< A B a)) eqBD eqDH-a

compTmEq-trans : {A : RawType} {t u v : RawTerm}
  -> ComputableTmEq A t u -> ComputableTmEq A u v -> ComputableTmEq A t v
compTmEq-trans {A} eq₁ eq₂ =
  compTmEq-transAcc A (<-wf (tyDepth A)) eq₁ eq₂

compTmEq-sidesAcc : (A : RawType) (pA : Acc _<_ (tyDepth A)) {t u : RawTerm}
  -> ComputableTmEqAcc A pA t u
  -> ComputableTmAcc A pA t × ComputableTmAcc A pA u
compTmEq-sidesAcc tyTop pA (evt , evu) = evt , evu
compTmEq-sidesAcc (tySigma A B) (acc rs) eq =
  let
    a , b , c , d , evt , evu , eqAC , eqBD = eq
    ca , cc = compTmEq-sidesAcc A (rs (tyDepth-fst<Sigma A B)) eqAC
    cb , cd = compTmEq-sidesAcc (subTy (singleSubst a) B) (rs (subTy-snd< A B a)) eqBD
    cd' =
      tmAcc-ty-subst
        (subTy (singleSubst a) B) (subTy (singleSubst c) B)
        (rs (subTy-snd< A B a)) (rs (subTy-snd< A B c))
        d
        (subTyConst (singleSubst a) (singleSubst c) B)
        cd
  in
  (a , b , evt , ca , cb) ,
  (c , d , evu , cc , cd')

compTmEq-sides : {A : RawType} {t u : RawTerm}
  -> ComputableTmEq A t u -> Computable A t × Computable A u
compTmEq-sides {A} eq =
  compTmEq-sidesAcc A (<-wf (tyDepth A)) eq

compTmEq-convAcc : (A B : RawType)
    (pA : Acc _<_ (tyDepth A)) (pB : Acc _<_ (tyDepth B))
    {t u : RawTerm}
  -> ComputableTyEqAcc A B pA pB
  -> ComputableTmEqAcc A pA t u
  -> ComputableTmEqAcc B pB t u
compTmEq-convAcc tyTop tyTop pA pB eq etu = etu
compTmEq-convAcc tyTop (tySigma C D) pA pB eq etu = ⊥-elim eq
compTmEq-convAcc (tySigma A B) tyTop pA pB eq etu = ⊥-elim eq
compTmEq-convAcc (tySigma A B) (tySigma C D) (acc rsAB) (acc rsCD) (eqAC , eqBD) etu =
  let
    a , b , c , d , evt , evu , eqA , eqB = etu
    ca =
      proj₁ (compTmEq-sidesAcc A (rsAB (tyDepth-fst<Sigma A B)) eqA)
    caCanonical =
      ComputableTmAcc-cast A
        (rsAB (tyDepth-fst<Sigma A B)) (<-wf (tyDepth A)) a ca
  in
  a , b , c , d , evt , evu ,
  compTmEq-convAcc A C
    (rsAB (tyDepth-fst<Sigma A B)) (rsCD (tyDepth-fst<Sigma C D))
    eqAC eqA ,
  compTmEq-convAcc (subTy (singleSubst a) B) (subTy (singleSubst a) D)
    (rsAB (subTy-snd< A B a)) (rsCD (subTy-snd< C D a))
    (eqBD a caCanonical) eqB

compTmEq-conv : {A B : RawType} {t u : RawTerm}
  -> ComputableTyEq A B -> ComputableTmEq A t u -> ComputableTmEq B t u
compTmEq-conv {A} {B} eq etu =
  compTmEq-convAcc A B (<-wf (tyDepth A)) (<-wf (tyDepth B)) eq etu

compTyEq-reflAcc : (A : RawType) (pA : Acc _<_ (tyDepth A))
  -> ComputableTyAcc A pA
  -> ComputableTyEqAcc A A pA pA
compTyEq-reflAcc tyTop pA ct = tt
compTyEq-reflAcc (tySigma A B) (acc rs) (ctA , ctB) =
  compTyEq-reflAcc A (rs (tyDepth-fst<Sigma A B)) ctA ,
  λ a ca -> compTyEq-reflAcc (subTy (singleSubst a) B)
    (rs (subTy-snd< A B a)) (ctB a ca)

compTyEq-refl : {A : RawType} -> ComputableTy A -> ComputableTyEq A A
compTyEq-refl {A} ct = compTyEq-reflAcc A (<-wf (tyDepth A)) ct

compTyEq-symAcc : (A B : RawType)
    (pA : Acc _<_ (tyDepth A)) (pB : Acc _<_ (tyDepth B))
  -> ComputableTyEqAcc A B pA pB
  -> ComputableTyEqAcc B A pB pA
compTyEq-symAcc tyTop tyTop pA pB eq = tt
compTyEq-symAcc tyTop (tySigma C D) pA pB eq = ⊥-elim eq
compTyEq-symAcc (tySigma A B) tyTop pA pB eq = ⊥-elim eq
compTyEq-symAcc (tySigma A B) (tySigma C D) (acc rsAB) (acc rsCD) (eqAC , eqBD) =
  let
    eqCA =
      compTyEq-symAcc A C
        (rsAB (tyDepth-fst<Sigma A B)) (rsCD (tyDepth-fst<Sigma C D))
        eqAC
  in
  eqCA ,
  λ a caC ->
    let
      caC-rs =
        ComputableTmAcc-cast C
          (<-wf (tyDepth C)) (rsCD (tyDepth-fst<Sigma C D)) a caC
      caA-rs =
        compTm-convAcc C A
          (rsCD (tyDepth-fst<Sigma C D)) (rsAB (tyDepth-fst<Sigma A B))
          eqCA caC-rs
      caA =
        ComputableTmAcc-cast A
          (rsAB (tyDepth-fst<Sigma A B)) (<-wf (tyDepth A)) a caA-rs
    in
    compTyEq-symAcc (subTy (singleSubst a) B) (subTy (singleSubst a) D)
      (rsAB (subTy-snd< A B a)) (rsCD (subTy-snd< C D a))
      (eqBD a caA)

compTyEq-sym : {A B : RawType} -> ComputableTyEq A B -> ComputableTyEq B A
compTyEq-sym {A} {B} eq =
  compTyEq-symAcc A B (<-wf (tyDepth A)) (<-wf (tyDepth B)) eq

compTyEq-transAcc : (A B C : RawType)
    (pA : Acc _<_ (tyDepth A)) (pB : Acc _<_ (tyDepth B)) (pC : Acc _<_ (tyDepth C))
  -> ComputableTyEqAcc A B pA pB
  -> ComputableTyEqAcc B C pB pC
  -> ComputableTyEqAcc A C pA pC
compTyEq-transAcc tyTop tyTop tyTop pA pB pC eqAB eqBC = tt
compTyEq-transAcc tyTop tyTop (tySigma E F) pA pB pC eqAB eqBC = ⊥-elim eqBC
compTyEq-transAcc tyTop (tySigma C D) tyTop pA pB pC eqAB eqBC = ⊥-elim eqAB
compTyEq-transAcc tyTop (tySigma C D) (tySigma E F) pA pB pC eqAB eqBC = ⊥-elim eqAB
compTyEq-transAcc (tySigma A B) tyTop tyTop pA pB pC eqAB eqBC = ⊥-elim eqAB
compTyEq-transAcc (tySigma A B) tyTop (tySigma E F) pA pB pC eqAB eqBC = ⊥-elim eqAB
compTyEq-transAcc (tySigma A B) (tySigma C D) tyTop pA pB pC eqAB eqBC = ⊥-elim eqBC
compTyEq-transAcc
  (tySigma A B) (tySigma C D) (tySigma E F)
  (acc rsAB) (acc rsCD) (acc rsEF)
  (eqAC , eqBD) (eqCE , eqDF) =
  compTyEq-transAcc A C E
    (rsAB (tyDepth-fst<Sigma A B))
    (rsCD (tyDepth-fst<Sigma C D))
    (rsEF (tyDepth-fst<Sigma E F))
    eqAC eqCE ,
  λ a caA ->
    let
      caA-rs =
        ComputableTmAcc-cast A
          (<-wf (tyDepth A)) (rsAB (tyDepth-fst<Sigma A B)) a caA
      caC-rs =
        compTm-convAcc A C
          (rsAB (tyDepth-fst<Sigma A B)) (rsCD (tyDepth-fst<Sigma C D))
          eqAC caA-rs
      caC =
        ComputableTmAcc-cast C
          (rsCD (tyDepth-fst<Sigma C D)) (<-wf (tyDepth C)) a caC-rs
    in
    compTyEq-transAcc (subTy (singleSubst a) B) (subTy (singleSubst a) D)
      (subTy (singleSubst a) F)
      (rsAB (subTy-snd< A B a))
      (rsCD (subTy-snd< C D a))
      (rsEF (subTy-snd< E F a))
      (eqBD a caA)
      (eqDF a caC)

compTyEq-trans : {A B C : RawType}
  -> ComputableTyEq A B -> ComputableTyEq B C -> ComputableTyEq A C
compTyEq-trans {A} {B} {C} eqAB eqBC =
  compTyEq-transAcc A B C
    (<-wf (tyDepth A)) (<-wf (tyDepth B)) (<-wf (tyDepth C))
    eqAB eqBC
