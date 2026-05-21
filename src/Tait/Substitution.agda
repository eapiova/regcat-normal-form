{-# OPTIONS --safe #-}

module Tait.Substitution where

open import Tait.Prelude
open import Data.List.Base using (List ; [] ; _∷_ ; map)
open import Data.Nat using (ℕ ; zero ; suc ; _+_)

open import Tait.Syntax
open import Tait.Context

data Ren : Type where
  shiftRen : ℕ -> Ren
  consRen : ℕ -> Ren -> Ren

data Subst : Type where
  shiftSub : ℕ -> Subst
  consSub : RawTerm -> Subst -> Subst

applyRen : Ren -> ℕ -> ℕ
applyRen (shiftRen k) n = k + n
applyRen (consRen m rho) zero = m
applyRen (consRen m rho) (suc n) = applyRen rho n

idRen : Ren
idRen = shiftRen 0

sucRen : Ren
sucRen = shiftRen 1

addRen : ℕ -> Ren
addRen k = shiftRen k

dropRen : ℕ -> Ren -> Ren
dropRen zero rho = rho
dropRen (suc k) (shiftRen j) = shiftRen (j + suc k)
dropRen (suc k) (consRen m rho) = dropRen k rho

compRen : Ren -> Ren -> Ren
compRen rho (shiftRen k) = dropRen k rho
compRen rho (consRen m tau) = consRen (applyRen rho m) (compRen rho tau)

raiseRen : Ren -> Ren
raiseRen rho = consRen 0 (compRen sucRen rho)

keep0RenBy : ℕ -> Ren
keep0RenBy k = consRen 0 (shiftRen (suc k))

+-assoc : (a b c : ℕ) -> (a + b) + c ≡ a + (b + c)
+-assoc zero b c = refl
+-assoc (suc a) b c = cong suc (+-assoc a b c)

applyRen-dropRen : (k : ℕ) (rho : Ren) (n : ℕ)
  -> applyRen (dropRen k rho) n ≡ applyRen rho (k + n)
applyRen-dropRen zero rho n = refl
applyRen-dropRen (suc k) (shiftRen j) n = +-assoc j (suc k) n
applyRen-dropRen (suc k) (consRen m rho) n = applyRen-dropRen k rho n

applyRen-compRen : (rho tau : Ren) (n : ℕ)
  -> applyRen (compRen rho tau) n ≡ applyRen rho (applyRen tau n)
applyRen-compRen rho (shiftRen k) n = applyRen-dropRen k rho n
applyRen-compRen rho (consRen m tau) zero = refl
applyRen-compRen rho (consRen m tau) (suc n) = applyRen-compRen rho tau n

applyRen-raise-suc : (rho : Ren) (n : ℕ)
  -> applyRen (raiseRen rho) (suc n) ≡ suc (applyRen rho n)
applyRen-raise-suc rho n = applyRen-compRen sucRen rho n

raiseRen-apply-cong : {rho tau : Ren}
  -> ((n : ℕ) -> applyRen rho n ≡ applyRen tau n)
  -> (n : ℕ) -> applyRen (raiseRen rho) n ≡ applyRen (raiseRen tau) n
raiseRen-apply-cong h zero = refl
raiseRen-apply-cong {rho} {tau} h (suc n) =
  applyRen-raise-suc rho n
  ∙ cong suc (h n)
  ∙ sym (applyRen-raise-suc tau n)

mutual
  renTy : Ren -> RawType -> RawType
  renTy rho tyTop = tyTop
  renTy rho (tySigma A B) = tySigma (renTy rho A) (renTy (raiseRen rho) B)

  renTm : Ren -> RawTerm -> RawTerm
  renTm rho (var n) = var (applyRen rho n)
  renTm rho tmStar = tmStar
  renTm rho (tmPair a b) = tmPair (renTm rho a) (renTm rho b)
  renTm rho (tmElSigma d m) = tmElSigma (renTm rho d) (renTm (raiseRen (raiseRen rho)) m)

wkTyBy : ℕ -> RawType -> RawType
wkTyBy k = renTy (addRen k)

wkTmBy : ℕ -> RawTerm -> RawTerm
wkTmBy k = renTm (addRen k)

mutual
  renTyEq : {rho tau : Ren}
    -> ((n : ℕ) -> applyRen rho n ≡ applyRen tau n)
    -> (A : RawType) -> renTy rho A ≡ renTy tau A
  renTyEq h tyTop = refl
  renTyEq {rho} {tau} h (tySigma A B) =
    cong₂ tySigma (renTyEq {rho = rho} {tau = tau} h A)
      (renTyEq {rho = raiseRen rho} {tau = raiseRen tau}
        (raiseRen-apply-cong {rho = rho} {tau = tau} h) B)

  renTmEq : {rho tau : Ren}
    -> ((n : ℕ) -> applyRen rho n ≡ applyRen tau n)
    -> (t : RawTerm) -> renTm rho t ≡ renTm tau t
  renTmEq h (var n) = cong var (h n)
  renTmEq h tmStar = refl
  renTmEq {rho} {tau} h (tmPair a b) =
    cong₂ tmPair (renTmEq {rho = rho} {tau = tau} h a)
      (renTmEq {rho = rho} {tau = tau} h b)
  renTmEq {rho} {tau} h (tmElSigma d m) =
    cong₂ tmElSigma (renTmEq {rho = rho} {tau = tau} h d)
      (renTmEq {rho = raiseRen (raiseRen rho)} {tau = raiseRen (raiseRen tau)}
        (raiseRen-apply-cong {rho = raiseRen rho} {tau = raiseRen tau}
          (raiseRen-apply-cong {rho = rho} {tau = tau} h)) m)

applySubst : Subst -> ℕ -> RawTerm
applySubst (shiftSub k) n = var (k + n)
applySubst (consSub t sigma) zero = t
applySubst (consSub t sigma) (suc n) = applySubst sigma n

renToSub : Ren -> Subst
renToSub (shiftRen k) = shiftSub k
renToSub (consRen m rho) = consSub (var m) (renToSub rho)

idSubst : Subst
idSubst = shiftSub 0

keepSubstBy : ℕ -> Subst
keepSubstBy k = shiftSub k

consSubst : RawTerm -> Subst -> Subst
consSubst = consSub

replace0By : ℕ -> RawTerm -> Subst
replace0By k t = consSub t (shiftSub k)

singleSubst : RawTerm -> Subst
singleSubst = replace0By 0

dropSub : ℕ -> Subst -> Subst
dropSub zero sigma = sigma
dropSub (suc k) (shiftSub j) = shiftSub (j + suc k)
dropSub (suc k) (consSub t sigma) = dropSub k sigma

dropSubstBy : ℕ -> Subst -> Subst
dropSubstBy = dropSub

compSubRen : Subst -> Ren -> Subst
compSubRen sigma (shiftRen k) = dropSub k sigma
compSubRen sigma (consRen m rho) = consSub (applySubst sigma m) (compSubRen sigma rho)

renSub : Ren -> Subst -> Subst
renSub rho (shiftSub k) = renToSub (dropRen k rho)
renSub rho (consSub t sigma) = consSub (renTm rho t) (renSub rho sigma)

liftSubst : Subst -> Subst
liftSubst sigma = consSub (var zero) (renSub sucRen sigma)

applySubst-dropSub : (k : ℕ) (sigma : Subst) (n : ℕ)
  -> applySubst (dropSub k sigma) n ≡ applySubst sigma (k + n)
applySubst-dropSub zero sigma n = refl
applySubst-dropSub (suc k) (shiftSub j) n = cong var (+-assoc j (suc k) n)
applySubst-dropSub (suc k) (consSub t sigma) n = applySubst-dropSub k sigma n

applySubst-compSubRen : (sigma : Subst) (rho : Ren) (n : ℕ)
  -> applySubst (compSubRen sigma rho) n ≡ applySubst sigma (applyRen rho n)
applySubst-compSubRen sigma (shiftRen k) n = applySubst-dropSub k sigma n
applySubst-compSubRen sigma (consRen m rho) zero = refl
applySubst-compSubRen sigma (consRen m rho) (suc n) =
  applySubst-compSubRen sigma rho n

applySubst-renToSub : (rho : Ren) (n : ℕ)
  -> applySubst (renToSub rho) n ≡ var (applyRen rho n)
applySubst-renToSub (shiftRen k) n = refl
applySubst-renToSub (consRen m rho) zero = refl
applySubst-renToSub (consRen m rho) (suc n) = applySubst-renToSub rho n

applySubst-renSub : (rho : Ren) (sigma : Subst) (n : ℕ)
  -> applySubst (renSub rho sigma) n ≡ renTm rho (applySubst sigma n)
applySubst-renSub rho (shiftSub k) n =
  applySubst-renToSub (dropRen k rho) n
  ∙ cong var (applyRen-dropRen k rho n)
applySubst-renSub rho (consSub t sigma) zero = refl
applySubst-renSub rho (consSub t sigma) (suc n) = applySubst-renSub rho sigma n

liftSubst-apply-suc : (sigma : Subst) (n : ℕ)
  -> applySubst (liftSubst sigma) (suc n) ≡ renTm sucRen (applySubst sigma n)
liftSubst-apply-suc sigma n = applySubst-renSub sucRen sigma n

liftSubst-apply-cong : {sigma tau : Subst}
  -> ((n : ℕ) -> applySubst sigma n ≡ applySubst tau n)
  -> (n : ℕ) -> applySubst (liftSubst sigma) n ≡ applySubst (liftSubst tau) n
liftSubst-apply-cong h zero = refl
liftSubst-apply-cong {sigma} {tau} h (suc n) =
  liftSubst-apply-suc sigma n
  ∙ cong (renTm sucRen) (h n)
  ∙ sym (liftSubst-apply-suc tau n)

mutual
  subTy : Subst -> RawType -> RawType
  subTy sigma tyTop = tyTop
  subTy sigma (tySigma A B) = tySigma (subTy sigma A) (subTy (liftSubst sigma) B)

  subTm : Subst -> RawTerm -> RawTerm
  subTm sigma (var n) = applySubst sigma n
  subTm sigma tmStar = tmStar
  subTm sigma (tmPair a b) = tmPair (subTm sigma a) (subTm sigma b)
  subTm sigma (tmElSigma d m) = tmElSigma (subTm sigma d) (subTm (liftSubst (liftSubst sigma)) m)

subJ : Subst -> JForm -> JForm
subJ sigma (isType gamma A) = isType [] (subTy sigma A)
subJ sigma (typeEq gamma A B) = typeEq [] (subTy sigma A) (subTy sigma B)
subJ sigma (hasTy gamma t A) = hasTy [] (subTm sigma t) (subTy sigma A)
subJ sigma (termEq gamma t u A) = termEq [] (subTm sigma t) (subTm sigma u) (subTy sigma A)

renJ : Ren -> JForm -> JForm
renJ rho (isType gamma A) = isType (map (renTy rho) gamma) (renTy rho A)
renJ rho (typeEq gamma A B) = typeEq (map (renTy rho) gamma) (renTy rho A) (renTy rho B)
renJ rho (hasTy gamma t A) = hasTy (map (renTy rho) gamma) (renTm rho t) (renTy rho A)
renJ rho (termEq gamma t u A) =
  termEq (map (renTy rho) gamma) (renTm rho t) (renTm rho u) (renTy rho A)

compSub : Subst -> Subst -> Subst
compSub sigma (shiftSub k) = dropSub k sigma
compSub sigma (consSub t tau) = consSub (subTm sigma t) (compSub sigma tau)

applySubst-compSub : (sigma tau : Subst) (n : ℕ)
  -> applySubst (compSub sigma tau) n ≡ subTm sigma (applySubst tau n)
applySubst-compSub sigma (shiftSub k) n = applySubst-dropSub k sigma n
applySubst-compSub sigma (consSub t tau) zero = refl
applySubst-compSub sigma (consSub t tau) (suc n) = applySubst-compSub sigma tau n

mutual
  subTyEq : {sigma tau : Subst}
    -> ((n : ℕ) -> applySubst sigma n ≡ applySubst tau n)
    -> (A : RawType) -> subTy sigma A ≡ subTy tau A
  subTyEq h tyTop = refl
  subTyEq {sigma} {tau} h (tySigma A B) =
    cong₂ tySigma (subTyEq {sigma = sigma} {tau = tau} h A)
      (subTyEq {sigma = liftSubst sigma} {tau = liftSubst tau}
        (liftSubst-apply-cong {sigma = sigma} {tau = tau} h) B)

  subTmEq : {sigma tau : Subst}
    -> ((n : ℕ) -> applySubst sigma n ≡ applySubst tau n)
    -> (t : RawTerm) -> subTm sigma t ≡ subTm tau t
  subTmEq h (var n) = h n
  subTmEq h tmStar = refl
  subTmEq {sigma} {tau} h (tmPair a b) =
    cong₂ tmPair (subTmEq {sigma = sigma} {tau = tau} h a)
      (subTmEq {sigma = sigma} {tau = tau} h b)
  subTmEq {sigma} {tau} h (tmElSigma d m) =
    cong₂ tmElSigma (subTmEq {sigma = sigma} {tau = tau} h d)
      (subTmEq {sigma = liftSubst (liftSubst sigma)} {tau = liftSubst (liftSubst tau)}
        (liftSubst-apply-cong {sigma = liftSubst sigma} {tau = liftSubst tau}
          (liftSubst-apply-cong {sigma = sigma} {tau = tau} h)) m)

liftId-apply : (n : ℕ) -> applySubst (liftSubst idSubst) n ≡ applySubst idSubst n
liftId-apply zero = refl
liftId-apply (suc n) = liftSubst-apply-suc idSubst n

liftId-subTy : (A : RawType) -> subTy (liftSubst idSubst) A ≡ subTy idSubst A
liftId-subTy A =
  subTyEq {sigma = liftSubst idSubst} {tau = idSubst} liftId-apply A

liftId-subTm : (t : RawTerm) -> subTm (liftSubst idSubst) t ≡ subTm idSubst t
liftId-subTm t =
  subTmEq {sigma = liftSubst idSubst} {tau = idSubst} liftId-apply t

liftId : (A : RawType) -> subTy (liftSubst idSubst) A ≡ subTy idSubst A
liftId = liftId-subTy

liftId2-apply : (n : ℕ)
  -> applySubst (liftSubst (liftSubst idSubst)) n ≡ applySubst idSubst n
liftId2-apply zero = refl
liftId2-apply (suc n) =
  liftSubst-apply-suc (liftSubst idSubst) n
  ∙ cong (renTm sucRen) (liftId-apply n)

liftId2-subTy : (A : RawType)
  -> subTy (liftSubst (liftSubst idSubst)) A ≡ subTy idSubst A
liftId2-subTy A =
  subTyEq {sigma = liftSubst (liftSubst idSubst)} {tau = idSubst} liftId2-apply A

liftId2-subTm : (t : RawTerm)
  -> subTm (liftSubst (liftSubst idSubst)) t ≡ subTm idSubst t
liftId2-subTm t =
  subTmEq {sigma = liftSubst (liftSubst idSubst)} {tau = idSubst} liftId2-apply t

liftId2 : (A : RawType) -> subTy (liftSubst (liftSubst idSubst)) A ≡ subTy idSubst A
liftId2 = liftId2-subTy

liftComp-apply : (sigma : Subst) (rho : Ren) (n : ℕ)
  -> applySubst (compSubRen (liftSubst sigma) (raiseRen rho)) n
       ≡ applySubst (liftSubst (compSubRen sigma rho)) n
liftComp-apply sigma rho zero = refl
liftComp-apply sigma rho (suc n) =
  applySubst-compSubRen (liftSubst sigma) (raiseRen rho) (suc n)
  ∙ cong (applySubst (liftSubst sigma)) (applyRen-raise-suc rho n)
  ∙ liftSubst-apply-suc sigma (applyRen rho n)
  ∙ cong (renTm sucRen) (sym (applySubst-compSubRen sigma rho n))
  ∙ sym (liftSubst-apply-suc (compSubRen sigma rho) n)

liftComp-subTy : (sigma : Subst) (rho : Ren) (A : RawType)
  -> subTy (compSubRen (liftSubst sigma) (raiseRen rho)) A
       ≡ subTy (liftSubst (compSubRen sigma rho)) A
liftComp-subTy sigma rho A =
  subTyEq
    {sigma = compSubRen (liftSubst sigma) (raiseRen rho)}
    {tau = liftSubst (compSubRen sigma rho)}
    (liftComp-apply sigma rho) A

liftComp-subTm : (sigma : Subst) (rho : Ren) (t : RawTerm)
  -> subTm (compSubRen (liftSubst sigma) (raiseRen rho)) t
       ≡ subTm (liftSubst (compSubRen sigma rho)) t
liftComp-subTm sigma rho t =
  subTmEq
    {sigma = compSubRen (liftSubst sigma) (raiseRen rho)}
    {tau = liftSubst (compSubRen sigma rho)}
    (liftComp-apply sigma rho) t

liftComp : (sigma : Subst) (rho : Ren) (A : RawType)
  -> subTy (compSubRen (liftSubst sigma) (raiseRen rho)) A
       ≡ subTy (liftSubst (compSubRen sigma rho)) A
liftComp = liftComp-subTy

liftComp2-apply : (sigma : Subst) (rho : Ren) (n : ℕ)
  -> applySubst (compSubRen (liftSubst (liftSubst sigma)) (raiseRen (raiseRen rho))) n
       ≡ applySubst (liftSubst (liftSubst (compSubRen sigma rho))) n
liftComp2-apply sigma rho n =
  liftComp-apply (liftSubst sigma) (raiseRen rho) n
  ∙ liftSubst-apply-cong
      {sigma = compSubRen (liftSubst sigma) (raiseRen rho)}
      {tau = liftSubst (compSubRen sigma rho)}
      (liftComp-apply sigma rho) n

liftComp2-subTy : (sigma : Subst) (rho : Ren) (A : RawType)
  -> subTy (compSubRen (liftSubst (liftSubst sigma)) (raiseRen (raiseRen rho))) A
       ≡ subTy (liftSubst (liftSubst (compSubRen sigma rho))) A
liftComp2-subTy sigma rho A =
  subTyEq
    {sigma = compSubRen (liftSubst (liftSubst sigma)) (raiseRen (raiseRen rho))}
    {tau = liftSubst (liftSubst (compSubRen sigma rho))}
    (liftComp2-apply sigma rho) A

liftComp2-subTm : (sigma : Subst) (rho : Ren) (t : RawTerm)
  -> subTm (compSubRen (liftSubst (liftSubst sigma)) (raiseRen (raiseRen rho))) t
       ≡ subTm (liftSubst (liftSubst (compSubRen sigma rho))) t
liftComp2-subTm sigma rho t =
  subTmEq
    {sigma = compSubRen (liftSubst (liftSubst sigma)) (raiseRen (raiseRen rho))}
    {tau = liftSubst (liftSubst (compSubRen sigma rho))}
    (liftComp2-apply sigma rho) t

liftComp2 : (sigma : Subst) (rho : Ren) (A : RawType)
  -> subTy (compSubRen (liftSubst (liftSubst sigma)) (raiseRen (raiseRen rho))) A
       ≡ subTy (liftSubst (liftSubst (compSubRen sigma rho))) A
liftComp2 = liftComp2-subTy

mutual
  subTyId : (A : RawType) -> subTy idSubst A ≡ A
  subTyId tyTop = refl
  subTyId (tySigma A B) =
    cong₂ tySigma (subTyId A) (liftId-subTy B ∙ subTyId B)

  subTmId : (t : RawTerm) -> subTm idSubst t ≡ t
  subTmId (var n) = refl
  subTmId tmStar = refl
  subTmId (tmPair a b) = cong₂ tmPair (subTmId a) (subTmId b)
  subTmId (tmElSigma d m) =
    cong₂ tmElSigma (subTmId d) (liftId2-subTm m ∙ subTmId m)

mutual
  subTyRen : (sigma : Subst) (rho : Ren) (A : RawType)
    -> subTy sigma (renTy rho A) ≡ subTy (compSubRen sigma rho) A
  subTyRen sigma rho tyTop = refl
  subTyRen sigma rho (tySigma A B) =
    cong₂ tySigma (subTyRen sigma rho A)
      (subTyRen (liftSubst sigma) (raiseRen rho) B
       ∙ liftComp-subTy sigma rho B)

  subTmRen : (sigma : Subst) (rho : Ren) (t : RawTerm)
    -> subTm sigma (renTm rho t) ≡ subTm (compSubRen sigma rho) t
  subTmRen sigma rho (var n) = sym (applySubst-compSubRen sigma rho n)
  subTmRen sigma rho tmStar = refl
  subTmRen sigma rho (tmPair a b) =
    cong₂ tmPair (subTmRen sigma rho a) (subTmRen sigma rho b)
  subTmRen sigma rho (tmElSigma d m) =
    cong₂ tmElSigma (subTmRen sigma rho d)
      (subTmRen (liftSubst (liftSubst sigma)) (raiseRen (raiseRen rho)) m
       ∙ liftComp2-subTm sigma rho m)

compSubRenIdAdd : (k : ℕ) -> compSubRen idSubst (addRen k) ≡ keepSubstBy k
compSubRenIdAdd zero = refl
compSubRenIdAdd (suc k) = refl

abstract
  renTyKeepSubstBy : (k : ℕ) (A : RawType) -> renTy (addRen k) A ≡ subTy (keepSubstBy k) A
  renTyKeepSubstBy k A =
    sym (subTyId (renTy (addRen k) A))
    ∙ subTyRen idSubst (addRen k) A
    ∙ cong (λ sigma -> subTy sigma A) (compSubRenIdAdd k)

  renTmKeepSubstBy : (k : ℕ) (t : RawTerm) -> renTm (addRen k) t ≡ subTm (keepSubstBy k) t
  renTmKeepSubstBy k t =
    sym (subTmId (renTm (addRen k) t))
    ∙ subTmRen idSubst (addRen k) t
    ∙ cong (λ sigma -> subTm sigma t) (compSubRenIdAdd k)

raiseCompRen-apply : (rho tau : Ren) (n : ℕ)
  -> applyRen (compRen (raiseRen rho) (raiseRen tau)) n
       ≡ applyRen (raiseRen (compRen rho tau)) n
raiseCompRen-apply rho tau zero = refl
raiseCompRen-apply rho tau (suc n) =
  applyRen-compRen (raiseRen rho) (raiseRen tau) (suc n)
  ∙ cong (applyRen (raiseRen rho)) (applyRen-raise-suc tau n)
  ∙ applyRen-raise-suc rho (applyRen tau n)
  ∙ cong suc (sym (applyRen-compRen rho tau n))
  ∙ sym (applyRen-raise-suc (compRen rho tau) n)

raiseCompRen : (rho tau : Ren) (A : RawType)
  -> renTy (compRen (raiseRen rho) (raiseRen tau)) A
       ≡ renTy (raiseRen (compRen rho tau)) A
raiseCompRen rho tau A =
  renTyEq
    {rho = compRen (raiseRen rho) (raiseRen tau)}
    {tau = raiseRen (compRen rho tau)}
    (raiseCompRen-apply rho tau) A

raiseCompRenTm : (rho tau : Ren) (t : RawTerm)
  -> renTm (compRen (raiseRen rho) (raiseRen tau)) t
       ≡ renTm (raiseRen (compRen rho tau)) t
raiseCompRenTm rho tau t =
  renTmEq
    {rho = compRen (raiseRen rho) (raiseRen tau)}
    {tau = raiseRen (compRen rho tau)}
    (raiseCompRen-apply rho tau) t

raiseCompRen2-apply : (rho tau : Ren) (n : ℕ)
  -> applyRen (compRen (raiseRen (raiseRen rho)) (raiseRen (raiseRen tau))) n
       ≡ applyRen (raiseRen (raiseRen (compRen rho tau))) n
raiseCompRen2-apply rho tau n =
  raiseCompRen-apply (raiseRen rho) (raiseRen tau) n
  ∙ raiseRen-apply-cong
      {rho = compRen (raiseRen rho) (raiseRen tau)}
      {tau = raiseRen (compRen rho tau)}
      (raiseCompRen-apply rho tau) n

raiseCompRen2 : (rho tau : Ren) (A : RawType)
  -> renTy (compRen (raiseRen (raiseRen rho)) (raiseRen (raiseRen tau))) A
       ≡ renTy (raiseRen (raiseRen (compRen rho tau))) A
raiseCompRen2 rho tau A =
  renTyEq
    {rho = compRen (raiseRen (raiseRen rho)) (raiseRen (raiseRen tau))}
    {tau = raiseRen (raiseRen (compRen rho tau))}
    (raiseCompRen2-apply rho tau) A

raiseCompRen2Tm : (rho tau : Ren) (t : RawTerm)
  -> renTm (compRen (raiseRen (raiseRen rho)) (raiseRen (raiseRen tau))) t
       ≡ renTm (raiseRen (raiseRen (compRen rho tau))) t
raiseCompRen2Tm rho tau t =
  renTmEq
    {rho = compRen (raiseRen (raiseRen rho)) (raiseRen (raiseRen tau))}
    {tau = raiseRen (raiseRen (compRen rho tau))}
    (raiseCompRen2-apply rho tau) t

shiftCompRen : (rho : Ren) -> compRen sucRen rho ≡ compRen (raiseRen rho) sucRen
shiftCompRen (shiftRen zero) = refl
shiftCompRen (shiftRen (suc k)) = refl
shiftCompRen (consRen m rho) = refl

dropLiftRenSub : (sigma : Subst) -> dropSub 1 (liftSubst sigma) ≡ renSub sucRen sigma
dropLiftRenSub sigma = refl

mutual
  renTyComp : (rho tau : Ren) (A : RawType)
    -> renTy rho (renTy tau A) ≡ renTy (compRen rho tau) A
  renTyComp rho tau tyTop = refl
  renTyComp rho tau (tySigma A B) =
    cong₂ tySigma (renTyComp rho tau A)
      (renTyComp (raiseRen rho) (raiseRen tau) B
       ∙ raiseCompRen rho tau B)

  renTmComp : (rho tau : Ren) (t : RawTerm)
    -> renTm rho (renTm tau t) ≡ renTm (compRen rho tau) t
  renTmComp rho tau (var n) = cong var (sym (applyRen-compRen rho tau n))
  renTmComp rho tau tmStar = refl
  renTmComp rho tau (tmPair a b) =
    cong₂ tmPair (renTmComp rho tau a) (renTmComp rho tau b)
  renTmComp rho tau (tmElSigma d m) =
    cong₂ tmElSigma (renTmComp rho tau d)
      (renTmComp (raiseRen (raiseRen rho)) (raiseRen (raiseRen tau)) m
       ∙ raiseCompRen2Tm rho tau m)

liftRenSub-apply : (rho : Ren) (sigma : Subst) (n : ℕ)
  -> applySubst (liftSubst (renSub rho sigma)) n
       ≡ applySubst (renSub (raiseRen rho) (liftSubst sigma)) n
liftRenSub-apply rho sigma zero = refl
liftRenSub-apply rho sigma (suc n) =
  liftSubst-apply-suc (renSub rho sigma) n
  ∙ cong (renTm sucRen) (applySubst-renSub rho sigma n)
  ∙ renTmComp sucRen rho (applySubst sigma n)
  ∙ cong (λ theta -> renTm theta (applySubst sigma n)) (shiftCompRen rho)
  ∙ sym (renTmComp (raiseRen rho) sucRen (applySubst sigma n))
  ∙ cong (renTm (raiseRen rho)) (sym (liftSubst-apply-suc sigma n))
  ∙ sym (applySubst-renSub (raiseRen rho) (liftSubst sigma) (suc n))

liftRenSub : (rho : Ren) (sigma : Subst) (A : RawType)
  -> subTy (liftSubst (renSub rho sigma)) A
       ≡ subTy (renSub (raiseRen rho) (liftSubst sigma)) A
liftRenSub rho sigma A =
  subTyEq
    {sigma = liftSubst (renSub rho sigma)}
    {tau = renSub (raiseRen rho) (liftSubst sigma)}
    (liftRenSub-apply rho sigma) A

liftRenSubTm : (rho : Ren) (sigma : Subst) (t : RawTerm)
  -> subTm (liftSubst (renSub rho sigma)) t
       ≡ subTm (renSub (raiseRen rho) (liftSubst sigma)) t
liftRenSubTm rho sigma t =
  subTmEq
    {sigma = liftSubst (renSub rho sigma)}
    {tau = renSub (raiseRen rho) (liftSubst sigma)}
    (liftRenSub-apply rho sigma) t

liftRenSub2-apply : (rho : Ren) (sigma : Subst) (n : ℕ)
  -> applySubst (liftSubst (liftSubst (renSub rho sigma))) n
       ≡ applySubst (renSub (raiseRen (raiseRen rho)) (liftSubst (liftSubst sigma))) n
liftRenSub2-apply rho sigma n =
  liftSubst-apply-cong
    {sigma = liftSubst (renSub rho sigma)}
    {tau = renSub (raiseRen rho) (liftSubst sigma)}
    (liftRenSub-apply rho sigma) n
  ∙ liftRenSub-apply (raiseRen rho) (liftSubst sigma) n

liftRenSub2 : (rho : Ren) (sigma : Subst) (A : RawType)
  -> subTy (liftSubst (liftSubst (renSub rho sigma))) A
       ≡ subTy (renSub (raiseRen (raiseRen rho)) (liftSubst (liftSubst sigma))) A
liftRenSub2 rho sigma A =
  subTyEq
    {sigma = liftSubst (liftSubst (renSub rho sigma))}
    {tau = renSub (raiseRen (raiseRen rho)) (liftSubst (liftSubst sigma))}
    (liftRenSub2-apply rho sigma) A

liftRenSub2Tm : (rho : Ren) (sigma : Subst) (t : RawTerm)
  -> subTm (liftSubst (liftSubst (renSub rho sigma))) t
       ≡ subTm (renSub (raiseRen (raiseRen rho)) (liftSubst (liftSubst sigma))) t
liftRenSub2Tm rho sigma t =
  subTmEq
    {sigma = liftSubst (liftSubst (renSub rho sigma))}
    {tau = renSub (raiseRen (raiseRen rho)) (liftSubst (liftSubst sigma))}
    (liftRenSub2-apply rho sigma) t

mutual
  renTySub : (rho : Ren) (sigma : Subst) (A : RawType)
    -> renTy rho (subTy sigma A) ≡ subTy (renSub rho sigma) A
  renTySub rho sigma tyTop = refl
  renTySub rho sigma (tySigma A B) =
    cong₂ tySigma (renTySub rho sigma A)
      (renTySub (raiseRen rho) (liftSubst sigma) B
       ∙ sym (liftRenSub rho sigma B))

  renTmSub : (rho : Ren) (sigma : Subst) (t : RawTerm)
    -> renTm rho (subTm sigma t) ≡ subTm (renSub rho sigma) t
  renTmSub rho sigma (var n) = sym (applySubst-renSub rho sigma n)
  renTmSub rho sigma tmStar = refl
  renTmSub rho sigma (tmPair a b) =
    cong₂ tmPair (renTmSub rho sigma a) (renTmSub rho sigma b)
  renTmSub rho sigma (tmElSigma d m) =
    cong₂ tmElSigma (renTmSub rho sigma d)
      (renTmSub (raiseRen (raiseRen rho)) (liftSubst (liftSubst sigma)) m
       ∙ sym (liftRenSub2Tm rho sigma m))

abstract
  wkTyLiftSubst : (sigma : Subst) (A : RawType)
    -> subTy (liftSubst sigma) (wkTyBy 1 A) ≡ wkTyBy 1 (subTy sigma A)
  wkTyLiftSubst sigma A =
    subTyRen (liftSubst sigma) sucRen A
    ∙ cong (λ theta -> subTy theta A) (dropLiftRenSub sigma)
    ∙ sym (renTySub sucRen sigma A)

  wkTmLiftSubst : (sigma : Subst) (t : RawTerm)
    -> subTm (liftSubst sigma) (wkTmBy 1 t) ≡ wkTmBy 1 (subTm sigma t)
  wkTmLiftSubst sigma t =
    subTmRen (liftSubst sigma) sucRen t
    ∙ cong (λ theta -> subTm theta t) (dropLiftRenSub sigma)
    ∙ sym (renTmSub sucRen sigma t)

abstract
  liftCompSub-apply : (sigma tau : Subst) (n : ℕ)
    -> applySubst (compSub (liftSubst sigma) (liftSubst tau)) n
         ≡ applySubst (liftSubst (compSub sigma tau)) n
  liftCompSub-apply sigma tau zero = refl
  liftCompSub-apply sigma tau (suc n) =
    applySubst-compSub (liftSubst sigma) (liftSubst tau) (suc n)
    ∙ cong (subTm (liftSubst sigma)) (liftSubst-apply-suc tau n)
    ∙ subTmRen (liftSubst sigma) sucRen (applySubst tau n)
    ∙ cong (λ theta -> subTm theta (applySubst tau n)) (dropLiftRenSub sigma)
    ∙ sym (renTmSub sucRen sigma (applySubst tau n))
    ∙ cong (renTm sucRen) (sym (applySubst-compSub sigma tau n))
    ∙ sym (liftSubst-apply-suc (compSub sigma tau) n)

  liftCompSub : (sigma tau : Subst) (A : RawType)
    -> subTy (compSub (liftSubst sigma) (liftSubst tau)) A
         ≡ subTy (liftSubst (compSub sigma tau)) A
  liftCompSub sigma tau A =
    subTyEq
      {sigma = compSub (liftSubst sigma) (liftSubst tau)}
      {tau = liftSubst (compSub sigma tau)}
      (liftCompSub-apply sigma tau) A

  liftCompSubTm : (sigma tau : Subst) (t : RawTerm)
    -> subTm (compSub (liftSubst sigma) (liftSubst tau)) t
         ≡ subTm (liftSubst (compSub sigma tau)) t
  liftCompSubTm sigma tau t =
    subTmEq
      {sigma = compSub (liftSubst sigma) (liftSubst tau)}
      {tau = liftSubst (compSub sigma tau)}
      (liftCompSub-apply sigma tau) t

  liftCompSub2-apply : (sigma tau : Subst) (n : ℕ)
    -> applySubst (compSub (liftSubst (liftSubst sigma)) (liftSubst (liftSubst tau))) n
         ≡ applySubst (liftSubst (liftSubst (compSub sigma tau))) n
  liftCompSub2-apply sigma tau n =
    liftCompSub-apply (liftSubst sigma) (liftSubst tau) n
    ∙ liftSubst-apply-cong
        {sigma = compSub (liftSubst sigma) (liftSubst tau)}
        {tau = liftSubst (compSub sigma tau)}
        (liftCompSub-apply sigma tau) n

  liftCompSub2 : (sigma tau : Subst) (A : RawType)
    -> subTy (compSub (liftSubst (liftSubst sigma)) (liftSubst (liftSubst tau))) A
         ≡ subTy (liftSubst (liftSubst (compSub sigma tau))) A
  liftCompSub2 sigma tau A =
    subTyEq
      {sigma = compSub (liftSubst (liftSubst sigma)) (liftSubst (liftSubst tau))}
      {tau = liftSubst (liftSubst (compSub sigma tau))}
      (liftCompSub2-apply sigma tau) A

  liftCompSub2Tm : (sigma tau : Subst) (t : RawTerm)
    -> subTm (compSub (liftSubst (liftSubst sigma)) (liftSubst (liftSubst tau))) t
         ≡ subTm (liftSubst (liftSubst (compSub sigma tau))) t
  liftCompSub2Tm sigma tau t =
    subTmEq
      {sigma = compSub (liftSubst (liftSubst sigma)) (liftSubst (liftSubst tau))}
      {tau = liftSubst (liftSubst (compSub sigma tau))}
      (liftCompSub2-apply sigma tau) t

  mutual
    subTyComp : (sigma tau : Subst) (A : RawType)
      -> subTy sigma (subTy tau A) ≡ subTy (compSub sigma tau) A
    subTyComp sigma tau tyTop = refl
    subTyComp sigma tau (tySigma A B) =
      cong₂ tySigma (subTyComp sigma tau A)
        (subTyComp (liftSubst sigma) (liftSubst tau) B
         ∙ liftCompSub sigma tau B)

    subTmComp : (sigma tau : Subst) (t : RawTerm)
      -> subTm sigma (subTm tau t) ≡ subTm (compSub sigma tau) t
    subTmComp sigma tau (var n) = sym (applySubst-compSub sigma tau n)
    subTmComp sigma tau tmStar = refl
    subTmComp sigma tau (tmPair a b) =
      cong₂ tmPair (subTmComp sigma tau a) (subTmComp sigma tau b)
    subTmComp sigma tau (tmElSigma d m) =
      cong₂ tmElSigma (subTmComp sigma tau d)
        (subTmComp (liftSubst (liftSubst sigma)) (liftSubst (liftSubst tau)) m
         ∙ liftCompSub2Tm sigma tau m)

sigmaCompSubSingle : (b c : RawTerm)
  -> compSub (consSubst c (consSubst b idSubst)) (replace0By 2 (tmPair (var (suc zero)) (var zero)))
       ≡ singleSubst (tmPair b c)
sigmaCompSubSingle b c = refl

sigmaBranchTyComp : (b c : RawTerm) (M : RawType)
  -> subTy (consSubst c (consSubst b idSubst)) (subTy (replace0By 2 (tmPair (var (suc zero)) (var zero))) M)
       ≡ subTy (singleSubst (tmPair b c)) M
sigmaBranchTyComp b c M =
  subTyComp (consSubst c (consSubst b idSubst)) (replace0By 2 (tmPair (var (suc zero)) (var zero))) M
  ∙ cong (λ theta -> subTy theta M) (sigmaCompSubSingle b c)

sigmaBranchTmComp : (b c m : RawTerm)
  -> subTm (consSubst c (consSubst b idSubst)) (subTm (replace0By 2 (tmPair (var (suc zero)) (var zero))) m)
       ≡ subTm (singleSubst (tmPair b c)) m
sigmaBranchTmComp b c m =
  subTmComp (consSubst c (consSubst b idSubst)) (replace0By 2 (tmPair (var (suc zero)) (var zero))) m
  ∙ cong (λ theta -> subTm theta m) (sigmaCompSubSingle b c)
