{-# OPTIONS --safe #-}

module TReg.Substitution where

open import Cubical.Foundations.Prelude
open import Cubical.Data.List.Base using (List ; [] ; _∷_ ; map)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_)

open import TReg.Syntax
open import TReg.Context

Ren : Type
Ren = ℕ -> ℕ

Subst : Type
Subst = ℕ -> RawTerm

raiseRen : Ren -> Ren
raiseRen rho zero = zero
raiseRen rho (suc n) = suc (rho n)

addRen : ℕ -> Ren
addRen k n = k + n

keepSubstBy : ℕ -> Subst
keepSubstBy k n = var (k + n)

dropSubstBy : ℕ -> Subst -> Subst
dropSubstBy k sigma n = sigma (k + n)

keep0RenBy : ℕ -> Ren
keep0RenBy k zero = zero
keep0RenBy k (suc n) = suc (k + n)

mutual
  renTy : Ren -> RawType -> RawType
  renTy rho tyTop = tyTop
  renTy rho (tySigma A B) = tySigma (renTy rho A) (renTy (raiseRen rho) B)
  renTy rho (tyEq A a b) = tyEq (renTy rho A) (renTm rho a) (renTm rho b)
  renTy rho (tyQtr A) = tyQtr (renTy rho A)

  renTm : Ren -> RawTerm -> RawTerm
  renTm rho (var n) = var (rho n)
  renTm rho tmStar = tmStar
  renTm rho (tmPair a b) = tmPair (renTm rho a) (renTm rho b)
  renTm rho (tmElSigma d m) = tmElSigma (renTm rho d) (renTm (raiseRen (raiseRen rho)) m)
  renTm rho tmR = tmR
  renTm rho (tmEq A a) = tmEq (renTy rho A) (renTm rho a)
  renTm rho (tmClass a) = tmClass (renTm rho a)
  renTm rho (tmElQtr l p) = tmElQtr (renTm (raiseRen rho) l) (renTm rho p)

wkTyBy : ℕ -> RawType -> RawType
wkTyBy k = renTy (addRen k)

wkTmBy : ℕ -> RawTerm -> RawTerm
wkTmBy k = renTm (addRen k)

idSubst : Subst
idSubst n = var n

consSubst : RawTerm -> Subst -> Subst
consSubst t sigma zero = t
consSubst t sigma (suc n) = sigma n

liftSubst : Subst -> Subst
liftSubst sigma zero = var zero
liftSubst sigma (suc n) = renTm suc (sigma n)

replace0By : ℕ -> RawTerm -> Subst
replace0By k t zero = t
replace0By k t (suc n) = var (k + n)

singleSubst : RawTerm -> Subst
singleSubst = replace0By 0

mutual
  subTy : Subst -> RawType -> RawType
  subTy sigma tyTop = tyTop
  subTy sigma (tySigma A B) = tySigma (subTy sigma A) (subTy (liftSubst sigma) B)
  subTy sigma (tyEq A a b) = tyEq (subTy sigma A) (subTm sigma a) (subTm sigma b)
  subTy sigma (tyQtr A) = tyQtr (subTy sigma A)

  subTm : Subst -> RawTerm -> RawTerm
  subTm sigma (var n) = sigma n
  subTm sigma tmStar = tmStar
  subTm sigma (tmPair a b) = tmPair (subTm sigma a) (subTm sigma b)
  subTm sigma (tmElSigma d m) = tmElSigma (subTm sigma d) (subTm (liftSubst (liftSubst sigma)) m)
  subTm sigma tmR = tmR
  subTm sigma (tmEq A a) = tmEq (subTy sigma A) (subTm sigma a)
  subTm sigma (tmClass a) = tmClass (subTm sigma a)
  subTm sigma (tmElQtr l p) = tmElQtr (subTm (liftSubst sigma) l) (subTm sigma p)

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

liftId : liftSubst idSubst ≡ idSubst
liftId = funExt λ where
  zero -> refl
  (suc n) -> refl

liftId2 : liftSubst (liftSubst idSubst) ≡ idSubst
liftId2 = funExt λ where
  zero -> refl
  (suc zero) -> refl
  (suc (suc n)) -> refl

liftComp : (sigma : Subst) (rho : Ren)
  -> (λ n -> liftSubst sigma (raiseRen rho n)) ≡ liftSubst (λ n -> sigma (rho n))
liftComp sigma rho = funExt λ where
  zero -> refl
  (suc n) -> refl

liftComp2 : (sigma : Subst) (rho : Ren)
  -> (λ n -> liftSubst (liftSubst sigma) (raiseRen (raiseRen rho) n))
       ≡ liftSubst (liftSubst (λ n -> sigma (rho n)))
liftComp2 sigma rho = funExt λ where
  zero -> refl
  (suc zero) -> refl
  (suc (suc n)) -> refl

mutual
  subTyId : (A : RawType) -> subTy idSubst A ≡ A
  subTyId tyTop = refl
  subTyId (tySigma A B) =
    cong₂ tySigma (subTyId A) (cong (λ sigma -> subTy sigma B) liftId ∙ subTyId B)
  subTyId (tyEq A a b) = cong₃ tyEq (subTyId A) (subTmId a) (subTmId b)
  subTyId (tyQtr A) = cong tyQtr (subTyId A)

  subTmId : (t : RawTerm) -> subTm idSubst t ≡ t
  subTmId (var n) = refl
  subTmId tmStar = refl
  subTmId (tmPair a b) = cong₂ tmPair (subTmId a) (subTmId b)
  subTmId (tmElSigma d m) =
    cong₂ tmElSigma (subTmId d) (cong (λ sigma -> subTm sigma m) liftId2 ∙ subTmId m)
  subTmId tmR = refl
  subTmId (tmEq A a) = cong₂ tmEq (subTyId A) (subTmId a)
  subTmId (tmClass a) = cong tmClass (subTmId a)
  subTmId (tmElQtr l p) =
    cong₂ tmElQtr (cong (λ sigma -> subTm sigma l) liftId ∙ subTmId l) (subTmId p)

mutual
  subTyRen : (sigma : Subst) (rho : Ren) (A : RawType)
    -> subTy sigma (renTy rho A) ≡ subTy (λ n -> sigma (rho n)) A
  subTyRen sigma rho tyTop = refl
  subTyRen sigma rho (tySigma A B) =
    cong₂ tySigma (subTyRen sigma rho A)
      (subTyRen (liftSubst sigma) (raiseRen rho) B
       ∙ cong (λ theta -> subTy theta B) (liftComp sigma rho))
  subTyRen sigma rho (tyEq A a b) =
    cong₃ tyEq (subTyRen sigma rho A) (subTmRen sigma rho a) (subTmRen sigma rho b)
  subTyRen sigma rho (tyQtr A) = cong tyQtr (subTyRen sigma rho A)

  subTmRen : (sigma : Subst) (rho : Ren) (t : RawTerm)
    -> subTm sigma (renTm rho t) ≡ subTm (λ n -> sigma (rho n)) t
  subTmRen sigma rho (var n) = refl
  subTmRen sigma rho tmStar = refl
  subTmRen sigma rho (tmPair a b) =
    cong₂ tmPair (subTmRen sigma rho a) (subTmRen sigma rho b)
  subTmRen sigma rho (tmElSigma d m) =
    cong₂ tmElSigma (subTmRen sigma rho d)
      (subTmRen (liftSubst (liftSubst sigma)) (raiseRen (raiseRen rho)) m
       ∙ cong (λ theta -> subTm theta m) (liftComp2 sigma rho))
  subTmRen sigma rho tmR = refl
  subTmRen sigma rho (tmEq A a) =
    cong₂ tmEq (subTyRen sigma rho A) (subTmRen sigma rho a)
  subTmRen sigma rho (tmClass a) = cong tmClass (subTmRen sigma rho a)
  subTmRen sigma rho (tmElQtr l p) =
    cong₂ tmElQtr
      (subTmRen (liftSubst sigma) (raiseRen rho) l
       ∙ cong (λ theta -> subTm theta l) (liftComp sigma rho))
      (subTmRen sigma rho p)

renTyKeepSubstBy : (k : ℕ) (A : RawType) -> renTy (addRen k) A ≡ subTy (keepSubstBy k) A
renTyKeepSubstBy k A =
  sym (subTyId (renTy (addRen k) A)) ∙ subTyRen idSubst (addRen k) A

renTmKeepSubstBy : (k : ℕ) (t : RawTerm) -> renTm (addRen k) t ≡ subTm (keepSubstBy k) t
renTmKeepSubstBy k t =
  sym (subTmId (renTm (addRen k) t)) ∙ subTmRen idSubst (addRen k) t

compRen : Ren -> Ren -> Ren
compRen rho tau n = rho (tau n)

raiseCompRen : (rho tau : Ren)
  -> compRen (raiseRen rho) (raiseRen tau) ≡ raiseRen (compRen rho tau)
raiseCompRen rho tau = funExt λ where
  zero -> refl
  (suc n) -> refl

raiseCompRen2 : (rho tau : Ren)
  -> compRen (raiseRen (raiseRen rho)) (raiseRen (raiseRen tau))
       ≡ raiseRen (raiseRen (compRen rho tau))
raiseCompRen2 rho tau =
  raiseCompRen (raiseRen rho) (raiseRen tau) ∙ cong raiseRen (raiseCompRen rho tau)

shiftCompRen : (rho : Ren) -> compRen suc rho ≡ compRen (raiseRen rho) suc
shiftCompRen rho = funExt λ where
  zero -> refl
  (suc n) -> refl

renSub : Ren -> Subst -> Subst
renSub rho sigma n = renTm rho (sigma n)

dropLiftRenSub : (sigma : Subst)
  -> (λ n -> liftSubst sigma (suc n)) ≡ renSub suc sigma
dropLiftRenSub sigma = funExt λ where
  zero -> refl
  (suc n) -> refl

mutual
  renTyComp : (rho tau : Ren) (A : RawType)
    -> renTy rho (renTy tau A) ≡ renTy (compRen rho tau) A
  renTyComp rho tau tyTop = refl
  renTyComp rho tau (tySigma A B) =
    cong₂ tySigma (renTyComp rho tau A)
      (renTyComp (raiseRen rho) (raiseRen tau) B
       ∙ cong (λ theta -> renTy theta B) (raiseCompRen rho tau))
  renTyComp rho tau (tyEq A a b) =
    cong₃ tyEq (renTyComp rho tau A) (renTmComp rho tau a) (renTmComp rho tau b)
  renTyComp rho tau (tyQtr A) = cong tyQtr (renTyComp rho tau A)

  renTmComp : (rho tau : Ren) (t : RawTerm)
    -> renTm rho (renTm tau t) ≡ renTm (compRen rho tau) t
  renTmComp rho tau (var n) = refl
  renTmComp rho tau tmStar = refl
  renTmComp rho tau (tmPair a b) =
    cong₂ tmPair (renTmComp rho tau a) (renTmComp rho tau b)
  renTmComp rho tau (tmElSigma d m) =
    cong₂ tmElSigma (renTmComp rho tau d)
      (renTmComp (raiseRen (raiseRen rho)) (raiseRen (raiseRen tau)) m
       ∙ cong (λ theta -> renTm theta m) (raiseCompRen2 rho tau))
  renTmComp rho tau tmR = refl
  renTmComp rho tau (tmEq A a) =
    cong₂ tmEq (renTyComp rho tau A) (renTmComp rho tau a)
  renTmComp rho tau (tmClass a) = cong tmClass (renTmComp rho tau a)
  renTmComp rho tau (tmElQtr l p) =
    cong₂ tmElQtr
      (renTmComp (raiseRen rho) (raiseRen tau) l
       ∙ cong (λ theta -> renTm theta l) (raiseCompRen rho tau))
      (renTmComp rho tau p)

liftRenSub : (rho : Ren) (sigma : Subst)
  -> liftSubst (renSub rho sigma) ≡ renSub (raiseRen rho) (liftSubst sigma)
liftRenSub rho sigma = funExt λ where
  zero -> refl
  (suc n) ->
    renTmComp suc rho (sigma n)
    ∙ cong (λ theta -> renTm theta (sigma n)) (shiftCompRen rho)
    ∙ sym (renTmComp (raiseRen rho) suc (sigma n))

liftRenSub2 : (rho : Ren) (sigma : Subst)
  -> liftSubst (liftSubst (renSub rho sigma))
       ≡ renSub (raiseRen (raiseRen rho)) (liftSubst (liftSubst sigma))
liftRenSub2 rho sigma =
  cong liftSubst (liftRenSub rho sigma) ∙ liftRenSub (raiseRen rho) (liftSubst sigma)

mutual
  renTySub : (rho : Ren) (sigma : Subst) (A : RawType)
    -> renTy rho (subTy sigma A) ≡ subTy (renSub rho sigma) A
  renTySub rho sigma tyTop = refl
  renTySub rho sigma (tySigma A B) =
    cong₂ tySigma (renTySub rho sigma A)
      (renTySub (raiseRen rho) (liftSubst sigma) B
       ∙ cong (λ theta -> subTy theta B) (sym (liftRenSub rho sigma)))
  renTySub rho sigma (tyEq A a b) =
    cong₃ tyEq (renTySub rho sigma A) (renTmSub rho sigma a) (renTmSub rho sigma b)
  renTySub rho sigma (tyQtr A) = cong tyQtr (renTySub rho sigma A)

  renTmSub : (rho : Ren) (sigma : Subst) (t : RawTerm)
    -> renTm rho (subTm sigma t) ≡ subTm (renSub rho sigma) t
  renTmSub rho sigma (var n) = refl
  renTmSub rho sigma tmStar = refl
  renTmSub rho sigma (tmPair a b) =
    cong₂ tmPair (renTmSub rho sigma a) (renTmSub rho sigma b)
  renTmSub rho sigma (tmElSigma d m) =
    cong₂ tmElSigma (renTmSub rho sigma d)
      (renTmSub (raiseRen (raiseRen rho)) (liftSubst (liftSubst sigma)) m
       ∙ cong (λ theta -> subTm theta m) (sym (liftRenSub2 rho sigma)))
  renTmSub rho sigma tmR = refl
  renTmSub rho sigma (tmEq A a) =
    cong₂ tmEq (renTySub rho sigma A) (renTmSub rho sigma a)
  renTmSub rho sigma (tmClass a) = cong tmClass (renTmSub rho sigma a)
  renTmSub rho sigma (tmElQtr l p) =
    cong₂ tmElQtr
      (renTmSub (raiseRen rho) (liftSubst sigma) l
       ∙ cong (λ theta -> subTm theta l) (sym (liftRenSub rho sigma)))
      (renTmSub rho sigma p)

wkTyLiftSubst : (sigma : Subst) (A : RawType)
  -> subTy (liftSubst sigma) (wkTyBy 1 A) ≡ wkTyBy 1 (subTy sigma A)
wkTyLiftSubst sigma A =
  subTyRen (liftSubst sigma) suc A
  ∙ cong (λ theta -> subTy theta A) (dropLiftRenSub sigma)
  ∙ sym (renTySub suc sigma A)

wkTmLiftSubst : (sigma : Subst) (t : RawTerm)
  -> subTm (liftSubst sigma) (wkTmBy 1 t) ≡ wkTmBy 1 (subTm sigma t)
wkTmLiftSubst sigma t =
  subTmRen (liftSubst sigma) suc t
  ∙ cong (λ theta -> subTm theta t) (dropLiftRenSub sigma)
  ∙ sym (renTmSub suc sigma t)

compSub : Subst -> Subst -> Subst
compSub sigma tau n = subTm sigma (tau n)

liftCompSub : (sigma tau : Subst)
  -> compSub (liftSubst sigma) (liftSubst tau) ≡ liftSubst (compSub sigma tau)
liftCompSub sigma tau = funExt λ where
  zero -> refl
  (suc n) ->
    subTmRen (liftSubst sigma) suc (tau n)
    ∙ cong (λ theta -> subTm theta (tau n)) (dropLiftRenSub sigma)
    ∙ sym (renTmSub suc sigma (tau n))

liftCompSub2 : (sigma tau : Subst)
  -> compSub (liftSubst (liftSubst sigma)) (liftSubst (liftSubst tau))
       ≡ liftSubst (liftSubst (compSub sigma tau))
liftCompSub2 sigma tau =
  liftCompSub (liftSubst sigma) (liftSubst tau) ∙ cong liftSubst (liftCompSub sigma tau)

mutual
  subTyComp : (sigma tau : Subst) (A : RawType)
    -> subTy sigma (subTy tau A) ≡ subTy (compSub sigma tau) A
  subTyComp sigma tau tyTop = refl
  subTyComp sigma tau (tySigma A B) =
    cong₂ tySigma (subTyComp sigma tau A)
      (subTyComp (liftSubst sigma) (liftSubst tau) B
       ∙ cong (λ theta -> subTy theta B) (liftCompSub sigma tau))
  subTyComp sigma tau (tyEq A a b) =
    cong₃ tyEq (subTyComp sigma tau A) (subTmComp sigma tau a) (subTmComp sigma tau b)
  subTyComp sigma tau (tyQtr A) = cong tyQtr (subTyComp sigma tau A)

  subTmComp : (sigma tau : Subst) (t : RawTerm)
    -> subTm sigma (subTm tau t) ≡ subTm (compSub sigma tau) t
  subTmComp sigma tau (var n) = refl
  subTmComp sigma tau tmStar = refl
  subTmComp sigma tau (tmPair a b) =
    cong₂ tmPair (subTmComp sigma tau a) (subTmComp sigma tau b)
  subTmComp sigma tau (tmElSigma d m) =
    cong₂ tmElSigma (subTmComp sigma tau d)
      (subTmComp (liftSubst (liftSubst sigma)) (liftSubst (liftSubst tau)) m
       ∙ cong (λ theta -> subTm theta m) (liftCompSub2 sigma tau))
  subTmComp sigma tau tmR = refl
  subTmComp sigma tau (tmEq A a) =
    cong₂ tmEq (subTyComp sigma tau A) (subTmComp sigma tau a)
  subTmComp sigma tau (tmClass a) = cong tmClass (subTmComp sigma tau a)
  subTmComp sigma tau (tmElQtr l p) =
    cong₂ tmElQtr
      (subTmComp (liftSubst sigma) (liftSubst tau) l
       ∙ cong (λ theta -> subTm theta l) (liftCompSub sigma tau))
      (subTmComp sigma tau p)

sigmaCompSubSingle : (b c : RawTerm)
  -> compSub (consSubst c (consSubst b idSubst)) (replace0By 2 (tmPair (var (suc zero)) (var zero)))
       ≡ singleSubst (tmPair b c)
sigmaCompSubSingle b c = funExt λ where
  zero -> refl
  (suc n) -> refl

qtrCompSubSingle : (a : RawTerm)
  -> compSub (consSubst a idSubst) (replace0By 1 (tmClass (var zero)))
       ≡ singleSubst (tmClass a)
qtrCompSubSingle a = funExt λ where
  zero -> refl
  (suc n) -> refl

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

qtrBranchTyComp : (a : RawTerm) (L : RawType)
  -> subTy (consSubst a idSubst) (subTy (replace0By 1 (tmClass (var zero))) L)
       ≡ subTy (singleSubst (tmClass a)) L
qtrBranchTyComp a L =
  subTyComp (consSubst a idSubst) (replace0By 1 (tmClass (var zero))) L
  ∙ cong (λ theta -> subTy theta L) (qtrCompSubSingle a)

qtrBranchTmComp : (a l : RawTerm)
  -> subTm (consSubst a idSubst) (subTm (replace0By 1 (tmClass (var zero))) l)
       ≡ subTm (singleSubst (tmClass a)) l
qtrBranchTmComp a l =
  subTmComp (consSubst a idSubst) (replace0By 1 (tmClass (var zero))) l
  ∙ cong (λ theta -> subTm theta l) (qtrCompSubSingle a)

qtrCohSubComp : (a b : RawTerm)
  -> compSub (consSubst b (consSubst a idSubst)) (replace0By 2 (tmClass (var (suc zero))))
       ≡ singleSubst (tmClass a)
qtrCohSubComp a b = funExt λ where
  zero -> refl
  (suc n) -> refl

qtrCohTyComp : (a b : RawTerm) (L : RawType)
  -> subTy (consSubst b (consSubst a idSubst)) (subTy (replace0By 2 (tmClass (var (suc zero)))) L)
       ≡ subTy (singleSubst (tmClass a)) L
qtrCohTyComp a b L =
  subTyComp (consSubst b (consSubst a idSubst)) (replace0By 2 (tmClass (var (suc zero)))) L
  ∙ cong (λ theta -> subTy theta L) (qtrCohSubComp a b)

qtrCohLeftTmComp : (a b l : RawTerm)
  -> subTm (consSubst b (consSubst a idSubst)) (wkTmBy 1 l)
       ≡ subTm (consSubst a idSubst) l
qtrCohLeftTmComp a b l =
  subTmRen (consSubst b (consSubst a idSubst)) (addRen 1) l
  ∙ cong (λ theta -> subTm theta l) (funExt λ where
      zero -> refl
      (suc n) -> refl)

qtrCohRightTmComp : (a b l : RawTerm)
  -> subTm (consSubst b (consSubst a idSubst)) (renTm (keep0RenBy 1) l)
       ≡ subTm (consSubst b idSubst) l
qtrCohRightTmComp a b l =
  subTmRen (consSubst b (consSubst a idSubst)) (keep0RenBy 1) l
  ∙ cong (λ theta -> subTm theta l) (funExt λ where
      zero -> refl
      (suc n) -> refl)
