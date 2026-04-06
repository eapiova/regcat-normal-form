{-# OPTIONS --safe #-}

module TReg.CompTheorem where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Empty.Base as Empty using (⊥ ; rec)
open import Cubical.Data.Sigma using (Σ ; Σ-syntax ; _×_ ; _,_ ; fst ; snd)
open import Cubical.Data.List.Base using ([] ; _∷_ ; _++_ ; length)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Nat.Order using (_<_ ; <-wellfounded)
open import Cubical.Data.Nat.Properties using (snotz)
open import Cubical.Data.Unit.Base using (Unit ; tt)
open import Cubical.Induction.WellFounded using (Acc ; acc)

open import TReg.Syntax
open import TReg.Context
open import TReg.Substitution
open import TReg.Measure
open import TReg.Evaluation
open import TReg.Derivability
open import TReg.Computability
open import TReg.Inversion
open import TReg.Presupposition
open import TReg.Structural
open import TReg.TopComp
open import TReg.EqComp
open import TReg.MainTheorem

nonemptyNeNil : {A : RawType} {gamma : Ctx} -> (A ∷ gamma ≡ []) -> ⊥
nonemptyNeNil {gamma = gamma} p = snotz (cong length p)

case_of_ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} -> A -> (A -> B) -> B
case x of f = f x

compReflTy : {A : RawType}
  -> Computable (isType [] A)
  -> Computable (typeEq [] A A)
compReflTy = compReflTyClosed

compReflTm : {t : RawTerm} {A : RawType}
  -> Computable (hasTy [] t A)
  -> Computable (termEq [] t t A)
compReflTm = compReflTmClosed

liftFitsNR : {theta gamma : Ctx} {A : RawType} {sigma : Subst}
  -> FitsSubst theta gamma sigma
  -> Derivable (isType theta (subTy sigma A))
  -> FitsSubst (subTy sigma A ∷ theta) (A ∷ gamma)
       (consSubst (var zero) (compSub (keepSubstBy 1) sigma))
liftFitsNR {theta = theta} {gamma = gamma} {A = A} {sigma = sigma} fits dAσ =
  fitsCons tail headVar
  where
  wfAσ : CtxWF (subTy sigma A ∷ theta)
  wfAσ = wfCons (fitsSubstCtxWF fits) dAσ

  tail : FitsSubst (subTy sigma A ∷ theta) gamma (compSub (keepSubstBy 1) sigma)
  tail =
    composeFits
      (fitsKeep {delta = subTy sigma A ∷ []} {gamma = theta} wfAσ)
      fits

  headVar0 : Derivable
    (hasTy (subTy sigma A ∷ theta) (var zero) (wkTyBy 1 (subTy sigma A)))
  headVar0 = varStar {gamma = theta} {delta = []} {A = subTy sigma A} wfAσ dAσ

  headVar : Derivable
    (hasTy (subTy sigma A ∷ theta) (var zero) (subTy (compSub (keepSubstBy 1) sigma) A))
  headVar =
    subst
      (λ T -> Derivable (hasTy (subTy sigma A ∷ theta) (var zero) T))
      (renTyKeepSubstBy 1 (subTy sigma A) ∙ subTyComp (keepSubstBy 1) sigma A)
      headVar0

liftFitsOneNR : {gamma : Ctx} {A : RawType} {sigma : Subst}
  -> FitsSubst [] gamma sigma
  -> Derivable (isType [] (subTy sigma A))
  -> FitsSubst (subTy sigma A ∷ []) (A ∷ gamma)
       (consSubst (var zero) (compSub (keepSubstBy 1) sigma))
liftFitsOneNR = liftFitsNR

liftFitsEqNR : {theta gamma : Ctx} {A : RawType} {sigma tau : Subst}
  -> FitsEqSubst theta gamma sigma tau
  -> Derivable (isType theta (subTy sigma A))
  -> FitsEqSubst (subTy sigma A ∷ theta) (A ∷ gamma)
       (consSubst (var zero) (compSub (keepSubstBy 1) sigma))
       (consSubst (var zero) (compSub (keepSubstBy 1) tau))
liftFitsEqNR {theta = theta} {gamma = gamma} {A = A} {sigma = sigma} {tau = tau} fitsEq dAσ =
  fitsEqCons tail (reflTm headVar)
  where
  wfAσ : CtxWF (subTy sigma A ∷ theta)
  wfAσ = wfCons (fitsEqSubstCtxWF fitsEq) dAσ

  tail : FitsEqSubst (subTy sigma A ∷ theta) gamma
    (compSub (keepSubstBy 1) sigma)
    (compSub (keepSubstBy 1) tau)
  tail =
    composeFitsEq
      (fitsKeep {delta = subTy sigma A ∷ []} {gamma = theta} wfAσ)
      fitsEq

  headVar0 : Derivable
    (hasTy (subTy sigma A ∷ theta) (var zero) (wkTyBy 1 (subTy sigma A)))
  headVar0 = varStar {gamma = theta} {delta = []} {A = subTy sigma A} wfAσ dAσ

  headVar : Derivable
    (hasTy (subTy sigma A ∷ theta) (var zero) (subTy (compSub (keepSubstBy 1) sigma) A))
  headVar =
    subst
      (λ T -> Derivable (hasTy (subTy sigma A ∷ theta) (var zero) T))
      (renTyKeepSubstBy 1 (subTy sigma A) ∙ subTyComp (keepSubstBy 1) sigma A)
      headVar0

liftFitsEqOneNR : {gamma : Ctx} {A : RawType} {sigma tau : Subst}
  -> FitsEqSubst [] gamma sigma tau
  -> Derivable (isType [] (subTy sigma A))
  -> FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma)
       (consSubst (var zero) (compSub (keepSubstBy 1) sigma))
       (consSubst (var zero) (compSub (keepSubstBy 1) tau))
liftFitsEqOneNR = liftFitsEqNR

liftSubstCompKeepNR : (sigma : Subst)
  -> consSubst (var zero) (compSub (keepSubstBy 1) sigma) ≡ liftSubst sigma
liftSubstCompKeepNR sigma = funExt λ where
  zero -> refl
  (suc n) -> sym (renTmKeepSubstBy 1 (sigma n))

composeOneBinderNR : {gamma : Ctx} {A : RawType} {sigma tau : Subst}
  -> FitsSubst [] gamma sigma
  -> Derivable (isType [] (subTy sigma A))
  -> FitsSubst [] (subTy sigma A ∷ []) tau
  -> FitsSubst [] (A ∷ gamma) (compSub tau (liftSubst sigma))
composeOneBinderNR {gamma = gamma} {A = A} {sigma = sigma} {tau = tau} fits dAσ fits2 =
  subst
    (λ rho -> FitsSubst [] (A ∷ gamma) rho)
    (cong (compSub tau) (liftSubstCompKeepNR sigma))
    (composeFits fits2 (liftFitsOneNR fits dAσ))

composeOneBinderEqNR : {gamma : Ctx} {A : RawType} {sigma tau₁ tau₂ : Subst}
  -> FitsSubst [] gamma sigma
  -> Derivable (isType [] (subTy sigma A))
  -> FitsEqSubst [] (subTy sigma A ∷ []) tau₁ tau₂
  -> FitsEqSubst [] (A ∷ gamma) (compSub tau₁ (liftSubst sigma)) (compSub tau₂ (liftSubst sigma))
composeOneBinderEqNR {gamma = gamma} {A = A} {sigma = sigma} {tau₁ = tau₁} {tau₂ = tau₂} fits dAσ fitsEq =
  subst
    (λ rho -> FitsEqSubst [] (A ∷ gamma) rho (compSub tau₂ (liftSubst sigma)))
    (cong (compSub tau₁) (liftSubstCompKeepNR sigma))
    (subst
      (λ rho ->
        FitsEqSubst [] (A ∷ gamma)
          (compSub tau₁ (consSubst (var zero) (compSub (keepSubstBy 1) sigma)))
          rho)
      (cong (compSub tau₂) (liftSubstCompKeepNR sigma))
      (composeEqFits fitsEq (liftFitsOneNR fits dAσ)))

mutual
  substDerivTyComp : {gamma : Ctx} {A : RawType} {sigma : Subst}
    -> Derivable (isType gamma A)
    -> FitsSubst [] gamma sigma
    -> Computable (isType [] (subTy sigma A))

  substDerivTmComp : {gamma : Ctx} {t : RawTerm} {A : RawType} {sigma : Subst}
    -> Derivable (hasTy gamma t A)
    -> FitsSubst [] gamma sigma
    -> Computable (hasTy [] (subTm sigma t) (subTy sigma A))

  substDerivTmEqComp : {gamma : Ctx} {t u : RawTerm} {A : RawType} {sigma : Subst}
    -> Derivable (termEq gamma t u A)
    -> FitsSubst [] gamma sigma
    -> Computable (termEq [] (subTm sigma t) (subTm sigma u) (subTy sigma A))

  eqSubDerivTyComp : {gamma : Ctx} {A : RawType} {sigma tau : Subst}
    -> Derivable (isType gamma A)
    -> FitsEqSubst [] gamma sigma tau
    -> Computable (typeEq [] (subTy sigma A) (subTy tau A))

  eqSubDerivTmComp : {gamma : Ctx} {t : RawTerm} {A : RawType} {sigma tau : Subst}
    -> Derivable (hasTy gamma t A)
    -> FitsEqSubst [] gamma sigma tau
    -> Computable (termEq [] (subTm sigma t) (subTm tau t) (subTy sigma A))

  eqSubDerivTmEqComp : {gamma : Ctx} {t u : RawTerm} {A : RawType} {sigma tau : Subst}
    -> Derivable (termEq gamma t u A)
    -> FitsEqSubst [] gamma sigma tau
    -> Computable (termEq [] (subTm sigma t) (subTm tau u) (subTy sigma A))

  substTyClosed : {delta : Ctx} {A : RawType} {sigma : Subst}
    -> Derivable (isType delta A)
    -> FitsSubst [] delta sigma
    -> Computable (isType [] (subTy sigma A))

  eqSubTyClosed : {delta : Ctx} {A : RawType} {sigma tau : Subst}
    -> Derivable (isType delta A)
    -> FitsEqSubst [] delta sigma tau
    -> Computable (typeEq [] (subTy sigma A) (subTy tau A))

  openHypTy1 : {gamma : Ctx} {A B : RawType} {sigma : Subst}
    -> FitsSubst [] gamma sigma
    -> Derivable (isType [] (subTy sigma A))
    -> Derivable (isType (A ∷ gamma) B)
    -> HypComputable (isType (subTy sigma A ∷ []) (subTy (liftSubst sigma) B))
  openHypTy1 {A = A} {B = B} {sigma = sigma} fits dAσ dB =
    subst
      (λ T -> HypComputable (isType (subTy sigma A ∷ []) T))
      (cong (λ rho -> subTy rho B) (liftSubstCompKeep sigma))
      (hypTyOpen
        nonemptyNeNil
        (substTyRule dB (liftFitsOne fits dAσ))
        (λ tau fits2 _ ->
          subst
            (λ T -> Computable (isType [] T))
            (sym
              (cong (λ rho -> subTy tau (subTy rho B)) (liftSubstCompKeep sigma)
                ∙ subTyComp tau (liftSubst sigma) B))
            (substDerivTyComp
              dB
              (composeOneBinder fits dAσ fits2)))
        (λ tau₁ tau₂ fitsEq2 _ ->
          subst
            (λ J -> Computable J)
            (sym
              (cong₂ (typeEq [])
                (cong (λ rho -> subTy tau₁ (subTy rho B)) (liftSubstCompKeep sigma)
                  ∙ subTyComp tau₁ (liftSubst sigma) B)
                (cong (λ rho -> subTy tau₂ (subTy rho B)) (liftSubstCompKeep sigma)
                  ∙ subTyComp tau₂ (liftSubst sigma) B)))
            (eqSubDerivTyComp
              dB
              (composeOneBinderEq fits dAσ fitsEq2))))

  openHypTy2 : {gamma : Ctx} {A B T : RawType} {sigma : Subst}
    -> FitsSubst [] gamma sigma
    -> Derivable (isType [] (subTy sigma A))
    -> Derivable (isType (subTy sigma A ∷ []) (subTy (liftSubst sigma) B))
    -> Derivable (isType (B ∷ A ∷ gamma) T)
    -> HypComputable
         (isType (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ [])
           (subTy (liftSubst (liftSubst sigma)) T))
  openHypTy2 {gamma = gamma} {A = A} {B = B} {T = T} {sigma = sigma}
    fits dAσ dBσ dT =
    let
      lifted1 : FitsSubst (subTy sigma A ∷ []) (A ∷ gamma) (liftSubst sigma)
      lifted1 =
        subst
          (λ rho -> FitsSubst (subTy sigma A ∷ []) (A ∷ gamma) rho)
          (liftSubstCompKeep sigma)
          (liftFitsOne fits dAσ)
    in
    subst
      (λ T' -> HypComputable (isType (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) T'))
      (cong (λ rho -> subTy rho T) (liftSubstCompKeep (liftSubst sigma)))
      (hypTyOpen
        nonemptyNeNil
        (substTyRule dT (liftFits lifted1 dBσ))
        (λ tau fits2 _ ->
          subst
            (λ T' -> Computable (isType [] T'))
            (sym
              (cong (λ rho -> subTy tau (subTy rho T)) (liftSubstCompKeep (liftSubst sigma))
                ∙ subTyComp tau (liftSubst (liftSubst sigma)) T))
            (substDerivTyComp
              dT
              (composeTwoBinders fits dAσ dBσ fits2)))
        (λ tau₁ tau₂ fitsEq2 _ ->
          subst
            (λ J -> Computable J)
            (sym
              (cong₂ (typeEq [])
                (cong (λ rho -> subTy tau₁ (subTy rho T)) (liftSubstCompKeep (liftSubst sigma))
                  ∙ subTyComp tau₁ (liftSubst (liftSubst sigma)) T)
                (cong (λ rho -> subTy tau₂ (subTy rho T)) (liftSubstCompKeep (liftSubst sigma))
                  ∙ subTyComp tau₂ (liftSubst (liftSubst sigma)) T)))
            (eqSubDerivTyComp
              dT
              (composeTwoBindersEq fits dAσ dBσ fitsEq2))))

  openHypTm1 : {gamma : Ctx} {A T : RawType} {t : RawTerm} {sigma : Subst}
    -> FitsSubst [] gamma sigma
    -> Derivable (isType [] (subTy sigma A))
    -> Derivable (hasTy (A ∷ gamma) t T)
    -> HypComputable
         (hasTy (subTy sigma A ∷ [])
           (subTm (liftSubst sigma) t)
           (subTy (liftSubst sigma) T))
  openHypTm1 {A = A} {T = T} {t = t} {sigma = sigma}
    fits dAσ dt =
    subst
      (λ J -> HypComputable J)
      (cong₂
        (hasTy (subTy sigma A ∷ []))
        (cong (λ rho -> subTm rho t) (liftSubstCompKeep sigma))
        (cong (λ rho -> subTy rho T) (liftSubstCompKeep sigma)))
      (hypTmOpen
        nonemptyNeNil
        (substTmRule dt (liftFitsOne fits dAσ))
        (subst
          (λ T' -> HypComputable (isType (subTy sigma A ∷ []) T'))
          (sym (cong (λ rho -> subTy rho T) (liftSubstCompKeep sigma)))
          (openHypTy1 fits dAσ (assocTy dt)))
        (λ tau fits2 _ ->
          subst
            (λ J -> Computable J)
            (sym
              (cong₂ (hasTy [])
                (cong (λ rho -> subTm tau (subTm rho t)) (liftSubstCompKeep sigma)
                  ∙ subTmComp tau (liftSubst sigma) t)
                (cong (λ rho -> subTy tau (subTy rho T)) (liftSubstCompKeep sigma)
                  ∙ subTyComp tau (liftSubst sigma) T)))
            (substDerivTmComp
              dt
              (composeOneBinder fits dAσ fits2)))
        (λ tau₁ tau₂ fitsEq2 _ ->
          subst
            (λ J -> Computable J)
            (sym
              (cong₃ (termEq [])
                (cong (λ rho -> subTm tau₁ (subTm rho t)) (liftSubstCompKeep sigma)
                  ∙ subTmComp tau₁ (liftSubst sigma) t)
                (cong (λ rho -> subTm tau₂ (subTm rho t)) (liftSubstCompKeep sigma)
                  ∙ subTmComp tau₂ (liftSubst sigma) t)
                (cong (λ rho -> subTy tau₁ (subTy rho T)) (liftSubstCompKeep sigma)
                  ∙ subTyComp tau₁ (liftSubst sigma) T)))
            (eqSubDerivTmComp
              dt
              (composeOneBinderEq fits dAσ fitsEq2))))

  openHypTmEq1 : {gamma : Ctx} {A T : RawType} {t u : RawTerm} {sigma : Subst}
    -> FitsSubst [] gamma sigma
    -> Derivable (isType [] (subTy sigma A))
    -> Derivable (termEq (A ∷ gamma) t u T)
    -> HypComputable
         (termEq (subTy sigma A ∷ [])
           (subTm (liftSubst sigma) t)
           (subTm (liftSubst sigma) u)
           (subTy (liftSubst sigma) T))
  openHypTmEq1 {A = A} {T = T} {t = t} {u = u} {sigma = sigma}
    fits dAσ dtu =
    subst
      (λ J -> HypComputable J)
      (cong₃
        (termEq (subTy sigma A ∷ []))
        (cong (λ rho -> subTm rho t) (liftSubstCompKeep sigma))
        (cong (λ rho -> subTm rho u) (liftSubstCompKeep sigma))
        (cong (λ rho -> subTy rho T) (liftSubstCompKeep sigma)))
      (hypTmEqOpen
        nonemptyNeNil
        (substTmEqRule dtu (liftFitsOne fits dAσ))
        (subst
          (λ J -> HypComputable J)
          (sym
            (cong₂
              (hasTy (subTy sigma A ∷ []))
              (cong (λ rho -> subTm rho t) (liftSubstCompKeep sigma))
              (cong (λ rho -> subTy rho T) (liftSubstCompKeep sigma))))
          (openHypTm1 fits dAσ (assocTmLeft dtu)))
        (λ tau fits2 _ ->
          subst
            (λ J -> Computable J)
            (sym
              (cong₃ (termEq [])
                (cong (λ rho -> subTm tau (subTm rho t)) (liftSubstCompKeep sigma)
                  ∙ subTmComp tau (liftSubst sigma) t)
                (cong (λ rho -> subTm tau (subTm rho u)) (liftSubstCompKeep sigma)
                  ∙ subTmComp tau (liftSubst sigma) u)
                (cong (λ rho -> subTy tau (subTy rho T)) (liftSubstCompKeep sigma)
                  ∙ subTyComp tau (liftSubst sigma) T)))
            (substDerivTmEqComp
              dtu
              (composeOneBinder fits dAσ fits2)))
        (λ tau₁ tau₂ fitsEq2 _ ->
          subst
            (λ J -> Computable J)
            (sym
              (cong₃ (termEq [])
                (cong (λ rho -> subTm tau₁ (subTm rho t)) (liftSubstCompKeep sigma)
                  ∙ subTmComp tau₁ (liftSubst sigma) t)
                (cong (λ rho -> subTm tau₂ (subTm rho u)) (liftSubstCompKeep sigma)
                  ∙ subTmComp tau₂ (liftSubst sigma) u)
                (cong (λ rho -> subTy tau₁ (subTy rho T)) (liftSubstCompKeep sigma)
                  ∙ subTyComp tau₁ (liftSubst sigma) T)))
            (eqSubDerivTmEqComp
              dtu
              (composeOneBinderEq fits dAσ fitsEq2))))

  openHypTm2 : {gamma : Ctx} {A B T : RawType} {t : RawTerm} {sigma : Subst}
    -> FitsSubst [] gamma sigma
    -> Derivable (isType [] (subTy sigma A))
    -> Derivable (isType (subTy sigma A ∷ []) (subTy (liftSubst sigma) B))
    -> Derivable (hasTy (B ∷ A ∷ gamma) t T)
    -> HypComputable
         (hasTy (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ [])
           (subTm (liftSubst (liftSubst sigma)) t)
           (subTy (liftSubst (liftSubst sigma)) T))
  openHypTm2 {gamma = gamma} {A = A} {B = B} {T = T} {t = t} {sigma = sigma}
    fits dAσ dBσ dt =
    let
      lifted1 : FitsSubst (subTy sigma A ∷ []) (A ∷ gamma) (liftSubst sigma)
      lifted1 =
        subst
          (λ rho -> FitsSubst (subTy sigma A ∷ []) (A ∷ gamma) rho)
          (liftSubstCompKeep sigma)
          (liftFitsOne fits dAσ)
    in
    subst
      (λ J -> HypComputable J)
      (cong₂
        (hasTy (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []))
        (cong (λ rho -> subTm rho t) (liftSubstCompKeep (liftSubst sigma)))
        (cong (λ rho -> subTy rho T) (liftSubstCompKeep (liftSubst sigma))))
      (hypTmOpen
        nonemptyNeNil
        (substTmRule dt (liftFits lifted1 dBσ))
        (subst
          (λ T' ->
            HypComputable (isType (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) T'))
          (sym (cong (λ rho -> subTy rho T) (liftSubstCompKeep (liftSubst sigma))))
          (openHypTy2 fits dAσ dBσ (assocTy dt)))
        (λ tau fits2 _ ->
          subst
            (λ J -> Computable J)
            (sym
              (cong₂ (hasTy [])
                (cong (λ rho -> subTm tau (subTm rho t)) (liftSubstCompKeep (liftSubst sigma))
                  ∙ subTmComp tau (liftSubst (liftSubst sigma)) t)
                (cong (λ rho -> subTy tau (subTy rho T)) (liftSubstCompKeep (liftSubst sigma))
                  ∙ subTyComp tau (liftSubst (liftSubst sigma)) T)))
            (substDerivTmComp
              dt
              (composeTwoBinders fits dAσ dBσ fits2)))
        (λ tau₁ tau₂ fitsEq2 _ ->
          subst
            (λ J -> Computable J)
            (sym
              (cong₃ (termEq [])
                (cong (λ rho -> subTm tau₁ (subTm rho t)) (liftSubstCompKeep (liftSubst sigma))
                  ∙ subTmComp tau₁ (liftSubst (liftSubst sigma)) t)
                (cong (λ rho -> subTm tau₂ (subTm rho t)) (liftSubstCompKeep (liftSubst sigma))
                  ∙ subTmComp tau₂ (liftSubst (liftSubst sigma)) t)
                (cong (λ rho -> subTy tau₁ (subTy rho T)) (liftSubstCompKeep (liftSubst sigma))
                  ∙ subTyComp tau₁ (liftSubst (liftSubst sigma)) T)))
            (eqSubDerivTmComp
              dt
              (composeTwoBindersEq fits dAσ dBσ fitsEq2))))

  openHypTmEq2 : {gamma : Ctx} {A B T : RawType} {t u : RawTerm} {sigma : Subst}
    -> FitsSubst [] gamma sigma
    -> Derivable (isType [] (subTy sigma A))
    -> Derivable (isType (subTy sigma A ∷ []) (subTy (liftSubst sigma) B))
    -> Derivable (termEq (B ∷ A ∷ gamma) t u T)
    -> HypComputable
         (termEq (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ [])
           (subTm (liftSubst (liftSubst sigma)) t)
           (subTm (liftSubst (liftSubst sigma)) u)
           (subTy (liftSubst (liftSubst sigma)) T))
  openHypTmEq2 {gamma = gamma} {A = A} {B = B} {T = T} {t = t} {u = u} {sigma = sigma}
    fits dAσ dBσ dtu =
    let
      lifted1 : FitsSubst (subTy sigma A ∷ []) (A ∷ gamma) (liftSubst sigma)
      lifted1 =
        subst
          (λ rho -> FitsSubst (subTy sigma A ∷ []) (A ∷ gamma) rho)
          (liftSubstCompKeep sigma)
          (liftFitsOne fits dAσ)
    in
    subst
      (λ J -> HypComputable J)
      (cong₃
        (termEq (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []))
        (cong (λ rho -> subTm rho t) (liftSubstCompKeep (liftSubst sigma)))
        (cong (λ rho -> subTm rho u) (liftSubstCompKeep (liftSubst sigma)))
        (cong (λ rho -> subTy rho T) (liftSubstCompKeep (liftSubst sigma))))
      (hypTmEqOpen
        nonemptyNeNil
        (substTmEqRule dtu (liftFits lifted1 dBσ))
        (subst
          (λ J -> HypComputable J)
          (sym
            (cong₂
              (hasTy (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []))
              (cong (λ rho -> subTm rho t) (liftSubstCompKeep (liftSubst sigma)))
              (cong (λ rho -> subTy rho T) (liftSubstCompKeep (liftSubst sigma)))))
          (openHypTm2 fits dAσ dBσ (assocTmLeft dtu)))
        (λ tau fits2 _ ->
          subst
            (λ J -> Computable J)
            (sym
              (cong₃ (termEq [])
                (cong (λ rho -> subTm tau (subTm rho t)) (liftSubstCompKeep (liftSubst sigma))
                  ∙ subTmComp tau (liftSubst (liftSubst sigma)) t)
                (cong (λ rho -> subTm tau (subTm rho u)) (liftSubstCompKeep (liftSubst sigma))
                  ∙ subTmComp tau (liftSubst (liftSubst sigma)) u)
                (cong (λ rho -> subTy tau (subTy rho T)) (liftSubstCompKeep (liftSubst sigma))
                  ∙ subTyComp tau (liftSubst (liftSubst sigma)) T)))
            (substDerivTmEqComp
              dtu
              (composeTwoBinders fits dAσ dBσ fits2)))
        (λ tau₁ tau₂ fitsEq2 _ ->
          subst
            (λ J -> Computable J)
            (sym
              (cong₃ (termEq [])
                (cong (λ rho -> subTm tau₁ (subTm rho t)) (liftSubstCompKeep (liftSubst sigma))
                  ∙ subTmComp tau₁ (liftSubst (liftSubst sigma)) t)
                (cong (λ rho -> subTm tau₂ (subTm rho u)) (liftSubstCompKeep (liftSubst sigma))
                  ∙ subTmComp tau₂ (liftSubst (liftSubst sigma)) u)
                (cong (λ rho -> subTy tau₁ (subTy rho T)) (liftSubstCompKeep (liftSubst sigma))
                  ∙ subTyComp tau₁ (liftSubst (liftSubst sigma)) T)))
            (eqSubDerivTmEqComp
              dtu
              (composeTwoBindersEq fits dAσ dBσ fitsEq2))))
  compFSigmaClosed : {A B : RawType}
    -> Computable (isType [] A)
    -> HypComputable (isType (A ∷ []) B)
    -> Computable (isType [] (tySigma A B))
  compFSigmaClosed compA compB =
    compTyClosedSigma
      (fSigma (compToDerivable compA) (hypCompToDerivable compB))
      evalSigma
      (reflTy (fSigma (compToDerivable compA) (hypCompToDerivable compB)))
      compA
      (hypCompToDerivable compB)
  
  compISigmaClosed : {a b : RawTerm} {A B : RawType}
    -> Computable (hasTy [] a A)
    -> Computable (hasTy [] b (subTy (singleSubst a) B))
    -> Computable (isType [] (tySigma A B))
    -> Computable (hasTy [] (tmPair a b) (tySigma A B))
  compISigmaClosed compa compb compSigma =
    compTmClosedSigma
      (iSigma (compToDerivable compa) (compToDerivable compb) (compToDerivable compSigma))
      compSigma
      evalSigma
      evalPair
      (reflTm (iSigma (compToDerivable compa) (compToDerivable compb) (compToDerivable compSigma)))
      compa
      compb
  
  compCSigmaClosed : {b c m : RawTerm} {A B M : RawType}
    -> HypComputable (isType ((tySigma A B) ∷ []) M)
    -> Computable (hasTy [] b A)
    -> Computable (hasTy [] c (subTy (singleSubst b) B))
    -> HypComputable (hasTy (B ∷ A ∷ []) m (sigmaBranchTy M))
    -> Computable
         (termEq [] (tmElSigma (tmPair b c) m) (subTm (sigmaCompSub b c) m)
           (subTy (singleSubst (tmPair b c)) M))
  compCSigmaClosed {b = b} {c = c} {m = m} {A = A} {B = B} {M = M}
    compM compb compc compm@(hypTmOpen neq dm compBranchTy sub subEq) =
    lhsEq body
    where
    db : Derivable (hasTy [] b A)
    db = compToDerivable compb
  
    dc : Derivable (hasTy [] c (subTy (singleSubst b) B))
    dc = compToDerivable compc
  
    dM : Derivable (isType ((tySigma A B) ∷ []) M)
    dM = hypCompToDerivable compM
  
    bodyFits : Σ (FitsSubst [] (B ∷ A ∷ []) (sigmaCompSub b c)) (λ fits -> ComputableFits fits)
    bodyFits = sigmaCompComputableFitsHelper compb compc
  
    rawBody : Computable
      (hasTy [] (subTm (sigmaCompSub b c) m) (subTy (sigmaCompSub b c) (sigmaBranchTy M)))
    rawBody = sub (sigmaCompSub b c) (fst bodyFits) (snd bodyFits)
  
    body : Computable
      (hasTy [] (subTm (sigmaCompSub b c) m) (subTy (singleSubst (tmPair b c)) M))
    body =
      subst
        (λ T -> Computable (hasTy [] (subTm (sigmaCompSub b c) m) T))
        (sigmaBranchTyComp b c M)
        rawBody
  
    dEq : Derivable
      (termEq [] (tmElSigma (tmPair b c) m) (subTm (sigmaCompSub b c) m)
        (subTy (singleSubst (tmPair b c)) M))
    dEq = cSigma dM db dc dm
  
    dLeft : Derivable
      (hasTy [] (tmElSigma (tmPair b c) m) (subTy (singleSubst (tmPair b c)) M))
    dLeft = assocTmLeft dEq
  
    lhsEq :
      Computable
        (hasTy [] (subTm (sigmaCompSub b c) m) (subTy (singleSubst (tmPair b c)) M))
      -> Computable
           (termEq [] (tmElSigma (tmPair b c) m) (subTm (sigmaCompSub b c) m)
             (subTy (singleSubst (tmPair b c)) M))
    lhsEq body@(compTmClosedTop drhs compTy evTy evRhs corrRhs) =
      let
        lhsCorr = transTm dEq corrRhs
        lhsComp =
          compTmClosedTop
            dLeft
            compTy
            evTy
            (evalElSigma evalPair evRhs)
            lhsCorr
      in
      compTmEqClosedTop dEq lhsComp body evTy (evalElSigma evalPair evRhs) evRhs
    lhsEq body@(compTmClosedSigma drhs compTy evTy evRhs corrRhs comp₁ comp₂) =
      let
        lhsCorr = transTm dEq corrRhs
        lhsComp =
          compTmClosedSigma
            dLeft
            compTy
            evTy
            (evalElSigma evalPair evRhs)
            lhsCorr
            comp₁
            comp₂
      in
      compTmEqClosedSigma
        dEq
        lhsComp
        body
        evTy
        (evalElSigma evalPair evRhs)
        evRhs
        (compReflTmClosed comp₁)
        (compReflTmClosed comp₂)
    lhsEq body@(compTmClosedEq drhs compTy evTy evRhs corrRhs compEq) =
      let
        lhsCorr = transTm dEq corrRhs
        lhsComp =
          compTmClosedEq
            dLeft
            compTy
            evTy
            (evalElSigma evalPair evRhs)
            lhsCorr
            compEq
      in
      compTmEqClosedEq
        dEq
        lhsComp
        body
        evTy
        (evalElSigma evalPair evRhs)
        evRhs
        compEq
    lhsEq body@(compTmClosedQtr drhs compTy evTy evRhs corrRhs compa) =
      let
        lhsCorr = transTm dEq corrRhs
        lhsComp =
          compTmClosedQtr
            dLeft
            compTy
            evTy
            (evalElSigma evalPair evRhs)
            lhsCorr
            compa
      in
      compTmEqClosedQtr
        dEq
        lhsComp
        body
        evTy
        (evalElSigma evalPair evRhs)
        evRhs
        compa
        compa
  
  compESigmaClosed : {A B M : RawType} {d d' m m' : RawTerm}
    -> ({t u v : RawTerm} {T : RawType}
         -> Computable (termEq [] t u T)
         -> Computable (termEq [] u v T)
         -> Computable (termEq [] t v T))
    -> ({t u : RawTerm} {T U : RawType}
         -> Computable (termEq [] t u T)
         -> Computable (typeEq [] T U)
         -> Computable (termEq [] t u U))
    -> HypComputable (isType ((tySigma A B) ∷ []) M)
    -> Computable (termEq [] d d' (tySigma A B))
    -> HypComputable (termEq (B ∷ A ∷ []) m m' (sigmaBranchTy M))
    -> Computable
         (termEq [] (tmElSigma d m) (tmElSigma d' m') (subTy (singleSubst d) M))
  compESigmaClosed {A = A} {B = B} {M = M} {d = d} {d' = d'} {m = m} {m' = m'}
    transCl convEqCl compM compdd'
    compmm'@(hypTmEqOpen neq dll' compBranchTy sub subEq) =
    transCl leftCan (transCl bodyEqD rightCanSym)
    where
    open ClosedSigmaTmEqInv (invertSigmaTmEq compdd' evalSigma)
  
    compSigma : Computable (isType [] (tySigma A B))
    compSigma = compTmToCompTy sigmaTmEqCompLeft
  
    compPairLeft : Computable (hasTy [] (tmPair sigmaTmEqLeftFst sigmaTmEqLeftSnd) (tySigma A B))
    compPairLeft =
      compISigmaClosed sigmaTmEqLeftCompFstTy sigmaTmEqLeftCompSndTy compSigma
  
    compPairRight : Computable (hasTy [] (tmPair sigmaTmEqRightFst sigmaTmEqRightSnd) (tySigma A B))
    compPairRight =
      compISigmaClosed sigmaTmEqRightCompFstTy sigmaTmEqRightCompSndTy compSigma
  
    compLeftCorr : Computable
      (termEq [] d (tmPair sigmaTmEqLeftFst sigmaTmEqLeftSnd) (tySigma A B))
    compLeftCorr =
      compTmEqClosedSigma
        sigmaTmEqLeftCorrPair
        sigmaTmEqCompLeft
        compPairLeft
        evalSigma
        sigmaTmEqEvalLeftPair
        evalPair
        (compReflTmClosed sigmaTmEqLeftCompFstTy)
        (compReflTmClosed sigmaTmEqLeftCompSndTy)

    compLeftCorrSym : Computable
      (termEq [] (tmPair sigmaTmEqLeftFst sigmaTmEqLeftSnd) d (tySigma A B))
    compLeftCorrSym =
      compTmEqClosedSigma
        (symTm sigmaTmEqLeftCorrPair)
        compPairLeft
        sigmaTmEqCompLeft
        evalSigma
        evalPair
        sigmaTmEqEvalLeftPair
        (compReflTmClosed sigmaTmEqLeftCompFstTy)
        (compReflTmClosed sigmaTmEqLeftCompSndTy)
  
    compRightCorr : Computable
      (termEq [] d' (tmPair sigmaTmEqRightFst sigmaTmEqRightSnd) (tySigma A B))
    compRightCorr =
      compTmEqClosedSigma
        sigmaTmEqRightCorrPair
        sigmaTmEqCompRight
        compPairRight
        evalSigma
        sigmaTmEqEvalRightPair
        evalPair
        (compReflTmClosed sigmaTmEqRightCompFstTy)
        (compReflTmClosed sigmaTmEqRightCompSndTy)
  
    branchFitsEq : Σ
      (FitsEqSubst [] (B ∷ A ∷ [])
        (sigmaCompSub sigmaTmEqLeftFst sigmaTmEqLeftSnd)
        (sigmaCompSub sigmaTmEqRightFst sigmaTmEqRightSnd))
      (λ fitsEq -> ComputableFitsEq fitsEq)
    branchFitsEq = sigmaCompComputableFitsEqHelper sigmaTmEqCompFst sigmaTmEqCompSnd
  
    branchEqPair : Computable
      (termEq []
        (subTm (sigmaCompSub sigmaTmEqLeftFst sigmaTmEqLeftSnd) m)
        (subTm (sigmaCompSub sigmaTmEqRightFst sigmaTmEqRightSnd) m')
        (subTy (singleSubst (tmPair sigmaTmEqLeftFst sigmaTmEqLeftSnd)) M))
    branchEqPair =
      subst
        (λ T ->
          Computable
            (termEq []
              (subTm (sigmaCompSub sigmaTmEqLeftFst sigmaTmEqLeftSnd) m)
              (subTm (sigmaCompSub sigmaTmEqRightFst sigmaTmEqRightSnd) m')
              T))
        (sigmaBranchTyComp sigmaTmEqLeftFst sigmaTmEqLeftSnd M)
        (subEq
          (sigmaCompSub sigmaTmEqLeftFst sigmaTmEqLeftSnd)
          (sigmaCompSub sigmaTmEqRightFst sigmaTmEqRightSnd)
          (fst branchFitsEq)
          (snd branchFitsEq))
  
    bodyEqD : Computable
      (termEq []
        (subTm (sigmaCompSub sigmaTmEqLeftFst sigmaTmEqLeftSnd) m)
        (subTm (sigmaCompSub sigmaTmEqRightFst sigmaTmEqRightSnd) m')
        (subTy (singleSubst d) M))
    bodyEqD =
      convEqCl
        branchEqPair
        (compSingleEqSubstTyClosed compM compLeftCorrSym)
  
    bodyLeft : Computable
      (hasTy []
        (subTm (sigmaCompSub sigmaTmEqLeftFst sigmaTmEqLeftSnd) m)
        (subTy (singleSubst d) M))
    bodyLeft = compTmEqLeft bodyEqD
  
    bodyRight : Computable
      (hasTy []
        (subTm (sigmaCompSub sigmaTmEqRightFst sigmaTmEqRightSnd) m')
        (subTy (singleSubst d) M))
    bodyRight = compTmEqRightClosed bodyEqD
  
    dM : Derivable (isType ((tySigma A B) ∷ []) M)
    dM = hypCompToDerivable compM
  
    dm : Derivable (hasTy (B ∷ A ∷ []) m (sigmaBranchTy M))
    dm = assocTmLeft dll'
  
    dm' : Derivable (hasTy (B ∷ A ∷ []) m' (sigmaBranchTy M))
    dm' = assocTmRight dll'
  
    db : Derivable (hasTy [] sigmaTmEqLeftFst A)
    db = compToDerivable sigmaTmEqLeftCompFstTy
  
    dc : Derivable (hasTy [] sigmaTmEqLeftSnd (subTy (singleSubst sigmaTmEqLeftFst) B))
    dc = compToDerivable sigmaTmEqLeftCompSndTy
  
    de : Derivable (hasTy [] sigmaTmEqRightFst A)
    de = compToDerivable sigmaTmEqRightCompFstTy
  
    df : Derivable (hasTy [] sigmaTmEqRightSnd (subTy (singleSubst sigmaTmEqRightFst) B))
    df = compToDerivable sigmaTmEqRightCompSndTy
  
    dLeftStep : Derivable
      (termEq [] (tmElSigma d m) (tmElSigma (tmPair sigmaTmEqLeftFst sigmaTmEqLeftSnd) m)
        (subTy (singleSubst d) M))
    dLeftStep = eSigmaEq dM sigmaTmEqLeftCorrPair (reflTm dm)
  
    dLeftCanon : Derivable
      (termEq []
        (tmElSigma (tmPair sigmaTmEqLeftFst sigmaTmEqLeftSnd) m)
        (subTm (sigmaCompSub sigmaTmEqLeftFst sigmaTmEqLeftSnd) m)
        (subTy (singleSubst d) M))
    dLeftCanon =
      convEq
        (cSigma dM db dc dm)
        (symTy (singleEqSubstTyHelper dM (compToDerivable compLeftCorr)))
  
    dLeftEq : Derivable
      (termEq []
        (tmElSigma d m)
        (subTm (sigmaCompSub sigmaTmEqLeftFst sigmaTmEqLeftSnd) m)
        (subTy (singleSubst d) M))
    dLeftEq = transTm dLeftStep dLeftCanon
  
    dLeftTy : Derivable (hasTy [] (tmElSigma d m) (subTy (singleSubst d) M))
    dLeftTy = assocTmLeft dLeftEq
  
    dRightCanon0 : Derivable
      (termEq []
        (tmElSigma d' m')
        (subTm (sigmaCompSub sigmaTmEqRightFst sigmaTmEqRightSnd) m')
        (subTy (singleSubst d') M))
    dRightCanon0 =
      transTm
        (eSigmaEq dM sigmaTmEqRightCorrPair (reflTm dm'))
        (convEq
          (cSigma dM de df dm')
          (symTy (singleEqSubstTyHelper dM (compToDerivable compRightCorr))))
  
    dRightEq : Derivable
      (termEq []
        (tmElSigma d' m')
        (subTm (sigmaCompSub sigmaTmEqRightFst sigmaTmEqRightSnd) m')
        (subTy (singleSubst d) M))
    dRightEq =
      convEq
        dRightCanon0
        (symTy (singleEqSubstTyHelper dM (compToDerivable compdd')))
  
    dRightTy : Derivable (hasTy [] (tmElSigma d' m') (subTy (singleSubst d) M))
    dRightTy = assocTmLeft dRightEq
  
    mkLeftCanon :
      Derivable
        (termEq []
          (tmElSigma d m)
          (subTm (sigmaCompSub sigmaTmEqLeftFst sigmaTmEqLeftSnd) m)
          (subTy (singleSubst d) M))
      -> Derivable (hasTy [] (tmElSigma d m) (subTy (singleSubst d) M))
      -> d =>e tmPair sigmaTmEqLeftFst sigmaTmEqLeftSnd
      -> Computable
           (hasTy []
             (subTm (sigmaCompSub sigmaTmEqLeftFst sigmaTmEqLeftSnd) m)
             (subTy (singleSubst d) M))
      -> Computable
           (termEq []
             (tmElSigma d m)
             (subTm (sigmaCompSub sigmaTmEqLeftFst sigmaTmEqLeftSnd) m)
             (subTy (singleSubst d) M))
    mkLeftCanon dEq dLeft evd body@(compTmClosedTop _ compTy evTy evRhs corrRhs) =
      let
        lhsCorr = transTm dEq corrRhs
        lhsComp =
          compTmClosedTop
            dLeft
            compTy
            evTy
            (evalElSigma evd evRhs)
            lhsCorr
      in
      compTmEqClosedTop dEq lhsComp body evTy (evalElSigma evd evRhs) evRhs
    mkLeftCanon dEq dLeft evd body@(compTmClosedSigma _ compTy evTy evRhs corrRhs comp₁ comp₂) =
      let
        lhsCorr = transTm dEq corrRhs
        lhsComp =
          compTmClosedSigma
            dLeft
            compTy
            evTy
            (evalElSigma evd evRhs)
            lhsCorr
            comp₁
            comp₂
      in
      compTmEqClosedSigma
        dEq
        lhsComp
        body
        evTy
        (evalElSigma evd evRhs)
        evRhs
        (compReflTmClosed comp₁)
        (compReflTmClosed comp₂)
    mkLeftCanon dEq dLeft evd body@(compTmClosedEq _ compTy evTy evRhs corrRhs compEq) =
      let
        lhsCorr = transTm dEq corrRhs
        lhsComp =
          compTmClosedEq
            dLeft
            compTy
            evTy
            (evalElSigma evd evRhs)
            lhsCorr
            compEq
      in
      compTmEqClosedEq
        dEq
        lhsComp
        body
        evTy
        (evalElSigma evd evRhs)
        evRhs
        compEq
    mkLeftCanon dEq dLeft evd body@(compTmClosedQtr _ compTy evTy evRhs corrRhs compa) =
      let
        lhsCorr = transTm dEq corrRhs
        lhsComp =
          compTmClosedQtr
            dLeft
            compTy
            evTy
            (evalElSigma evd evRhs)
            lhsCorr
            compa
      in
      compTmEqClosedQtr
        dEq
        lhsComp
        body
        evTy
        (evalElSigma evd evRhs)
        evRhs
        compa
        compa
  
    mkRightCanon :
      Derivable
        (termEq []
          (tmElSigma d' m')
          (subTm (sigmaCompSub sigmaTmEqRightFst sigmaTmEqRightSnd) m')
          (subTy (singleSubst d) M))
      -> Derivable (hasTy [] (tmElSigma d' m') (subTy (singleSubst d) M))
      -> d' =>e tmPair sigmaTmEqRightFst sigmaTmEqRightSnd
      -> Computable
           (hasTy []
             (subTm (sigmaCompSub sigmaTmEqRightFst sigmaTmEqRightSnd) m')
             (subTy (singleSubst d) M))
      -> Computable
           (termEq []
             (tmElSigma d' m')
             (subTm (sigmaCompSub sigmaTmEqRightFst sigmaTmEqRightSnd) m')
             (subTy (singleSubst d) M))
    mkRightCanon dEq dLeft evd body@(compTmClosedTop _ compTy evTy evRhs corrRhs) =
      let
        lhsCorr = transTm dEq corrRhs
        lhsComp =
          compTmClosedTop
            dLeft
            compTy
            evTy
            (evalElSigma evd evRhs)
            lhsCorr
      in
      compTmEqClosedTop dEq lhsComp body evTy (evalElSigma evd evRhs) evRhs
    mkRightCanon dEq dLeft evd body@(compTmClosedSigma _ compTy evTy evRhs corrRhs comp₁ comp₂) =
      let
        lhsCorr = transTm dEq corrRhs
        lhsComp =
          compTmClosedSigma
            dLeft
            compTy
            evTy
            (evalElSigma evd evRhs)
            lhsCorr
            comp₁
            comp₂
      in
      compTmEqClosedSigma
        dEq
        lhsComp
        body
        evTy
        (evalElSigma evd evRhs)
        evRhs
        (compReflTmClosed comp₁)
        (compReflTmClosed comp₂)
    mkRightCanon dEq dLeft evd body@(compTmClosedEq _ compTy evTy evRhs corrRhs compEq) =
      let
        lhsCorr = transTm dEq corrRhs
        lhsComp =
          compTmClosedEq
            dLeft
            compTy
            evTy
            (evalElSigma evd evRhs)
            lhsCorr
            compEq
      in
      compTmEqClosedEq
        dEq
        lhsComp
        body
        evTy
        (evalElSigma evd evRhs)
        evRhs
        compEq
    mkRightCanon dEq dLeft evd body@(compTmClosedQtr _ compTy evTy evRhs corrRhs compa) =
      let
        lhsCorr = transTm dEq corrRhs
        lhsComp =
          compTmClosedQtr
            dLeft
            compTy
            evTy
            (evalElSigma evd evRhs)
            lhsCorr
            compa
      in
      compTmEqClosedQtr
        dEq
        lhsComp
        body
        evTy
        (evalElSigma evd evRhs)
        evRhs
        compa
        compa

    mkRightCanonSym :
      Derivable
        (termEq []
          (tmElSigma d' m')
          (subTm (sigmaCompSub sigmaTmEqRightFst sigmaTmEqRightSnd) m')
          (subTy (singleSubst d) M))
      -> Derivable (hasTy [] (tmElSigma d' m') (subTy (singleSubst d) M))
      -> d' =>e tmPair sigmaTmEqRightFst sigmaTmEqRightSnd
      -> Computable
           (hasTy []
             (subTm (sigmaCompSub sigmaTmEqRightFst sigmaTmEqRightSnd) m')
             (subTy (singleSubst d) M))
      -> Computable
           (termEq []
             (subTm (sigmaCompSub sigmaTmEqRightFst sigmaTmEqRightSnd) m')
             (tmElSigma d' m')
             (subTy (singleSubst d) M))
    mkRightCanonSym dEq dLeft evd body@(compTmClosedTop _ compTy evTy evRhs corrRhs) =
      let
        lhsCorr = transTm dEq corrRhs
        lhsComp =
          compTmClosedTop
            dLeft
            compTy
            evTy
            (evalElSigma evd evRhs)
            lhsCorr
      in
      compTmEqClosedTop
        (symTm dEq)
        body
        lhsComp
        evTy
        evRhs
        (evalElSigma evd evRhs)
    mkRightCanonSym dEq dLeft evd body@(compTmClosedSigma _ compTy evTy evRhs corrRhs comp₁ comp₂) =
      let
        lhsCorr = transTm dEq corrRhs
        lhsComp =
          compTmClosedSigma
            dLeft
            compTy
            evTy
            (evalElSigma evd evRhs)
            lhsCorr
            comp₁
            comp₂
      in
      compTmEqClosedSigma
        (symTm dEq)
        body
        lhsComp
        evTy
        evRhs
        (evalElSigma evd evRhs)
        (compReflTmClosed comp₁)
        (compReflTmClosed comp₂)
    mkRightCanonSym dEq dLeft evd body@(compTmClosedEq _ compTy evTy evRhs corrRhs compEq) =
      let
        lhsCorr = transTm dEq corrRhs
        lhsComp =
          compTmClosedEq
            dLeft
            compTy
            evTy
            (evalElSigma evd evRhs)
            lhsCorr
            compEq
      in
      compTmEqClosedEq
        (symTm dEq)
        body
        lhsComp
        evTy
        evRhs
        (evalElSigma evd evRhs)
        compEq
    mkRightCanonSym dEq dLeft evd body@(compTmClosedQtr _ compTy evTy evRhs corrRhs compa) =
      let
        lhsCorr = transTm dEq corrRhs
        lhsComp =
          compTmClosedQtr
            dLeft
            compTy
            evTy
            (evalElSigma evd evRhs)
            lhsCorr
            compa
      in
      compTmEqClosedQtr
        (symTm dEq)
        body
        lhsComp
        evTy
        evRhs
        (evalElSigma evd evRhs)
        compa
        compa
  
    leftCan : Computable
      (termEq []
        (tmElSigma d m)
        (subTm (sigmaCompSub sigmaTmEqLeftFst sigmaTmEqLeftSnd) m)
        (subTy (singleSubst d) M))
    leftCan = mkLeftCanon dLeftEq dLeftTy sigmaTmEqEvalLeftPair bodyLeft
  
    rightCan : Computable
      (termEq []
        (tmElSigma d' m')
        (subTm (sigmaCompSub sigmaTmEqRightFst sigmaTmEqRightSnd) m')
        (subTy (singleSubst d) M))
    rightCan = mkRightCanon dRightEq dRightTy sigmaTmEqEvalRightPair bodyRight

    rightCanSym : Computable
      (termEq []
        (subTm (sigmaCompSub sigmaTmEqRightFst sigmaTmEqRightSnd) m')
        (tmElSigma d' m')
        (subTy (singleSubst d) M))
    rightCanSym = mkRightCanonSym dRightEq dRightTy sigmaTmEqEvalRightPair bodyRight
  
  compFQtrClosed : {A : RawType}
    -> Computable (isType [] A)
    -> Computable (isType [] (tyQtr A))
  compFQtrClosed compA =
    compTyClosedQtr
      (fQtr (compToDerivable compA))
      evalQtr
      (reflTy (fQtr (compToDerivable compA)))
      compA
  
  compIQtrClosed : {a : RawTerm} {A : RawType}
    -> Computable (hasTy [] a A)
    -> Computable (hasTy [] (tmClass a) (tyQtr A))
  compIQtrClosed compa =
    compTmClosedQtr
      (iQtr (compToDerivable compa))
      (compFQtrClosed (compTmToCompTy compa))
      evalQtr
      evalClass
      (reflTm (iQtr (compToDerivable compa)))
      compa
  
  compIQtrEqClosed : {a b : RawTerm} {A : RawType}
    -> Computable (hasTy [] a A)
    -> Computable (hasTy [] b A)
    -> Computable (termEq [] (tmClass a) (tmClass b) (tyQtr A))
  compIQtrEqClosed compa compb =
    compTmEqClosedQtr
      (iQtrEq (compToDerivable compa) (compToDerivable compb))
      (compIQtrClosed compa)
      (compIQtrClosed compb)
      evalQtr
      evalClass
      evalClass
      compa
      compb
  
  compCQtrClosed : {a l : RawTerm} {A L : RawType}
    -> HypComputable (isType ((tyQtr A) ∷ []) L)
    -> Computable (hasTy [] a A)
    -> HypComputable (hasTy (A ∷ []) l (qtrBranchTy L))
    -> HypComputable
         (termEq (wkTyBy 1 A ∷ A ∷ []) (wkTmBy 1 l) (renTm qtrSecondBranchRen l) (qtrCohTy L))
    -> Computable
         (termEq [] (tmElQtr l (tmClass a)) (subTm (qtrCompSub a) l)
           (subTy (singleSubst (tmClass a)) L))
  compCQtrClosed {a = a} {l = l} {A = A} {L = L}
    compL compa compl@(hypTmOpen neq dl compBranchTy sub subEq) coh =
    lhsEq body
    where
    dL : Derivable (isType ((tyQtr A) ∷ []) L)
    dL = hypCompToDerivable compL
  
    da : Derivable (hasTy [] a A)
    da = compToDerivable compa
  
    dcoh : Derivable
      (termEq (wkTyBy 1 A ∷ A ∷ []) (wkTmBy 1 l) (renTm qtrSecondBranchRen l) (qtrCohTy L))
    dcoh = hypCompToDerivable coh
  
    fits : Σ (FitsSubst [] (A ∷ []) (qtrCompSub a)) (λ fit -> ComputableFits fit)
    fits = qtrCompComputableFitsHelper compa
  
    rawBody : Computable
      (hasTy [] (subTm (qtrCompSub a) l) (subTy (qtrCompSub a) (qtrBranchTy L)))
    rawBody = sub (qtrCompSub a) (fst fits) (snd fits)
  
    body : Computable
      (hasTy [] (subTm (qtrCompSub a) l) (subTy (singleSubst (tmClass a)) L))
    body =
      subst
        (λ T -> Computable (hasTy [] (subTm (qtrCompSub a) l) T))
        (qtrBranchTyComp a L)
        rawBody
  
    dEq : Derivable
      (termEq [] (tmElQtr l (tmClass a)) (subTm (qtrCompSub a) l)
        (subTy (singleSubst (tmClass a)) L))
    dEq = cQtr dL da dl dcoh
  
    dLeft : Derivable
      (hasTy [] (tmElQtr l (tmClass a)) (subTy (singleSubst (tmClass a)) L))
    dLeft = assocTmLeft dEq
  
    lhsEq :
      Computable
        (hasTy [] (subTm (qtrCompSub a) l) (subTy (singleSubst (tmClass a)) L))
      -> Computable
           (termEq [] (tmElQtr l (tmClass a)) (subTm (qtrCompSub a) l)
             (subTy (singleSubst (tmClass a)) L))
    lhsEq body@(compTmClosedTop drhs compTy evTy evRhs corrRhs) =
      let
        lhsCorr = transTm dEq corrRhs
        lhsComp =
          compTmClosedTop
            dLeft
            compTy
            evTy
            (evalElQtr evalClass evRhs)
            lhsCorr
      in
      compTmEqClosedTop dEq lhsComp body evTy (evalElQtr evalClass evRhs) evRhs
    lhsEq body@(compTmClosedSigma drhs compTy evTy evRhs corrRhs comp₁ comp₂) =
      let
        lhsCorr = transTm dEq corrRhs
        lhsComp =
          compTmClosedSigma
            dLeft
            compTy
            evTy
            (evalElQtr evalClass evRhs)
            lhsCorr
            comp₁
            comp₂
      in
      compTmEqClosedSigma
        dEq
        lhsComp
        body
        evTy
        (evalElQtr evalClass evRhs)
        evRhs
        (compReflTmClosed comp₁)
        (compReflTmClosed comp₂)
    lhsEq body@(compTmClosedEq drhs compTy evTy evRhs corrRhs compEq) =
      let
        lhsCorr = transTm dEq corrRhs
        lhsComp =
          compTmClosedEq
            dLeft
            compTy
            evTy
            (evalElQtr evalClass evRhs)
            lhsCorr
            compEq
      in
      compTmEqClosedEq
        dEq
        lhsComp
        body
        evTy
        (evalElQtr evalClass evRhs)
        evRhs
        compEq
    lhsEq body@(compTmClosedQtr drhs compTy evTy evRhs corrRhs compx) =
      let
        lhsCorr = transTm dEq corrRhs
        lhsComp =
          compTmClosedQtr
            dLeft
            compTy
            evTy
            (evalElQtr evalClass evRhs)
            lhsCorr
            compx
      in
      compTmEqClosedQtr
        dEq
        lhsComp
        body
        evTy
        (evalElQtr evalClass evRhs)
        evRhs
        compx
        compx
  
  compEQtrClosed : {A L : RawType} {l l' p p' : RawTerm}
    -> ({t u v : RawTerm} {T : RawType}
         -> Computable (termEq [] t u T)
         -> Computable (termEq [] u v T)
         -> Computable (termEq [] t v T))
    -> ({t u : RawTerm} {T : RawType}
         -> Computable (termEq [] t u T)
         -> Computable (termEq [] u t T))
    -> ({t u : RawTerm} {T U : RawType}
         -> Computable (termEq [] t u T)
         -> Computable (typeEq [] T U)
         -> Computable (termEq [] t u U))
    -> HypComputable (isType ((tyQtr A) ∷ []) L)
    -> Computable (termEq [] p p' (tyQtr A))
    -> HypComputable (termEq (A ∷ []) l l' (qtrBranchTy L))
    -> HypComputable
         (termEq (wkTyBy 1 A ∷ A ∷ []) (wkTmBy 1 l) (renTm qtrSecondBranchRen l) (qtrCohTy L))
    -> HypComputable
         (termEq (wkTyBy 1 A ∷ A ∷ []) (wkTmBy 1 l') (renTm qtrSecondBranchRen l') (qtrCohTy L))
    -> Computable
         (termEq [] (tmElQtr l p) (tmElQtr l' p') (subTy (singleSubst p) L))
  compEQtrClosed {A = A} {L = L} {l = l} {l' = l'} {p = p} {p' = p'}
    transCl symCl convEqCl compL comppp'
    compll'@(hypTmEqOpen neq dll' compBranchTy sub subEq)
    coh
    coh'@(hypTmEqOpen neqCoh' dcoh'comp compCohTy' subCoh' subEqCoh') =
    transCl leftCan (transCl bodyEqP (symCl rightCan))
    where
    open ClosedQtrTmEqInv (invertQtrTmEq comppp' evalQtr)
  
    compQtr : Computable (isType [] (tyQtr A))
    compQtr = compTmToCompTy qtrTmEqCompLeft
  
    compClassLeft : Computable (hasTy [] (tmClass qtrTmEqLeftRepr) (tyQtr A))
    compClassLeft = compIQtrClosed qtrTmEqCompLeftRepr
  
    compClassRight : Computable (hasTy [] (tmClass qtrTmEqRightRepr) (tyQtr A))
    compClassRight = compIQtrClosed qtrTmEqCompRightRepr
  
    compLeftCorr : Computable
      (termEq [] p (tmClass qtrTmEqLeftRepr) (tyQtr A))
    compLeftCorr =
      compTmEqClosedQtr
        qtrTmEqLeftCorrClass
        qtrTmEqCompLeft
        compClassLeft
        evalQtr
        qtrTmEqEvalLeftClass
        evalClass
        qtrTmEqCompLeftRepr
        qtrTmEqCompLeftRepr
  
    compRightCorr : Computable
      (termEq [] p' (tmClass qtrTmEqRightRepr) (tyQtr A))
    compRightCorr =
      compTmEqClosedQtr
        qtrTmEqRightCorrClass
        qtrTmEqCompRight
        compClassRight
        evalQtr
        qtrTmEqEvalRightClass
        evalClass
        qtrTmEqCompRightRepr
        qtrTmEqCompRightRepr
  
    dL : Derivable (isType ((tyQtr A) ∷ []) L)
    dL = hypCompToDerivable compL
  
    dl : Derivable (hasTy (A ∷ []) l (qtrBranchTy L))
    dl = assocTmLeft dll'
  
    dl' : Derivable (hasTy (A ∷ []) l' (qtrBranchTy L))
    dl' = assocTmRight dll'
  
    dcoh : Derivable
      (termEq (wkTyBy 1 A ∷ A ∷ []) (wkTmBy 1 l) (renTm qtrSecondBranchRen l) (qtrCohTy L))
    dcoh = hypCompToDerivable coh
  
    dcoh' : Derivable
      (termEq (wkTyBy 1 A ∷ A ∷ []) (wkTmBy 1 l') (renTm qtrSecondBranchRen l') (qtrCohTy L))
    dcoh' = hypCompToDerivable coh'
  
    da : Derivable (hasTy [] qtrTmEqLeftRepr A)
    da = compToDerivable qtrTmEqCompLeftRepr
  
    db : Derivable (hasTy [] qtrTmEqRightRepr A)
    db = compToDerivable qtrTmEqCompRightRepr
  
    dHeadTyPath : A ≡ subTy (qtrCompSub qtrTmEqLeftRepr) (wkTyBy 1 A)
    dHeadTyPath =
      sym
        (cong (subTy (qtrCompSub qtrTmEqLeftRepr)) (renTyKeepSubstBy 1 A)
          ∙ subTyComp (qtrCompSub qtrTmEqLeftRepr) (keepSubstBy 1) A
          ∙ cong (λ rho -> subTy rho A) (funExt λ n -> refl)
          ∙ subTyId A)
  
    dbOnHead : Derivable
      (hasTy [] qtrTmEqRightRepr (subTy (qtrCompSub qtrTmEqLeftRepr) (wkTyBy 1 A)))
    dbOnHead = subst (λ T -> Derivable (hasTy [] qtrTmEqRightRepr T)) dHeadTyPath db
  
    compbOnHead : Computable
      (hasTy [] qtrTmEqRightRepr (subTy (qtrCompSub qtrTmEqLeftRepr) (wkTyBy 1 A)))
    compbOnHead =
      subst
        (λ T -> Computable (hasTy [] qtrTmEqRightRepr T))
        dHeadTyPath
        qtrTmEqCompRightRepr
  
    branchFitsLeft : Σ (FitsSubst [] (A ∷ []) (qtrCompSub qtrTmEqLeftRepr)) (λ fits -> ComputableFits fits)
    branchFitsLeft = qtrCompComputableFitsHelper qtrTmEqCompLeftRepr
  
    branchEqClassA : Computable
      (termEq []
        (subTm (qtrCompSub qtrTmEqLeftRepr) l)
        (subTm (qtrCompSub qtrTmEqLeftRepr) l')
        (subTy (singleSubst (tmClass qtrTmEqLeftRepr)) L))
    branchEqClassA =
      subst
        (λ T ->
          Computable
            (termEq []
              (subTm (qtrCompSub qtrTmEqLeftRepr) l)
              (subTm (qtrCompSub qtrTmEqLeftRepr) l')
              T))
        (qtrBranchTyComp qtrTmEqLeftRepr L)
        (sub
          (qtrCompSub qtrTmEqLeftRepr)
          (fst branchFitsLeft)
          (snd branchFitsLeft))
  
    cohFitsRight : FitsSubst [] (wkTyBy 1 A ∷ A ∷ [])
      (consSubst qtrTmEqRightRepr (consSubst qtrTmEqLeftRepr idSubst))
    cohFitsRight =
      fitsCons
        (fst (qtrCompComputableFitsHelper qtrTmEqCompLeftRepr))
        dbOnHead
  
    cohFitsRightComp : ComputableFits cohFitsRight
    cohFitsRightComp =
      compFitsCons
        (snd (qtrCompComputableFitsHelper qtrTmEqCompLeftRepr))
        compbOnHead
  
    cohEqClassA : Computable
      (termEq []
        (subTm (qtrCompSub qtrTmEqLeftRepr) l')
        (subTm (qtrCompSub qtrTmEqRightRepr) l')
        (subTy (singleSubst (tmClass qtrTmEqLeftRepr)) L))
    cohEqClassA =
      subst
        (λ t ->
          Computable
            (termEq []
              t
              (subTm (qtrCompSub qtrTmEqRightRepr) l')
              (subTy (singleSubst (tmClass qtrTmEqLeftRepr)) L)))
        (qtrCohLeftTmComp qtrTmEqLeftRepr qtrTmEqRightRepr l')
        (subst
          (λ u ->
            Computable
              (termEq []
                (subTm (consSubst qtrTmEqRightRepr (consSubst qtrTmEqLeftRepr idSubst))
                  (wkTmBy 1 l'))
                u
                (subTy (singleSubst (tmClass qtrTmEqLeftRepr)) L)))
          (qtrCohRightTmComp qtrTmEqLeftRepr qtrTmEqRightRepr l')
          (subst
            (λ T ->
              Computable
                (termEq []
                  (subTm (consSubst qtrTmEqRightRepr (consSubst qtrTmEqLeftRepr idSubst))
                    (wkTmBy 1 l'))
                  (subTm (consSubst qtrTmEqRightRepr (consSubst qtrTmEqLeftRepr idSubst))
                    (renTm qtrSecondBranchRen l'))
                  T))
            (qtrCohTyComp qtrTmEqLeftRepr qtrTmEqRightRepr L)
            (subCoh'
              (consSubst qtrTmEqRightRepr (consSubst qtrTmEqLeftRepr idSubst))
              cohFitsRight
              cohFitsRightComp)))
  
    bodyEqClassA : Computable
      (termEq []
        (subTm (qtrCompSub qtrTmEqLeftRepr) l)
        (subTm (qtrCompSub qtrTmEqRightRepr) l')
        (subTy (singleSubst (tmClass qtrTmEqLeftRepr)) L))
    bodyEqClassA = transCl branchEqClassA cohEqClassA
  
    bodyEqP : Computable
      (termEq []
        (subTm (qtrCompSub qtrTmEqLeftRepr) l)
        (subTm (qtrCompSub qtrTmEqRightRepr) l')
        (subTy (singleSubst p) L))
    bodyEqP =
      convEqCl
        bodyEqClassA
        (compSingleEqSubstTyClosed compL (symCl compLeftCorr))
  
    bodyLeft : Computable
      (hasTy []
        (subTm (qtrCompSub qtrTmEqLeftRepr) l)
        (subTy (singleSubst p) L))
    bodyLeft = compTmEqLeft bodyEqP
  
    bodyRight : Computable
      (hasTy []
        (subTm (qtrCompSub qtrTmEqRightRepr) l')
        (subTy (singleSubst p) L))
    bodyRight = compTmEqRightClosed bodyEqP
  
    dLeftStep : Derivable
      (termEq [] (tmElQtr l p) (tmElQtr l (tmClass qtrTmEqLeftRepr)) (subTy (singleSubst p) L))
    dLeftStep =
      eQtrEq
        dL
        (compToDerivable compLeftCorr)
        (reflTm dl)
        dcoh
        dcoh
  
    dLeftCanon : Derivable
      (termEq []
        (tmElQtr l (tmClass qtrTmEqLeftRepr))
        (subTm (qtrCompSub qtrTmEqLeftRepr) l)
        (subTy (singleSubst p) L))
    dLeftCanon =
      convEq
        (cQtr dL da dl dcoh)
        (symTy (singleEqSubstTyHelper dL (compToDerivable compLeftCorr)))
  
    dLeftEq : Derivable
      (termEq []
        (tmElQtr l p)
        (subTm (qtrCompSub qtrTmEqLeftRepr) l)
        (subTy (singleSubst p) L))
    dLeftEq = transTm dLeftStep dLeftCanon
  
    dLeftTy : Derivable (hasTy [] (tmElQtr l p) (subTy (singleSubst p) L))
    dLeftTy = assocTmLeft dLeftEq
  
    dRightCanon0 : Derivable
      (termEq []
        (tmElQtr l' p')
        (subTm (qtrCompSub qtrTmEqRightRepr) l')
        (subTy (singleSubst p') L))
    dRightCanon0 =
      transTm
        (eQtrEq dL (compToDerivable compRightCorr) (reflTm dl') dcoh' dcoh')
        (convEq
          (cQtr dL db dl' dcoh')
          (symTy (singleEqSubstTyHelper dL (compToDerivable compRightCorr))))
  
    dRightEq : Derivable
      (termEq []
        (tmElQtr l' p')
        (subTm (qtrCompSub qtrTmEqRightRepr) l')
        (subTy (singleSubst p) L))
    dRightEq =
      convEq
        dRightCanon0
        (symTy (singleEqSubstTyHelper dL (compToDerivable comppp')))
  
    dRightTy : Derivable (hasTy [] (tmElQtr l' p') (subTy (singleSubst p) L))
    dRightTy = assocTmLeft dRightEq
  
    mkLeftCanon :
      Derivable
        (termEq []
          (tmElQtr l p)
          (subTm (qtrCompSub qtrTmEqLeftRepr) l)
          (subTy (singleSubst p) L))
      -> Derivable (hasTy [] (tmElQtr l p) (subTy (singleSubst p) L))
      -> p =>e tmClass qtrTmEqLeftRepr
      -> Computable
           (hasTy []
             (subTm (qtrCompSub qtrTmEqLeftRepr) l)
             (subTy (singleSubst p) L))
      -> Computable
           (termEq []
             (tmElQtr l p)
             (subTm (qtrCompSub qtrTmEqLeftRepr) l)
             (subTy (singleSubst p) L))
    mkLeftCanon dEq dLeft evp body@(compTmClosedTop _ compTy evTy evRhs corrRhs) =
      let
        lhsCorr = transTm dEq corrRhs
        lhsComp =
          compTmClosedTop
            dLeft
            compTy
            evTy
            (evalElQtr evp evRhs)
            lhsCorr
      in
      compTmEqClosedTop dEq lhsComp body evTy (evalElQtr evp evRhs) evRhs
    mkLeftCanon dEq dLeft evp body@(compTmClosedSigma _ compTy evTy evRhs corrRhs comp₁ comp₂) =
      let
        lhsCorr = transTm dEq corrRhs
        lhsComp =
          compTmClosedSigma
            dLeft
            compTy
            evTy
            (evalElQtr evp evRhs)
            lhsCorr
            comp₁
            comp₂
      in
      compTmEqClosedSigma
        dEq
        lhsComp
        body
        evTy
        (evalElQtr evp evRhs)
        evRhs
        (compReflTmClosed comp₁)
        (compReflTmClosed comp₂)
    mkLeftCanon dEq dLeft evp body@(compTmClosedEq _ compTy evTy evRhs corrRhs compEq) =
      let
        lhsCorr = transTm dEq corrRhs
        lhsComp =
          compTmClosedEq
            dLeft
            compTy
            evTy
            (evalElQtr evp evRhs)
            lhsCorr
            compEq
      in
      compTmEqClosedEq
        dEq
        lhsComp
        body
        evTy
        (evalElQtr evp evRhs)
        evRhs
        compEq
    mkLeftCanon dEq dLeft evp body@(compTmClosedQtr _ compTy evTy evRhs corrRhs compx) =
      let
        lhsCorr = transTm dEq corrRhs
        lhsComp =
          compTmClosedQtr
            dLeft
            compTy
            evTy
            (evalElQtr evp evRhs)
            lhsCorr
            compx
      in
      compTmEqClosedQtr
        dEq
        lhsComp
        body
        evTy
        (evalElQtr evp evRhs)
        evRhs
        compx
        compx
  
    mkRightCanon :
      Derivable
        (termEq []
          (tmElQtr l' p')
          (subTm (qtrCompSub qtrTmEqRightRepr) l')
          (subTy (singleSubst p) L))
      -> Derivable (hasTy [] (tmElQtr l' p') (subTy (singleSubst p) L))
      -> p' =>e tmClass qtrTmEqRightRepr
      -> Computable
           (hasTy []
             (subTm (qtrCompSub qtrTmEqRightRepr) l')
             (subTy (singleSubst p) L))
      -> Computable
           (termEq []
             (tmElQtr l' p')
             (subTm (qtrCompSub qtrTmEqRightRepr) l')
             (subTy (singleSubst p) L))
    mkRightCanon dEq dLeft evp body@(compTmClosedTop _ compTy evTy evRhs corrRhs) =
      let
        lhsCorr = transTm dEq corrRhs
        lhsComp =
          compTmClosedTop
            dLeft
            compTy
            evTy
            (evalElQtr evp evRhs)
            lhsCorr
      in
      compTmEqClosedTop dEq lhsComp body evTy (evalElQtr evp evRhs) evRhs
    mkRightCanon dEq dLeft evp body@(compTmClosedSigma _ compTy evTy evRhs corrRhs comp₁ comp₂) =
      let
        lhsCorr = transTm dEq corrRhs
        lhsComp =
          compTmClosedSigma
            dLeft
            compTy
            evTy
            (evalElQtr evp evRhs)
            lhsCorr
            comp₁
            comp₂
      in
      compTmEqClosedSigma
        dEq
        lhsComp
        body
        evTy
        (evalElQtr evp evRhs)
        evRhs
        (compReflTmClosed comp₁)
        (compReflTmClosed comp₂)
    mkRightCanon dEq dLeft evp body@(compTmClosedEq _ compTy evTy evRhs corrRhs compEq) =
      let
        lhsCorr = transTm dEq corrRhs
        lhsComp =
          compTmClosedEq
            dLeft
            compTy
            evTy
            (evalElQtr evp evRhs)
            lhsCorr
            compEq
      in
      compTmEqClosedEq
        dEq
        lhsComp
        body
        evTy
        (evalElQtr evp evRhs)
        evRhs
        compEq
    mkRightCanon dEq dLeft evp body@(compTmClosedQtr _ compTy evTy evRhs corrRhs compx) =
      let
        lhsCorr = transTm dEq corrRhs
        lhsComp =
          compTmClosedQtr
            dLeft
            compTy
            evTy
            (evalElQtr evp evRhs)
            lhsCorr
            compx
      in
      compTmEqClosedQtr
        dEq
        lhsComp
        body
        evTy
        (evalElQtr evp evRhs)
        evRhs
        compx
        compx
  
    leftCan : Computable
      (termEq []
        (tmElQtr l p)
        (subTm (qtrCompSub qtrTmEqLeftRepr) l)
        (subTy (singleSubst p) L))
    leftCan = mkLeftCanon dLeftEq dLeftTy qtrTmEqEvalLeftClass bodyLeft
  
    rightCan : Computable
      (termEq []
        (tmElQtr l' p')
        (subTm (qtrCompSub qtrTmEqRightRepr) l')
        (subTy (singleSubst p) L))
    rightCan = mkRightCanon dRightEq dRightTy qtrTmEqEvalRightClass bodyRight
  
  subSubJIntoPath : {theta gamma delta : Ctx} {rho sigma : Subst} {J : JForm}
    -> subJInto theta rho (subJInto gamma sigma J) ≡ subJInto theta (compSub rho sigma) J
  subSubJIntoPath {J = isType delta A} =
    cong (isType _) (subTyComp _ _ A)
  subSubJIntoPath {J = typeEq delta A B} =
    cong₂ (typeEq _)
      (subTyComp _ _ A)
      (subTyComp _ _ B)
  subSubJIntoPath {J = hasTy delta t A} =
    cong₂ (hasTy _)
      (subTmComp _ _ t)
      (subTyComp _ _ A)
  subSubJIntoPath {J = termEq delta t u A} =
    cong₃ (termEq _)
      (subTmComp _ _ t)
      (subTmComp _ _ u)
      (subTyComp _ _ A)
  
  subEqJIntoPath : {theta gamma delta : Ctx} {rho sigma tau : Subst} {J : JForm}
    -> subJInto theta rho (eqSubJInto gamma sigma tau J)
     ≡ eqSubJInto theta (compSub rho sigma) (compSub rho tau) J
  subEqJIntoPath {J = isType delta A} =
    cong₂ (typeEq _)
      (subTyComp _ _ A)
      (subTyComp _ _ A)
  subEqJIntoPath {J = typeEq delta A B} =
    cong₂ (typeEq _)
      (subTyComp _ _ A)
      (subTyComp _ _ B)
  subEqJIntoPath {J = hasTy delta t A} =
    cong₃ (termEq _)
      (subTmComp _ _ t)
      (subTmComp _ _ t)
      (subTyComp _ _ A)
  subEqJIntoPath {J = termEq delta t u A} =
    cong₃ (termEq _)
      (subTmComp _ _ t)
      (subTmComp _ _ u)
      (subTyComp _ _ A)
  
  eqSubSubJIntoPath : {theta gamma delta : Ctx} {rho eta sigma : Subst} {J : JForm}
    -> eqSubJInto theta rho eta (subJInto gamma sigma J)
     ≡ eqSubJInto theta (compSub rho sigma) (compSub eta sigma) J
  eqSubSubJIntoPath {J = isType delta A} =
    cong₂ (typeEq _)
      (subTyComp _ _ A)
      (subTyComp _ _ A)
  eqSubSubJIntoPath {J = typeEq delta A B} =
    cong₂ (typeEq _)
      (subTyComp _ _ A)
      (subTyComp _ _ B)
  eqSubSubJIntoPath {J = hasTy delta t A} =
    cong₃ (termEq _)
      (subTmComp _ _ t)
      (subTmComp _ _ t)
      (subTyComp _ _ A)
  eqSubSubJIntoPath {J = termEq delta t u A} =
    cong₃ (termEq _)
      (subTmComp _ _ t)
      (subTmComp _ _ u)
      (subTyComp _ _ A)
  
  eqSubEqJIntoPath : {theta gamma delta : Ctx} {rho eta sigma tau : Subst} {J : JForm}
    -> eqSubJInto theta rho eta (eqSubJInto gamma sigma tau J)
     ≡ eqSubJInto theta (compSub rho sigma) (compSub eta tau) J
  eqSubEqJIntoPath {J = isType delta A} =
    cong₂ (typeEq _)
      (subTyComp _ _ A)
      (subTyComp _ _ A)
  eqSubEqJIntoPath {J = typeEq delta A B} =
    cong₂ (typeEq _)
      (subTyComp _ _ A)
      (subTyComp _ _ B)
  eqSubEqJIntoPath {J = hasTy delta t A} =
    cong₃ (termEq _)
      (subTmComp _ _ t)
      (subTmComp _ _ t)
      (subTyComp _ _ A)
  eqSubEqJIntoPath {J = termEq delta t u A} =
    cong₃ (termEq _)
      (subTmComp _ _ t)
      (subTmComp _ _ u)
      (subTyComp _ _ A)
  
  wkJKeepPath : {delta : Ctx} {J : JForm}
    -> subJInto (delta ++ ctxOf J) (keepSubstBy (length delta)) J ≡ wkJBy delta J
  wkJKeepPath {delta = delta} {J = isType gamma A} =
    cong (isType _) (sym (renTyKeepSubstBy (length delta) A))
  wkJKeepPath {delta = delta} {J = typeEq gamma A B} =
    cong₂ (typeEq _)
      (sym (renTyKeepSubstBy (length delta) A))
      (sym (renTyKeepSubstBy (length delta) B))
  wkJKeepPath {delta = delta} {J = hasTy gamma t A} =
    cong₂ (hasTy _)
      (sym (renTmKeepSubstBy (length delta) t))
      (sym (renTyKeepSubstBy (length delta) A))
  wkJKeepPath {delta = delta} {J = termEq gamma t u A} =
    cong₃ (termEq _)
      (sym (renTmKeepSubstBy (length delta) t))
      (sym (renTmKeepSubstBy (length delta) u))
      (sym (renTyKeepSubstBy (length delta) A))
  
  compSubKeepBy : (sigma : Subst) (k : ℕ)
    -> compSub sigma (keepSubstBy k) ≡ dropSubstBy k sigma
  compSubKeepBy sigma k = funExt λ n -> refl
  
  subTyWkBy : (sigma : Subst) (k : ℕ) (A : RawType)
    -> subTy sigma (wkTyBy k A) ≡ subTy (dropSubstBy k sigma) A
  subTyWkBy sigma k A =
    cong (subTy sigma) (renTyKeepSubstBy k A)
    ∙ subTyComp sigma (keepSubstBy k) A
    ∙ cong (λ rho -> subTy rho A) (compSubKeepBy sigma k)
  
  subTmWkBy : (sigma : Subst) (k : ℕ) (t : RawTerm)
    -> subTm sigma (wkTmBy k t) ≡ subTm (dropSubstBy k sigma) t
  subTmWkBy sigma k t =
    cong (subTm sigma) (renTmKeepSubstBy k t)
    ∙ subTmComp sigma (keepSubstBy k) t
    ∙ cong (λ rho -> subTm rho t) (compSubKeepBy sigma k)
  
  wkTyBy0 : (A : RawType) -> wkTyBy 0 A ≡ A
  wkTyBy0 A =
    renTyKeepSubstBy 0 A
    ∙ cong (λ sigma -> subTy sigma A) keepSubstBy0Id
    ∙ subTyId A
  
  wkTmBy0 : (t : RawTerm) -> wkTmBy 0 t ≡ t
  wkTmBy0 t =
    renTmKeepSubstBy 0 t
    ∙ cong (λ sigma -> subTm sigma t) keepSubstBy0Id
    ∙ subTmId t
  
  dropCons : (t : RawTerm) (sigma : Subst) (k : ℕ)
    -> dropSubstBy (suc k) (consSubst t sigma) ≡ dropSubstBy k sigma
  dropCons t sigma k = funExt λ n -> refl
  
  subTyWkStep : (t : RawTerm) (sigma : Subst) (k : ℕ) (A : RawType)
    -> subTy (consSubst t sigma) (wkTyBy (suc k) A)
     ≡ subTy sigma (wkTyBy k A)
  subTyWkStep t sigma k A =
    subTyWkBy (consSubst t sigma) (suc k) A
    ∙ cong (λ rho -> subTy rho A) (dropCons t sigma k)
    ∙ sym (subTyWkBy sigma k A)
  
  lookupVarFits : {delta gamma : Ctx} {A : RawType} {sigma : Subst}
    -> FitsSubst [] (delta ++ (A ∷ gamma)) sigma
    -> Derivable
         (hasTy [] (subTm sigma (var (length delta)))
           (subTy sigma (wkTyBy (suc (length delta)) A)))
  lookupVarFits {delta = []} {A = A}
    (fitsCons {sigma = sigma} {t = t} fits dt) =
    subst
      (λ T -> Derivable (hasTy [] t T))
      (sym (subTyWkStep t sigma 0 A ∙ cong (subTy sigma) (wkTyBy0 A)))
      dt
  lookupVarFits {delta = D ∷ delta} {A = A}
    (fitsCons {sigma = sigma} {t = t} fits dt) =
    subst
      (λ T -> Derivable (hasTy [] (subTm sigma (var (length delta))) T))
      (sym (subTyWkStep t sigma (suc (length delta)) A))
      (lookupVarFits {delta = delta} {A = A} {sigma = sigma} fits)
  
  lookupVarFitsEq : {delta gamma : Ctx} {A : RawType} {sigma tau : Subst}
    -> FitsEqSubst [] (delta ++ (A ∷ gamma)) sigma tau
    -> Derivable
         (termEq [] (subTm sigma (var (length delta))) (subTm tau (var (length delta)))
           (subTy sigma (wkTyBy (suc (length delta)) A)))
  lookupVarFitsEq {delta = []} {A = A}
    (fitsEqCons {sigma = sigma} {tau = tau} {t = t} {u = u} fitsEq dtu) =
    subst
      (λ T -> Derivable (termEq [] t u T))
      (sym (subTyWkStep t sigma 0 A ∙ cong (subTy sigma) (wkTyBy0 A)))
      dtu
  lookupVarFitsEq {delta = D ∷ delta} {A = A}
    (fitsEqCons {sigma = sigma} {tau = tau} {t = t} {u = u} fitsEq dtu) =
    subst
      (λ T ->
        Derivable
          (termEq [] (subTm sigma (var (length delta))) (subTm tau (var (length delta))) T))
      (sym (subTyWkStep t sigma (suc (length delta)) A))
      (lookupVarFitsEq {delta = delta} {A = A} {sigma = sigma} {tau = tau} fitsEq)
  
  dropFits : {delta : Ctx} {sigma : Subst}
    -> (drop : Ctx)
    -> FitsSubst [] (drop ++ delta) sigma
    -> FitsSubst [] delta (dropSubstBy (length drop) sigma)
  dropFits {delta = delta} {sigma = sigma} [] fits = fits
  dropFits {delta = delta} {sigma = sigma} (A ∷ drop)
    (fitsCons {sigma = sigmaTail} {t = t} fits dt) =
    subst
      (λ rho -> FitsSubst [] delta rho)
      (dropCons t sigmaTail (length drop))
      (dropFits {delta = delta} {sigma = sigmaTail} drop fits)
  
  dropFitsEq : {delta : Ctx} {sigma tau : Subst}
    -> (drop : Ctx)
    -> FitsEqSubst [] (drop ++ delta) sigma tau
    -> FitsEqSubst [] delta (dropSubstBy (length drop) sigma) (dropSubstBy (length drop) tau)
  dropFitsEq {delta = delta} {sigma = sigma} {tau = tau} [] fitsEq = fitsEq
  dropFitsEq {delta = delta} {sigma = sigma} {tau = tau} (A ∷ drop)
    (fitsEqCons {sigma = sigmaTail} {tau = tauTail} {t = t} {u = u} fitsEq dtu) =
    subst
      (λ rho ->
        FitsEqSubst [] delta rho
          (dropSubstBy (suc (length drop)) (consSubst u tauTail)))
      (dropCons t sigmaTail (length drop))
      (subst
        (λ rho ->
          FitsEqSubst [] delta
            (dropSubstBy (suc (length drop)) (consSubst t sigmaTail))
            rho)
        (dropCons u tauTail (length drop))
        (dropFitsEq {delta = delta} {sigma = sigmaTail} {tau = tauTail} drop fitsEq))
  
  closedEqSubTy : {gamma : Ctx} {A : RawType} {sigma tau : Subst}
    -> Derivable (isType [] A)
    -> CtxWF gamma
    -> Derivable (typeEq gamma (subTy sigma A) (subTy tau A))
  closedEqSubTy {gamma = gamma} {sigma = sigma} {tau = tau} dA wf =
    eqSubTyRule dA
      (fitsEqNil {gamma = gamma} {delta = []} {sigma = sigma} {tau = tau} wf)
  
  closedEqSubTyEq : {gamma : Ctx} {A B : RawType} {sigma tau : Subst}
    -> Derivable (typeEq [] A B)
    -> CtxWF gamma
    -> Derivable (typeEq gamma (subTy sigma A) (subTy tau B))
  closedEqSubTyEq {gamma = gamma} {sigma = sigma} {tau = tau} dAB wf =
    eqSubTyEqRule dAB
      (fitsEqNil {gamma = gamma} {delta = []} {sigma = sigma} {tau = tau} wf)
  
  closedEqSubTm : {gamma : Ctx} {t : RawTerm} {A : RawType} {sigma tau : Subst}
    -> Derivable (hasTy [] t A)
    -> CtxWF gamma
    -> Derivable (termEq gamma (subTm sigma t) (subTm tau t) (subTy sigma A))
  closedEqSubTm {gamma = gamma} {sigma = sigma} {tau = tau} dt wf =
    eqSubTmRule dt
      (fitsEqNil {gamma = gamma} {delta = []} {sigma = sigma} {tau = tau} wf)
  
  closedEqSubTmEq : {gamma : Ctx} {t u : RawTerm} {A : RawType} {sigma tau : Subst}
    -> Derivable (termEq [] t u A)
    -> CtxWF gamma
    -> Derivable (termEq gamma (subTm sigma t) (subTm tau u) (subTy sigma A))
  closedEqSubTmEq {gamma = gamma} {sigma = sigma} {tau = tau} dtu wf =
    eqSubTmEqRule dtu
      (fitsEqNil {gamma = gamma} {delta = []} {sigma = sigma} {tau = tau} wf)
  
  liftFits : {theta gamma : Ctx} {A : RawType} {sigma : Subst}
    -> FitsSubst theta gamma sigma
    -> Derivable (isType theta (subTy sigma A))
    -> FitsSubst (subTy sigma A ∷ theta) (A ∷ gamma)
         (consSubst (var zero) (compSub (keepSubstBy 1) sigma))
  liftFits {theta = theta} {gamma = gamma} {A = A} {sigma = sigma} fits dAσ =
    fitsCons tail headVar
    where
    wfAσ : CtxWF (subTy sigma A ∷ theta)
    wfAσ = wfCons (fitsSubstCtxWF fits) dAσ
  
    tail : FitsSubst (subTy sigma A ∷ theta) gamma (compSub (keepSubstBy 1) sigma)
    tail =
      composeFits
        (fitsKeep {delta = subTy sigma A ∷ []} {gamma = theta} wfAσ)
        fits
  
    headVar0 : Derivable
      (hasTy (subTy sigma A ∷ theta) (var zero) (wkTyBy 1 (subTy sigma A)))
    headVar0 = varStar {gamma = theta} {delta = []} {A = subTy sigma A} wfAσ dAσ
  
    headVar : Derivable
      (hasTy (subTy sigma A ∷ theta) (var zero) (subTy (compSub (keepSubstBy 1) sigma) A))
    headVar =
      subst
        (λ T -> Derivable (hasTy (subTy sigma A ∷ theta) (var zero) T))
        (renTyKeepSubstBy 1 (subTy sigma A) ∙ subTyComp (keepSubstBy 1) sigma A)
        headVar0
  
  liftFitsOne : {gamma : Ctx} {A : RawType} {sigma : Subst}
    -> FitsSubst [] gamma sigma
    -> Derivable (isType [] (subTy sigma A))
    -> FitsSubst (subTy sigma A ∷ []) (A ∷ gamma)
         (consSubst (var zero) (compSub (keepSubstBy 1) sigma))
  liftFitsOne = liftFits
  
  liftFitsEq : {theta gamma : Ctx} {A : RawType} {sigma tau : Subst}
    -> FitsEqSubst theta gamma sigma tau
    -> Derivable (isType theta (subTy sigma A))
    -> FitsEqSubst (subTy sigma A ∷ theta) (A ∷ gamma)
         (consSubst (var zero) (compSub (keepSubstBy 1) sigma))
         (consSubst (var zero) (compSub (keepSubstBy 1) tau))
  liftFitsEq {theta = theta} {gamma = gamma} {A = A} {sigma = sigma} {tau = tau} fitsEq dAσ =
    fitsEqCons tail (reflTm headVar)
    where
    wfAσ : CtxWF (subTy sigma A ∷ theta)
    wfAσ = wfCons (fitsEqSubstCtxWF fitsEq) dAσ
  
    tail : FitsEqSubst (subTy sigma A ∷ theta) gamma
      (compSub (keepSubstBy 1) sigma)
      (compSub (keepSubstBy 1) tau)
    tail =
      composeFitsEq
        (fitsKeep {delta = subTy sigma A ∷ []} {gamma = theta} wfAσ)
        fitsEq
  
    headVar0 : Derivable
      (hasTy (subTy sigma A ∷ theta) (var zero) (wkTyBy 1 (subTy sigma A)))
    headVar0 = varStar {gamma = theta} {delta = []} {A = subTy sigma A} wfAσ dAσ
  
    headVar : Derivable
      (hasTy (subTy sigma A ∷ theta) (var zero) (subTy (compSub (keepSubstBy 1) sigma) A))
    headVar =
      subst
        (λ T -> Derivable (hasTy (subTy sigma A ∷ theta) (var zero) T))
        (renTyKeepSubstBy 1 (subTy sigma A) ∙ subTyComp (keepSubstBy 1) sigma A)
        headVar0
  
  liftFitsEqOne : {gamma : Ctx} {A : RawType} {sigma tau : Subst}
    -> FitsEqSubst [] gamma sigma tau
    -> Derivable (isType [] (subTy sigma A))
    -> FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma)
         (consSubst (var zero) (compSub (keepSubstBy 1) sigma))
         (consSubst (var zero) (compSub (keepSubstBy 1) tau))
  liftFitsEqOne = liftFitsEq
  
  liftSubstCompKeep : (sigma : Subst)
    -> consSubst (var zero) (compSub (keepSubstBy 1) sigma) ≡ liftSubst sigma
  liftSubstCompKeep sigma = funExt λ where
    zero -> refl
    (suc n) -> sym (renTmKeepSubstBy 1 (sigma n))
  
  reflFitsEq : {gamma delta : Ctx} {sigma : Subst}
    -> FitsSubst gamma delta sigma
    -> FitsEqSubst gamma delta sigma sigma
  reflFitsEq {gamma = gamma} {sigma = sigma} (fitsNil wf) =
    fitsEqNil {gamma = gamma} {delta = []} {sigma = sigma} {tau = sigma} wf
  reflFitsEq (fitsCons fits dt) =
    fitsEqCons (reflFitsEq fits) (reflTm dt)
  
  compSubIdLeft : (sigma : Subst) -> compSub idSubst sigma ≡ sigma
  compSubIdLeft sigma = funExt λ n -> subTmId (sigma n)
  
  oneBinderCompSub : (tau sigma : Subst)
    -> consSubst (tau zero) (compSub (dropSubstBy 1 tau) sigma) ≡ compSub tau (liftSubst sigma)
  oneBinderCompSub tau sigma = funExt λ where
    zero -> refl
    (suc n) -> sym (subTmRen tau suc (sigma n))
  
  twoBinderCompSub : (tau sigma : Subst)
    -> consSubst (tau zero) (consSubst (tau (suc zero)) (compSub (dropSubstBy 2 tau) sigma))
         ≡ compSub tau (liftSubst (liftSubst sigma))
  twoBinderCompSub tau sigma = funExt λ where
    zero -> refl
    (suc zero) -> refl
    (suc (suc n)) ->
      sym
        (cong (subTm tau) (renTmComp suc suc (sigma n))
          ∙ subTmRen tau (compRen suc suc) (sigma n))
  
  composeOneBinder : {gamma : Ctx} {A : RawType} {sigma tau : Subst}
    -> FitsSubst [] gamma sigma
    -> Derivable (isType [] (subTy sigma A))
    -> FitsSubst [] (subTy sigma A ∷ []) tau
    -> FitsSubst [] (A ∷ gamma) (compSub tau (liftSubst sigma))
  composeOneBinder {gamma = gamma} {A = A} {sigma = sigma} {tau = tau} fits dAσ fits2 =
    subst
      (λ rho -> FitsSubst [] (A ∷ gamma) rho)
      (cong (compSub tau) (liftSubstCompKeep sigma))
      (composeFits fits2 (liftFitsOne fits dAσ))
  
  composeOneBinderEq : {gamma : Ctx} {A : RawType} {sigma tau₁ tau₂ : Subst}
    -> FitsSubst [] gamma sigma
    -> Derivable (isType [] (subTy sigma A))
    -> FitsEqSubst [] (subTy sigma A ∷ []) tau₁ tau₂
    -> FitsEqSubst [] (A ∷ gamma) (compSub tau₁ (liftSubst sigma)) (compSub tau₂ (liftSubst sigma))
  composeOneBinderEq {gamma = gamma} {A = A} {sigma = sigma} {tau₁ = tau₁} {tau₂ = tau₂} fits dAσ fitsEq =
    subst
      (λ rho -> FitsEqSubst [] (A ∷ gamma) rho (compSub tau₂ (liftSubst sigma)))
      (cong (compSub tau₁) (liftSubstCompKeep sigma))
      (subst
        (λ rho ->
          FitsEqSubst [] (A ∷ gamma)
            (compSub tau₁ (consSubst (var zero) (compSub (keepSubstBy 1) sigma)))
            rho)
        (cong (compSub tau₂) (liftSubstCompKeep sigma))
        (composeEqFits fitsEq (liftFitsOne fits dAσ)))
  
  composeTwoBinders : {gamma : Ctx} {A B : RawType} {sigma tau : Subst}
    -> FitsSubst [] gamma sigma
    -> Derivable (isType [] (subTy sigma A))
    -> Derivable (isType (subTy sigma A ∷ []) (subTy (liftSubst sigma) B))
    -> FitsSubst [] (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) tau
    -> FitsSubst [] (B ∷ A ∷ gamma) (compSub tau (liftSubst (liftSubst sigma)))
  composeTwoBinders {gamma = gamma} {A = A} {B = B} {sigma = sigma} {tau = tau} fits dAσ dBσ fits2 =
    let
      lifted1 : FitsSubst (subTy sigma A ∷ []) (A ∷ gamma) (liftSubst sigma)
      lifted1 =
        subst
          (λ rho -> FitsSubst (subTy sigma A ∷ []) (A ∷ gamma) rho)
          (liftSubstCompKeep sigma)
          (liftFitsOne fits dAσ)
    in
    subst
      (λ rho -> FitsSubst [] (B ∷ A ∷ gamma) rho)
      (cong (compSub tau) (liftSubstCompKeep (liftSubst sigma)))
      (composeFits fits2 (liftFits lifted1 dBσ))
  
  composeTwoBindersEq : {gamma : Ctx} {A B : RawType} {sigma tau₁ tau₂ : Subst}
    -> FitsSubst [] gamma sigma
    -> Derivable (isType [] (subTy sigma A))
    -> Derivable (isType (subTy sigma A ∷ []) (subTy (liftSubst sigma) B))
    -> FitsEqSubst [] (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) tau₁ tau₂
    -> FitsEqSubst [] (B ∷ A ∷ gamma)
         (compSub tau₁ (liftSubst (liftSubst sigma)))
         (compSub tau₂ (liftSubst (liftSubst sigma)))
  composeTwoBindersEq {gamma = gamma} {A = A} {B = B} {sigma = sigma} {tau₁ = tau₁} {tau₂ = tau₂} fits dAσ dBσ fitsEq =
    let
      lifted1 : FitsSubst (subTy sigma A ∷ []) (A ∷ gamma) (liftSubst sigma)
      lifted1 =
        subst
          (λ rho -> FitsSubst (subTy sigma A ∷ []) (A ∷ gamma) rho)
          (liftSubstCompKeep sigma)
          (liftFitsOne fits dAσ)
    in
    subst
      (λ rho ->
        FitsEqSubst [] (B ∷ A ∷ gamma) rho (compSub tau₂ (liftSubst (liftSubst sigma))))
      (cong (compSub tau₁) (liftSubstCompKeep (liftSubst sigma)))
      (subst
        (λ rho ->
          FitsEqSubst [] (B ∷ A ∷ gamma)
            (compSub tau₁ (consSubst (var zero) (compSub (keepSubstBy 1) (liftSubst sigma))))
            rho)
        (cong (compSub tau₂) (liftSubstCompKeep (liftSubst sigma)))
        (composeEqFits fitsEq (liftFits lifted1 dBσ)))
  
  singleSubstCompLift : (sigma : Subst) (t : RawTerm)
    -> compSub (singleSubst (subTm sigma t)) (liftSubst sigma) ≡ compSub sigma (singleSubst t)
  singleSubstCompLift sigma t = funExt λ where
    zero -> refl
    (suc n) ->
      subTmRen (singleSubst (subTm sigma t)) suc (sigma n)
      ∙ cong (λ rho -> subTm rho (sigma n)) (funExt λ k -> refl)
      ∙ subTmId (sigma n)
  
  qtrBranchSubLiftComp : (sigma : Subst)
    -> compSub (liftSubst sigma) qtrBranchSub ≡ compSub qtrBranchSub (liftSubst sigma)
  qtrBranchSubLiftComp sigma = funExt λ where
    zero -> refl
    (suc n) ->
      sym (subTmId (renTm suc (sigma n)))
      ∙ subTmRen idSubst suc (sigma n)
      ∙ cong (λ rho -> subTm rho (sigma n)) (sym (funExt λ k -> refl))
      ∙ sym (subTmRen qtrBranchSub suc (sigma n))
  
  sigmaCompSubLiftComp : (sigma : Subst) (b c : RawTerm)
    -> compSub sigma (sigmaCompSub b c)
     ≡ compSub (sigmaCompSub (subTm sigma b) (subTm sigma c)) (liftSubst (liftSubst sigma))
  sigmaCompSubLiftComp sigma b c = funExt λ where
    zero -> refl
    (suc zero) -> refl
    (suc (suc n)) ->
      sym (subTmId (sigma n))
      ∙ cong
          (λ rho -> subTm rho (sigma n))
          (sym (funExt λ k -> refl))
      ∙ sym (subTmRen (sigmaCompSub (subTm sigma b) (subTm sigma c)) (compRen suc suc) (sigma n))
      ∙ cong
          (λ t -> subTm (sigmaCompSub (subTm sigma b) (subTm sigma c)) t)
          (sym (renTmComp suc suc (sigma n)))
  
  sigmaMotSubLiftComp : (sigma : Subst)
    -> compSub (liftSubst (liftSubst sigma)) sigmaMotSub ≡ compSub sigmaMotSub (liftSubst sigma)
  sigmaMotSubLiftComp sigma = funExt λ where
    zero -> refl
    (suc n) ->
      renTmComp suc suc (sigma n)
      ∙ sym (subTmId (renTm (addRen 2) (sigma n)))
      ∙ subTmRen idSubst (addRen 2) (sigma n)
      ∙ sym (subTmRen sigmaMotSub suc (sigma n))
  
  qtrCohSubLiftComp : (sigma : Subst)
    -> compSub (liftSubst (liftSubst sigma)) qtrCohSub ≡ compSub qtrCohSub (liftSubst sigma)
  qtrCohSubLiftComp sigma = funExt λ where
    zero -> refl
    (suc n) ->
      renTmComp suc suc (sigma n)
      ∙ sym (subTmId (renTm (addRen 2) (sigma n)))
      ∙ subTmRen idSubst (addRen 2) (sigma n)
      ∙ sym (subTmRen qtrCohSub suc (sigma n))
  
  sigmaBranchTyLiftComp : (sigma : Subst) (M : RawType)
    -> subTy (liftSubst (liftSubst sigma)) (sigmaBranchTy M)
         ≡ sigmaBranchTy (subTy (liftSubst sigma) M)
  sigmaBranchTyLiftComp sigma M =
    subTyComp (liftSubst (liftSubst sigma)) sigmaMotSub M
    ∙ cong (λ rho -> subTy rho M) (sigmaMotSubLiftComp sigma)
    ∙ sym (subTyComp sigmaMotSub (liftSubst sigma) M)
  
  qtrBranchTyLiftComp : (sigma : Subst) (L : RawType)
    -> subTy (liftSubst sigma) (qtrBranchTy L)
         ≡ qtrBranchTy (subTy (liftSubst sigma) L)
  qtrBranchTyLiftComp sigma L =
    subTyComp (liftSubst sigma) qtrBranchSub L
    ∙ cong (λ rho -> subTy rho L) (qtrBranchSubLiftComp sigma)
    ∙ sym (subTyComp qtrBranchSub (liftSubst sigma) L)
  
  qtrCohTyLiftComp : (sigma : Subst) (L : RawType)
    -> subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)
         ≡ qtrCohTy (subTy (liftSubst sigma) L)
  qtrCohTyLiftComp sigma L =
    subTyComp (liftSubst (liftSubst sigma)) qtrCohSub L
    ∙ cong (λ rho -> subTy rho L) (qtrCohSubLiftComp sigma)
    ∙ sym (subTyComp qtrCohSub (liftSubst sigma) L)
  
  qtrSecondBranchRenPath : qtrSecondBranchRen ≡ raiseRen suc
  qtrSecondBranchRenPath = funExt λ where
    zero -> refl
    (suc n) -> refl
  
  qtrSecondBranchSubLiftComp : (sigma : Subst)
    -> (λ n -> liftSubst (liftSubst sigma) (qtrSecondBranchRen n))
         ≡ renSub qtrSecondBranchRen (liftSubst sigma)
  qtrSecondBranchSubLiftComp sigma = funExt λ where
    zero -> refl
    (suc n) ->
      renTmComp suc suc (sigma n)
      ∙ cong
          (λ rho -> renTm rho (sigma n))
          (funExt λ where
            zero -> refl
            (suc k) -> refl)
      ∙ sym (renTmComp qtrSecondBranchRen suc (sigma n))
  
  qtrSecondBranchTmLiftComp : (sigma : Subst) (l : RawTerm)
    -> subTm (liftSubst (liftSubst sigma)) (renTm qtrSecondBranchRen l)
         ≡ renTm qtrSecondBranchRen (subTm (liftSubst sigma) l)
  qtrSecondBranchTmLiftComp sigma l =
    subTmRen (liftSubst (liftSubst sigma)) qtrSecondBranchRen l
    ∙ cong
        (λ theta -> subTm theta l)
        (qtrSecondBranchSubLiftComp sigma)
    ∙ sym (renTmSub qtrSecondBranchRen (liftSubst sigma) l)
  
  qtrCompSubLiftComp : (sigma : Subst) (a : RawTerm)
    -> compSub sigma (qtrCompSub a)
         ≡ compSub (qtrCompSub (subTm sigma a)) (liftSubst sigma)
  qtrCompSubLiftComp sigma a =
    cong
      (compSub sigma)
      (sym (singleSubstConsKeep a ∙ cong (consSubst a) keepSubstBy0Id))
    ∙ sym (singleSubstCompLift sigma a)
    ∙ cong
        (λ rho -> compSub rho (liftSubst sigma))
        (singleSubstConsKeep (subTm sigma a)
          ∙ cong (consSubst (subTm sigma a)) keepSubstBy0Id)
  
  qtrBranchTyWk : (L : RawType)
    -> wkTyBy 1 (qtrBranchTy L) ≡ qtrCohTy L
  qtrBranchTyWk L =
    renTySub suc qtrBranchSub L
    ∙ cong
        (λ rho -> subTy rho L)
        (funExt λ where
          zero -> refl
          (suc n) -> refl)
  
  substSccTyEq1 : {gamma : Ctx} {A B C : RawType} {sigma : Subst}
    -> ({gamma : Ctx} {A B : RawType} {sigma : Subst}
         -> FitsSubst [] gamma sigma
         -> Derivable (isType [] (subTy sigma A))
         -> Derivable (isType (A ∷ gamma) B)
         -> HypComputable (isType (subTy sigma A ∷ []) (subTy (liftSubst sigma) B)))
    -> ({gamma : Ctx} {A B : RawType} {sigma : Subst}
         -> Derivable (typeEq gamma A B)
         -> FitsSubst [] gamma sigma
         -> Computable (typeEq [] (subTy sigma A) (subTy sigma B)))
    -> ({gamma : Ctx} {A B : RawType} {sigma tau : Subst}
         -> Derivable (typeEq gamma A B)
         -> FitsEqSubst [] gamma sigma tau
         -> Computable (typeEq [] (subTy sigma A) (subTy tau B)))
    -> FitsSubst [] gamma sigma
    -> Derivable (isType [] (subTy sigma A))
    -> Derivable (typeEq (A ∷ gamma) B C)
    -> HypComputable
         (typeEq (subTy sigma A ∷ [])
           (subTy (liftSubst sigma) B)
           (subTy (liftSubst sigma) C))
  substSccTyEq1 {A = A} {B = B} {C = C} {sigma = sigma}
    sccTy1Cl subTyEqCl eqSubTyEqCl fits dAσ dBC =
    subst
      (λ J -> HypComputable J)
      (cong₂
        (typeEq (subTy sigma A ∷ []))
        (cong (λ rho -> subTy rho B) (liftSubstCompKeep sigma))
        (cong (λ rho -> subTy rho C) (liftSubstCompKeep sigma)))
      (hypTyEqOpen
        nonemptyNeNil
        (substTyEqRule dBC (liftFitsOne fits dAσ))
        (subst
          (λ T -> HypComputable (isType (subTy sigma A ∷ []) T))
          (sym (cong (λ rho -> subTy rho B) (liftSubstCompKeep sigma)))
          (sccTy1Cl fits dAσ (assocTyLeft dBC)))
        (λ tau fits2 _ ->
          subst
            (λ J -> Computable J)
            (sym
              (cong₂ (typeEq [])
                (cong (λ rho -> subTy tau (subTy rho B)) (liftSubstCompKeep sigma)
                  ∙ subTyComp tau (liftSubst sigma) B)
                (cong (λ rho -> subTy tau (subTy rho C)) (liftSubstCompKeep sigma)
                  ∙ subTyComp tau (liftSubst sigma) C)))
            (subTyEqCl
              dBC
              (composeOneBinder fits dAσ fits2)))
        (λ tau₁ tau₂ fitsEq2 _ ->
          subst
            (λ J -> Computable J)
            (sym
              (cong₂ (typeEq [])
                (cong (λ rho -> subTy tau₁ (subTy rho B)) (liftSubstCompKeep sigma)
                  ∙ subTyComp tau₁ (liftSubst sigma) B)
                (cong (λ rho -> subTy tau₂ (subTy rho C)) (liftSubstCompKeep sigma)
                  ∙ subTyComp tau₂ (liftSubst sigma) C)))
            (eqSubTyEqCl
              dBC
              (composeOneBinderEq fits dAσ fitsEq2))))

  eqSubSccTy1 : {gamma : Ctx} {A B : RawType} {sigma tau : Subst}
    -> ({gamma : Ctx} {A B : RawType} {sigma : Subst}
         -> FitsSubst [] gamma sigma
         -> Derivable (isType [] (subTy sigma A))
         -> Derivable (isType (A ∷ gamma) B)
         -> HypComputable
              (isType (subTy sigma A ∷ [])
                (subTy (liftSubst sigma) B)))
    -> ({gamma : Ctx} {A : RawType} {sigma tau : Subst}
         -> Derivable (isType gamma A)
         -> FitsEqSubst [] gamma sigma tau
         -> Computable (typeEq [] (subTy sigma A) (subTy tau A)))
    -> FitsEqSubst [] gamma sigma tau
    -> Derivable (isType [] (subTy sigma A))
    -> Derivable (isType (A ∷ gamma) B)
    -> HypComputable (typeEq (subTy sigma A ∷ []) (subTy (liftSubst sigma) B) (subTy (liftSubst tau) B))
  eqSubSccTy1 {gamma = gamma} {A = A} {B = B} {sigma = sigma} {tau = tau}
    sccTy1Cl eqSubTyCl fitsEq dAσ dB =
    let
      sigmaFits = fitsEqSubstLeft fitsEq
      liftedEq :
        FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma)
          (liftSubst sigma)
          (liftSubst tau)
      liftedEq =
        subst
          (λ rho -> FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma) rho (liftSubst tau))
          (liftSubstCompKeep sigma)
          (subst
            (λ rho ->
              FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma)
                (consSubst (var zero) (compSub (keepSubstBy 1) sigma))
                rho)
            (liftSubstCompKeep tau)
            (liftFitsEqOne fitsEq dAσ))
    in
    hypTyEqOpen
      nonemptyNeNil
      (eqSubTyRule dB liftedEq)
      (sccTy1Cl sigmaFits dAσ dB)
      (λ rho fits2 _ ->
        let
          composedFitsEq = composeFitsEq fits2 liftedEq
        in
        subst
          (λ J -> Computable J)
          (sym
            (cong₂ (typeEq [])
              (subTyComp rho (liftSubst sigma) B)
              (subTyComp rho (liftSubst tau) B)))
          (eqSubTyCl
            dB
            composedFitsEq))
      (λ rho eta fitsEq2 _ ->
        let
          composedFitsEq = composeEqFitsEq fitsEq2 liftedEq
        in
        subst
          (λ J -> Computable J)
          (sym
            (cong₂ (typeEq [])
              (subTyComp rho (liftSubst sigma) B)
              (subTyComp eta (liftSubst tau) B)))
          (eqSubTyCl
            dB
            composedFitsEq))

  eqSubSccTyEq1 : {gamma : Ctx} {A B C : RawType} {sigma tau : Subst}
    -> ({gamma : Ctx} {A B : RawType} {sigma : Subst}
         -> FitsSubst [] gamma sigma
         -> Derivable (isType [] (subTy sigma A))
         -> Derivable (isType (A ∷ gamma) B)
         -> HypComputable
              (isType (subTy sigma A ∷ [])
                (subTy (liftSubst sigma) B)))
    -> ({gamma : Ctx} {A B : RawType} {sigma tau : Subst}
         -> Derivable (typeEq gamma A B)
         -> FitsEqSubst [] gamma sigma tau
         -> Computable (typeEq [] (subTy sigma A) (subTy tau B)))
    -> FitsEqSubst [] gamma sigma tau
    -> Derivable (isType [] (subTy sigma A))
    -> Derivable (typeEq (A ∷ gamma) B C)
    -> HypComputable (typeEq (subTy sigma A ∷ []) (subTy (liftSubst sigma) B) (subTy (liftSubst tau) C))
  eqSubSccTyEq1 {gamma = gamma} {A = A} {B = B} {C = C} {sigma = sigma} {tau = tau}
    sccTy1Cl eqSubTyEqCl fitsEq dAσ dBC =
    let
      sigmaFits = fitsEqSubstLeft fitsEq
      liftedEq :
        FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma)
          (liftSubst sigma)
          (liftSubst tau)
      liftedEq =
        subst
          (λ rho -> FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma) rho (liftSubst tau))
          (liftSubstCompKeep sigma)
          (subst
            (λ rho ->
              FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma)
                (consSubst (var zero) (compSub (keepSubstBy 1) sigma))
                rho)
            (liftSubstCompKeep tau)
            (liftFitsEqOne fitsEq dAσ))
    in
    hypTyEqOpen
      nonemptyNeNil
      (eqSubTyEqRule dBC liftedEq)
      (sccTy1Cl sigmaFits dAσ (assocTyLeft dBC))
      (λ rho fits2 _ ->
        let
          composedFitsEq = composeFitsEq fits2 liftedEq
        in
        subst
          (λ J -> Computable J)
          (sym
            (cong₂ (typeEq [])
              (subTyComp rho (liftSubst sigma) B)
              (subTyComp rho (liftSubst tau) C)))
          (eqSubTyEqCl
            dBC
            composedFitsEq))
      (λ rho eta fitsEq2 _ ->
        let
          composedFitsEq = composeEqFitsEq fitsEq2 liftedEq
        in
        subst
          (λ J -> Computable J)
          (sym
            (cong₂ (typeEq [])
              (subTyComp rho (liftSubst sigma) B)
              (subTyComp eta (liftSubst tau) C)))
          (eqSubTyEqCl
            dBC
            composedFitsEq))

  eqSubSccTm1 : {gamma : Ctx} {A T : RawType} {t : RawTerm} {sigma tau : Subst}
    -> ({gamma : Ctx} {A T : RawType} {t : RawTerm} {sigma : Subst}
         -> FitsSubst [] gamma sigma
         -> Derivable (isType [] (subTy sigma A))
         -> Derivable (hasTy (A ∷ gamma) t T)
         -> HypComputable
              (hasTy (subTy sigma A ∷ [])
                (subTm (liftSubst sigma) t)
                (subTy (liftSubst sigma) T)))
    -> ({gamma : Ctx} {t : RawTerm} {A : RawType} {sigma tau : Subst}
         -> Derivable (hasTy gamma t A)
         -> FitsEqSubst [] gamma sigma tau
         -> Computable (termEq [] (subTm sigma t) (subTm tau t) (subTy sigma A)))
    -> FitsEqSubst [] gamma sigma tau
    -> Derivable (isType [] (subTy sigma A))
    -> Derivable (hasTy (A ∷ gamma) t T)
    -> HypComputable
         (termEq (subTy sigma A ∷ [])
           (subTm (liftSubst sigma) t)
           (subTm (liftSubst tau) t)
           (subTy (liftSubst sigma) T))
  eqSubSccTm1 {gamma = gamma} {A = A} {T = T} {t = t} {sigma = sigma} {tau = tau}
    sccTm1Cl eqSubTmCl fitsEq dAσ dt =
    let
      sigmaFits = fitsEqSubstLeft fitsEq
      liftedEq :
        FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma)
          (liftSubst sigma)
          (liftSubst tau)
      liftedEq =
        subst
          (λ rho -> FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma) rho (liftSubst tau))
          (liftSubstCompKeep sigma)
          (subst
            (λ rho ->
              FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma)
                (consSubst (var zero) (compSub (keepSubstBy 1) sigma))
                rho)
            (liftSubstCompKeep tau)
            (liftFitsEqOne fitsEq dAσ))
    in
    hypTmEqOpen
      nonemptyNeNil
      (eqSubTmRule dt liftedEq)
      (sccTm1Cl sigmaFits dAσ dt)
      (λ rho fits2 _ ->
        let
          composedFitsEq = composeFitsEq fits2 liftedEq
        in
        subst
          (λ J -> Computable J)
          (sym
            (cong₃ (termEq [])
              (subTmComp rho (liftSubst sigma) t)
              (subTmComp rho (liftSubst tau) t)
              (subTyComp rho (liftSubst sigma) T)))
          (eqSubTmCl
            dt
            composedFitsEq))
      (λ rho eta fitsEq2 _ ->
        let
          composedFitsEq = composeEqFitsEq fitsEq2 liftedEq
        in
        subst
          (λ J -> Computable J)
          (sym
            (cong₃ (termEq [])
              (subTmComp rho (liftSubst sigma) t)
              (subTmComp eta (liftSubst tau) t)
              (subTyComp rho (liftSubst sigma) T)))
          (eqSubTmCl
            dt
            composedFitsEq))

  eqSubSccTmEq1 : {gamma : Ctx} {A T : RawType} {t u : RawTerm} {sigma tau : Subst}
    -> ({gamma : Ctx} {A T : RawType} {t : RawTerm} {sigma : Subst}
         -> FitsSubst [] gamma sigma
         -> Derivable (isType [] (subTy sigma A))
         -> Derivable (hasTy (A ∷ gamma) t T)
         -> HypComputable
              (hasTy (subTy sigma A ∷ [])
                (subTm (liftSubst sigma) t)
                (subTy (liftSubst sigma) T)))
    -> ({gamma : Ctx} {t u : RawTerm} {A : RawType} {sigma tau : Subst}
         -> Derivable (termEq gamma t u A)
         -> FitsEqSubst [] gamma sigma tau
         -> Computable (termEq [] (subTm sigma t) (subTm tau u) (subTy sigma A)))
    -> FitsEqSubst [] gamma sigma tau
    -> Derivable (isType [] (subTy sigma A))
    -> Derivable (termEq (A ∷ gamma) t u T)
    -> HypComputable
         (termEq (subTy sigma A ∷ [])
           (subTm (liftSubst sigma) t)
           (subTm (liftSubst tau) u)
           (subTy (liftSubst sigma) T))
  eqSubSccTmEq1 {gamma = gamma} {A = A} {T = T} {t = t} {u = u} {sigma = sigma} {tau = tau}
    sccTm1Cl eqSubTmEqCl fitsEq dAσ dtu =
    let
      sigmaFits = fitsEqSubstLeft fitsEq
      liftedEq :
        FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma)
          (liftSubst sigma)
          (liftSubst tau)
      liftedEq =
        subst
          (λ rho -> FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma) rho (liftSubst tau))
          (liftSubstCompKeep sigma)
          (subst
            (λ rho ->
              FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma)
                (consSubst (var zero) (compSub (keepSubstBy 1) sigma))
                rho)
            (liftSubstCompKeep tau)
            (liftFitsEqOne fitsEq dAσ))
    in
    hypTmEqOpen
      nonemptyNeNil
      (eqSubTmEqRule dtu liftedEq)
      (sccTm1Cl sigmaFits dAσ (assocTmLeft dtu))
      (λ rho fits2 _ ->
        let
          composedFitsEq = composeFitsEq fits2 liftedEq
        in
        subst
          (λ J -> Computable J)
          (sym
            (cong₃ (termEq [])
              (subTmComp rho (liftSubst sigma) t)
              (subTmComp rho (liftSubst tau) u)
              (subTyComp rho (liftSubst sigma) T)))
          (eqSubTmEqCl
            dtu
            composedFitsEq))
      (λ rho eta fitsEq2 _ ->
        let
          composedFitsEq = composeEqFitsEq fitsEq2 liftedEq
        in
        subst
          (λ J -> Computable J)
          (sym
            (cong₃ (termEq [])
              (subTmComp rho (liftSubst sigma) t)
              (subTmComp eta (liftSubst tau) u)
              (subTyComp rho (liftSubst sigma) T)))
          (eqSubTmEqCl
            dtu
            composedFitsEq))

  eqSubSccTm2 : {gamma : Ctx} {A B T : RawType} {t : RawTerm} {sigma tau : Subst}
    -> ({gamma : Ctx} {A B T : RawType} {t : RawTerm} {sigma : Subst}
         -> FitsSubst [] gamma sigma
         -> Derivable (isType [] (subTy sigma A))
         -> Derivable (isType (subTy sigma A ∷ []) (subTy (liftSubst sigma) B))
         -> Derivable (hasTy (B ∷ A ∷ gamma) t T)
         -> HypComputable
              (hasTy (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ [])
                (subTm (liftSubst (liftSubst sigma)) t)
                (subTy (liftSubst (liftSubst sigma)) T)))
    -> ({gamma : Ctx} {t : RawTerm} {A : RawType} {sigma tau : Subst}
         -> Derivable (hasTy gamma t A)
         -> FitsEqSubst [] gamma sigma tau
         -> Computable (termEq [] (subTm sigma t) (subTm tau t) (subTy sigma A)))
    -> FitsEqSubst [] gamma sigma tau
    -> Derivable (isType [] (subTy sigma A))
    -> Derivable (isType (subTy sigma A ∷ []) (subTy (liftSubst sigma) B))
    -> Derivable (hasTy (B ∷ A ∷ gamma) t T)
    -> HypComputable
         (termEq (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ [])
           (subTm (liftSubst (liftSubst sigma)) t)
           (subTm (liftSubst (liftSubst tau)) t)
           (subTy (liftSubst (liftSubst sigma)) T))
  eqSubSccTm2 {gamma = gamma} {A = A} {B = B} {T = T} {t = t} {sigma = sigma} {tau = tau}
    sccTm2Cl eqSubTmCl fitsEq dAσ dBσ dt =
    let
      sigmaFits = fitsEqSubstLeft fitsEq
      lifted1Eq :
        FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma)
          (liftSubst sigma)
          (liftSubst tau)
      lifted1Eq =
        subst
          (λ rho -> FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma) rho (liftSubst tau))
          (liftSubstCompKeep sigma)
          (subst
            (λ rho ->
              FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma)
                (consSubst (var zero) (compSub (keepSubstBy 1) sigma))
                rho)
            (liftSubstCompKeep tau)
            (liftFitsEqOne fitsEq dAσ))
      lifted2Eq :
        FitsEqSubst (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) (B ∷ A ∷ gamma)
          (liftSubst (liftSubst sigma))
          (liftSubst (liftSubst tau))
      lifted2Eq =
        subst
          (λ rho ->
            FitsEqSubst (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) (B ∷ A ∷ gamma)
              rho
              (liftSubst (liftSubst tau)))
          (liftSubstCompKeep (liftSubst sigma))
          (subst
            (λ rho ->
              FitsEqSubst (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) (B ∷ A ∷ gamma)
                (consSubst (var zero) (compSub (keepSubstBy 1) (liftSubst sigma)))
                rho)
            (liftSubstCompKeep (liftSubst tau))
            (liftFitsEq lifted1Eq dBσ))
    in
    hypTmEqOpen
      nonemptyNeNil
      (eqSubTmRule dt lifted2Eq)
      (sccTm2Cl sigmaFits dAσ dBσ dt)
      (λ rho fits2 _ ->
        let
          composedFitsEq = composeFitsEq fits2 lifted2Eq
        in
        subst
          (λ J -> Computable J)
          (sym
            (cong₃ (termEq [])
              (subTmComp rho (liftSubst (liftSubst sigma)) t)
              (subTmComp rho (liftSubst (liftSubst tau)) t)
              (subTyComp rho (liftSubst (liftSubst sigma)) T)))
          (eqSubTmCl
            dt
            composedFitsEq))
      (λ rho eta fitsEq2 _ ->
        let
          composedFitsEq = composeEqFitsEq fitsEq2 lifted2Eq
        in
        subst
          (λ J -> Computable J)
          (sym
            (cong₃ (termEq [])
              (subTmComp rho (liftSubst (liftSubst sigma)) t)
              (subTmComp eta (liftSubst (liftSubst tau)) t)
              (subTyComp rho (liftSubst (liftSubst sigma)) T)))
          (eqSubTmCl
            dt
            composedFitsEq))

  eqSubSccTmEq2 : {gamma : Ctx} {A B T : RawType} {t u : RawTerm} {sigma tau : Subst}
    -> ({gamma : Ctx} {A B T : RawType} {t : RawTerm} {sigma : Subst}
         -> FitsSubst [] gamma sigma
         -> Derivable (isType [] (subTy sigma A))
         -> Derivable (isType (subTy sigma A ∷ []) (subTy (liftSubst sigma) B))
         -> Derivable (hasTy (B ∷ A ∷ gamma) t T)
         -> HypComputable
              (hasTy (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ [])
                (subTm (liftSubst (liftSubst sigma)) t)
                (subTy (liftSubst (liftSubst sigma)) T)))
    -> ({gamma : Ctx} {t u : RawTerm} {A : RawType} {sigma tau : Subst}
         -> Derivable (termEq gamma t u A)
         -> FitsEqSubst [] gamma sigma tau
         -> Computable (termEq [] (subTm sigma t) (subTm tau u) (subTy sigma A)))
    -> FitsEqSubst [] gamma sigma tau
    -> Derivable (isType [] (subTy sigma A))
    -> Derivable (isType (subTy sigma A ∷ []) (subTy (liftSubst sigma) B))
    -> Derivable (termEq (B ∷ A ∷ gamma) t u T)
    -> HypComputable
         (termEq (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ [])
           (subTm (liftSubst (liftSubst sigma)) t)
           (subTm (liftSubst (liftSubst tau)) u)
           (subTy (liftSubst (liftSubst sigma)) T))
  eqSubSccTmEq2 {gamma = gamma} {A = A} {B = B} {T = T} {t = t} {u = u} {sigma = sigma} {tau = tau}
    sccTm2Cl eqSubTmEqCl fitsEq dAσ dBσ dtu =
    let
      sigmaFits = fitsEqSubstLeft fitsEq
      lifted1Eq :
        FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma)
          (liftSubst sigma)
          (liftSubst tau)
      lifted1Eq =
        subst
          (λ rho -> FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma) rho (liftSubst tau))
          (liftSubstCompKeep sigma)
          (subst
            (λ rho ->
              FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma)
                (consSubst (var zero) (compSub (keepSubstBy 1) sigma))
                rho)
            (liftSubstCompKeep tau)
            (liftFitsEqOne fitsEq dAσ))
      lifted2Eq :
        FitsEqSubst (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) (B ∷ A ∷ gamma)
          (liftSubst (liftSubst sigma))
          (liftSubst (liftSubst tau))
      lifted2Eq =
        subst
          (λ rho ->
            FitsEqSubst (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) (B ∷ A ∷ gamma)
              rho
              (liftSubst (liftSubst tau)))
          (liftSubstCompKeep (liftSubst sigma))
          (subst
            (λ rho ->
              FitsEqSubst (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) (B ∷ A ∷ gamma)
                (consSubst (var zero) (compSub (keepSubstBy 1) (liftSubst sigma)))
                rho)
            (liftSubstCompKeep (liftSubst tau))
            (liftFitsEq lifted1Eq dBσ))
    in
    hypTmEqOpen
      nonemptyNeNil
      (eqSubTmEqRule dtu lifted2Eq)
      (sccTm2Cl sigmaFits dAσ dBσ (assocTmLeft dtu))
      (λ rho fits2 _ ->
        let
          composedFitsEq = composeFitsEq fits2 lifted2Eq
        in
        subst
          (λ J -> Computable J)
          (sym
            (cong₃ (termEq [])
              (subTmComp rho (liftSubst (liftSubst sigma)) t)
              (subTmComp rho (liftSubst (liftSubst tau)) u)
              (subTyComp rho (liftSubst (liftSubst sigma)) T)))
          (eqSubTmEqCl
            dtu
            composedFitsEq))
      (λ rho eta fitsEq2 _ ->
        let
          composedFitsEq = composeEqFitsEq fitsEq2 lifted2Eq
        in
        subst
          (λ J -> Computable J)
          (sym
            (cong₃ (termEq [])
              (subTmComp rho (liftSubst (liftSubst sigma)) t)
              (subTmComp eta (liftSubst (liftSubst tau)) u)
              (subTyComp rho (liftSubst (liftSubst sigma)) T)))
          (eqSubTmEqCl
            dtu
            composedFitsEq))

  substDerivTyComp (fTop wf) fits = compFTopClosed
  substDerivTyComp {gamma = gamma} {sigma = sigma} (fSigma {A = A} {B = B} dA dB) fits =
    let
      compA = substDerivTyComp dA fits
      dAσ = substTyRule dA fits
      compB =
        subst
          (λ T -> HypComputable (isType (subTy sigma A ∷ []) T))
          (cong (λ rho -> subTy rho B) (liftSubstCompKeep sigma))
          (hypTyOpen
            nonemptyNeNil
            (substTyRule dB (liftFitsOne fits dAσ))
            (λ tau fits2 _ ->
              subst
                (λ T -> Computable (isType [] T))
                (sym
                  (cong (λ rho -> subTy tau (subTy rho B)) (liftSubstCompKeep sigma)
                    ∙ subTyComp tau (liftSubst sigma) B))
                (substDerivTyComp
                  dB
                  (composeOneBinder fits dAσ fits2)))
            (λ tau₁ tau₂ fitsEq2 _ ->
              subst
                (λ J -> Computable J)
                (sym
                  (cong₂ (typeEq [])
                    (cong (λ rho -> subTy tau₁ (subTy rho B)) (liftSubstCompKeep sigma)
                      ∙ subTyComp tau₁ (liftSubst sigma) B)
                    (cong (λ rho -> subTy tau₂ (subTy rho B)) (liftSubstCompKeep sigma)
                      ∙ subTyComp tau₂ (liftSubst sigma) B)))
                (eqSubDerivTyComp
                  dB
                  (composeOneBinderEq fits dAσ fitsEq2))))
    in
    compFSigmaClosed compA compB
  substDerivTyComp (fEq dA da db) fits =
    compFEqClosed
      (substDerivTyComp dA fits)
      (substDerivTmComp da fits)
      (substDerivTmComp db fits)
  substDerivTyComp (fQtr dA) fits =
    compFQtrClosed (substDerivTyComp dA fits)
  substDerivTyComp {sigma = sigma} (weakenTy {delta = delta} {A = A} d wf) fits =
    subst
      (λ T -> Computable (isType [] T))
      (sym (subTyWkBy sigma (length delta) A))
      (substDerivTyComp d (dropFits delta fits))
  substDerivTyComp {sigma = sigma} (substTyRule {sigma = sigma'} {A = A} d fits') fits =
    let
      composedFits = composeFits fits fits'
    in
    subst
      (λ T -> Computable (isType [] T))
      (sym (subTyComp sigma sigma' A))
      (substDerivTyComp d composedFits)

  substDerivTyEqComp : {gamma : Ctx} {A B : RawType} {sigma : Subst}
    -> Derivable (typeEq gamma A B)
    -> FitsSubst [] gamma sigma
    -> Computable (typeEq [] (subTy sigma A) (subTy sigma B))
  substDerivTyEqComp (reflTy d) fits =
    compReflTy (substDerivTyComp d fits)
  substDerivTyEqComp (symTy d) fits =
    compSymTyClosed (substDerivTyEqComp d fits)
  substDerivTyEqComp (transTy d₁ d₂) fits =
    compTransTyClosed (substDerivTyEqComp d₁ fits) (substDerivTyEqComp d₂ fits)
  substDerivTyEqComp {sigma = sigma} (fSigmaEq {A = A} {B = B} {D = D} dAC dBD) fits =
    let
      compAC = substDerivTyEqComp dAC fits
      compA = compTyEqLeft compAC
      compC = compTyEqRightClosed compAC
      dAσ = substTyRule (assocTyLeft dAC) fits
      compB =
        subst
          (λ T -> HypComputable (isType (subTy sigma A ∷ []) T))
          (cong (λ rho -> subTy rho B) (liftSubstCompKeep sigma))
          (hypTyOpen
            nonemptyNeNil
            (substTyRule (assocTyLeft dBD) (liftFitsOne fits dAσ))
            (λ tau fits2 _ ->
              subst
                (λ T -> Computable (isType [] T))
                (sym
                  (cong (λ rho -> subTy tau (subTy rho B)) (liftSubstCompKeep sigma)
                    ∙ subTyComp tau (liftSubst sigma) B))
                (compTyEqLeft
                  (substDerivTyEqComp
                    dBD
                    (composeOneBinder fits dAσ fits2))))
            (λ tau₁ tau₂ fitsEq2 _ ->
              subst
                (λ J -> Computable J)
                (sym
                  (cong₂ (typeEq [])
                    (cong (λ rho -> subTy tau₁ (subTy rho B)) (liftSubstCompKeep sigma)
                      ∙ subTyComp tau₁ (liftSubst sigma) B)
                    (cong (λ rho -> subTy tau₂ (subTy rho B)) (liftSubstCompKeep sigma)
                      ∙ subTyComp tau₂ (liftSubst sigma) B)))
                (compTransTyClosed
                  (eqSubDerivTyEqComp
                    dBD
                    (composeOneBinderEq fits dAσ fitsEq2))
                  (compSymTyClosed
                    (substDerivTyEqComp
                      dBD
                      (composeOneBinder
                        fits
                        dAσ
                        (fitsEqSubstRight (wfCons wfNil dAσ) fitsEq2)))))))
      compBD =
        subst
          (λ J -> HypComputable J)
          (cong₂
            (typeEq (subTy sigma A ∷ []))
            (cong (λ rho -> subTy rho B) (liftSubstCompKeep sigma))
            (cong (λ rho -> subTy rho D) (liftSubstCompKeep sigma)))
          (hypTyEqOpen
            nonemptyNeNil
            (substTyEqRule dBD (liftFitsOne fits dAσ))
            (subst
              (λ T -> HypComputable (isType (subTy sigma A ∷ []) T))
              (sym (cong (λ rho -> subTy rho B) (liftSubstCompKeep sigma)))
              compB)
            (λ tau fits2 _ ->
              subst
                (λ J -> Computable J)
                (sym
                  (cong₂ (typeEq [])
                    (cong (λ rho -> subTy tau (subTy rho B)) (liftSubstCompKeep sigma)
                      ∙ subTyComp tau (liftSubst sigma) B)
                    (cong (λ rho -> subTy tau (subTy rho D)) (liftSubstCompKeep sigma)
                      ∙ subTyComp tau (liftSubst sigma) D)))
                (substDerivTyEqComp
                  dBD
                  (composeOneBinder fits dAσ fits2)))
            (λ tau₁ tau₂ fitsEq2 _ ->
              subst
                (λ J -> Computable J)
                (sym
                  (cong₂ (typeEq [])
                    (cong (λ rho -> subTy tau₁ (subTy rho B)) (liftSubstCompKeep sigma)
                      ∙ subTyComp tau₁ (liftSubst sigma) B)
                    (cong (λ rho -> subTy tau₂ (subTy rho D)) (liftSubstCompKeep sigma)
                      ∙ subTyComp tau₂ (liftSubst sigma) D)))
                (eqSubDerivTyEqComp
                  dBD
                  (composeOneBinderEq fits dAσ fitsEq2))))
      compSigmaA = compFSigmaClosed compA (hypTyEqLeft compBD)
      compSigmaC = compFSigmaClosed compC (compTransportFamilyTy compAC (hypTyEqRight compBD))
    in
    compTyEqClosedSigma
      (fSigmaEq (compToDerivable compAC) (hypCompToDerivable compBD))
      compSigmaA
      compSigmaC
      evalSigma
      evalSigma
      compAC
      (hypCompToDerivable compBD)
  substDerivTyEqComp (fEqEq dAC dac dbd) fits =
    let
      compAC = substDerivTyEqComp dAC fits
      compac = substDerivTmEqComp dac fits
      compbd = substDerivTmEqComp dbd fits
      compA = compTyEqLeft compAC
      compC = compTyEqRightClosed compAC
      compa = compTmEqLeft compac
      compb = compTmEqLeft compbd
      compcA = compTmEqRightClosed compac
      compdA = compTmEqRightClosed compbd
      compc = compConvTmClosed compcA compAC
      compd = compConvTmClosed compdA compAC
      compEqA = compFEqClosed compA compa compb
      compEqC = compFEqClosed compC compc compd
    in
    compTyEqClosedEq
      (fEqEq (compToDerivable compAC) (compToDerivable compac) (compToDerivable compbd))
      compEqA
      compEqC
      evalEq
      evalEq
      compAC
      compac
      compbd
  substDerivTyEqComp (fQtrEq dAB) fits =
    let
      compAB = substDerivTyEqComp dAB fits
    in
    compTyEqClosedQtr
      (fQtrEq (compToDerivable compAB))
      (compFQtrClosed (compTyEqLeft compAB))
      (compFQtrClosed (compTyEqRightClosed compAB))
      evalQtr
      evalQtr
      compAB
  substDerivTyEqComp {sigma = sigma} (weakenTyEq {delta = delta} {A = A} {B = B} d wf) fits =
    subst
      (λ J -> Computable J)
      (cong₂ (typeEq [])
        (sym (subTyWkBy sigma (length delta) A))
        (sym (subTyWkBy sigma (length delta) B)))
      (substDerivTyEqComp d (dropFits delta fits))
  substDerivTyEqComp {sigma = sigma} (substTyEqRule {sigma = sigma'} {A = A} {B = B} d fits') fits =
    let
      composedFits = composeFits fits fits'
    in
    subst
      (λ J -> Computable J)
      (cong₂ (typeEq [])
        (sym (subTyComp sigma sigma' A))
        (sym (subTyComp sigma sigma' B)))
      (substDerivTyEqComp d composedFits)
  substDerivTyEqComp {sigma = sigma} (eqSubTyRule {sigma = sigma'} {tau = tau'} {A = A} d fitsEq') fits =
    let
      composedFitsEq = composeFitsEq fits fitsEq'
    in
    subst
      (λ J -> Computable J)
      (cong₂ (typeEq [])
        (sym (subTyComp sigma sigma' A))
        (sym (subTyComp sigma tau' A)))
      (eqSubDerivTyComp d composedFitsEq)
  substDerivTyEqComp {sigma = sigma} (eqSubTyEqRule {sigma = sigma'} {tau = tau'} {A = A} {B = B} d fitsEq') fits =
    let
      composedFitsEq = composeFitsEq fits fitsEq'
    in
    subst
      (λ J -> Computable J)
      (cong₂ (typeEq [])
        (sym (subTyComp sigma sigma' A))
        (sym (subTyComp sigma tau' B)))
      (eqSubDerivTyEqComp d composedFitsEq)

  substDerivTmCompEQtr
    : {gamma : Ctx} {A L : RawType} {l p : RawTerm} {sigma : Subst}
    -> Derivable (isType ((tyQtr A) ∷ gamma) L)
    -> Derivable (hasTy gamma p (tyQtr A))
    -> Derivable (hasTy (A ∷ gamma) l (qtrBranchTy L))
    -> Derivable
         (termEq (wkTyBy 1 A ∷ A ∷ gamma)
           (wkTmBy 1 l)
           (renTm qtrSecondBranchRen l)
           (qtrCohTy L))
    -> FitsSubst [] gamma sigma
    -> Computable
         (hasTy [] (subTm sigma (tmElQtr l p))
           (subTy sigma (subTy (singleSubst p) L)))
  substDerivTmCompEQtr
    {gamma = gamma} {A = A} {L = L} {l = l} {p = p} {sigma = sigma}
    dL dp dl dcoh fits =
    let
      compdp = substDerivTmComp dp fits
      compQtrσ = compTmToCompTy compdp
      dQtrσ = compToDerivable compQtrσ
      tyInv = invertQtrTy compQtrσ evalQtr
      compAσ = ClosedQtrTyInv.qtrTyCompBase tyInv
      dAσ = compToDerivable compAσ
      dWkAσ =
        subst
          (λ T -> Derivable (isType (subTy sigma A ∷ []) T))
          (sym (wkTyLiftSubst sigma A))
          (weakenTy dAσ (wfCons wfNil dAσ))
      compL = openHypTy1 fits dQtrσ dL

      compl =
        subst
          (λ T ->
            HypComputable
              (hasTy (subTy sigma A ∷ [])
                (subTm (liftSubst sigma) l)
                T))
          (qtrBranchTyLiftComp sigma L)
          (openHypTm1
            fits
            dAσ
            dl)

      compcoh =
        subst
          (λ J -> HypComputable J)
          (cong
            (λ T ->
              termEq (T ∷ subTy sigma A ∷ [])
                (subTm (liftSubst (liftSubst sigma)) (wkTmBy 1 l))
                (subTm (liftSubst (liftSubst sigma)) (renTm qtrSecondBranchRen l))
                (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
            (wkTyLiftSubst sigma A)
            ∙ cong
                (λ t ->
                  termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                    t
                    (subTm (liftSubst (liftSubst sigma)) (renTm qtrSecondBranchRen l))
                    (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
                (wkTmLiftSubst (liftSubst sigma) l)
            ∙ cong
                (λ u ->
                  termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                    (wkTmBy 1 (subTm (liftSubst sigma) l))
                    u
                    (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
                (qtrSecondBranchTmLiftComp sigma l)
            ∙ cong
                (λ T ->
                  termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                    (wkTmBy 1 (subTm (liftSubst sigma) l))
                    (renTm qtrSecondBranchRen (subTm (liftSubst sigma) l))
                    T)
                (qtrCohTyLiftComp sigma L))
          (openHypTmEq2
            fits
            dAσ
            dWkAσ
            dcoh)

      resultPath :
        hasTy []
          (subTm sigma (tmElQtr l p))
          (subTy sigma (subTy (singleSubst p) L))
          ≡
        hasTy []
          (tmElQtr (subTm (liftSubst sigma) l) (subTm sigma p))
          (subTy (singleSubst (subTm sigma p)) (subTy (liftSubst sigma) L))
      resultPath =
        cong₂
          (hasTy [])
          refl
          (subTyComp sigma (singleSubst p) L
            ∙ cong (λ rho -> subTy rho L) (sym (singleSubstCompLift sigma p))
            ∙ sym (subTyComp (singleSubst (subTm sigma p)) (liftSubst sigma) L))
    in
    subst
      (λ J -> Computable J)
      (sym resultPath)
      (compTmEqLeft
        (compEQtrClosed
          compTransTmClosed
          compSymTmClosed
          compConvTmEqClosed
          compL
          (compReflTm compdp)
          (hypReflTm compl)
          compcoh
          compcoh))

  substDerivTmComp (varStar {delta = delta} {A = A} wf dA) fits =
    computableTmClosed (lookupVarFits {delta = delta} {A = A} fits)
  substDerivTmComp (iTop wf) fits = compITopClosed
  substDerivTmComp {sigma = sigma}
    (iSigma {a = a} {b = b} {A = A} {B = B} da db dSigma) fits =
    let
      compa = substDerivTmComp da fits
      compb =
        subst
          (λ T -> Computable (hasTy [] (subTm sigma b) T))
          (subTyComp sigma (singleSubst a) B
            ∙ cong (λ rho -> subTy rho B) (sym (singleSubstCompLift sigma a))
            ∙ sym (subTyComp (singleSubst (subTm sigma a)) (liftSubst sigma) B))
          (substDerivTmComp db fits)
    in
    compISigmaClosed compa compb (substDerivTyComp dSigma fits)
  substDerivTmComp (iEq da) fits =
    compIEqClosed (substDerivTmComp da fits)
  substDerivTmComp (iQtr da) fits =
    compIQtrClosed (substDerivTmComp da fits)
  substDerivTmComp {gamma = gamma} {sigma = sigma}
    (eSigma {A = A} {B = B} {M = M} {d = d} {m = m} dM dd dm) fits =
    let
      compdd = substDerivTmComp dd fits
      compSigma = compTmToCompTy compdd
      dSigmaσ = compToDerivable compSigma
      tyInv = invertSigmaTy compSigma evalSigma
      compAσ = ClosedSigmaTyInv.sigmaTyCompHead tyInv
      dAσ = compToDerivable compAσ
      compBσ = hypComputableTy (ClosedSigmaTyInv.sigmaTyFamDeriv tyInv)
      dBσ = hypCompToDerivable compBσ
      compM = openHypTy1 fits dSigmaσ dM

      compdm =
        let
          lifted1 : FitsSubst (subTy sigma A ∷ []) (A ∷ gamma) (liftSubst sigma)
          lifted1 =
            subst
              (λ rho -> FitsSubst (subTy sigma A ∷ []) (A ∷ gamma) rho)
              (liftSubstCompKeep sigma)
              (liftFitsOne fits dAσ)
          compBranchTy =
            subst
              (λ T' ->
                HypComputable (isType (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) T'))
              (cong (λ rho -> subTy rho (sigmaBranchTy M))
                (liftSubstCompKeep (liftSubst sigma)))
              (hypTyOpen
                nonemptyNeNil
                (substTyRule (assocTy dm) (liftFits lifted1 dBσ))
                (λ rho fits2 _ ->
                  subst
                    (λ T' -> Computable (isType [] T'))
                    (sym
                      (cong (λ theta -> subTy rho (subTy theta (sigmaBranchTy M)))
                        (liftSubstCompKeep (liftSubst sigma))
                        ∙ subTyComp rho (liftSubst (liftSubst sigma)) (sigmaBranchTy M)))
                    (substDerivTyComp
                      (assocTy dm)
                      (composeTwoBinders fits dAσ dBσ fits2)))
                (λ rho eta fitsEq2 _ ->
                  subst
                    (λ J -> Computable J)
                    (sym
                      (cong₂ (typeEq [])
                        (cong (λ theta -> subTy rho (subTy theta (sigmaBranchTy M)))
                          (liftSubstCompKeep (liftSubst sigma))
                          ∙ subTyComp rho (liftSubst (liftSubst sigma)) (sigmaBranchTy M))
                        (cong (λ theta -> subTy eta (subTy theta (sigmaBranchTy M)))
                          (liftSubstCompKeep (liftSubst sigma))
                          ∙ subTyComp eta (liftSubst (liftSubst sigma)) (sigmaBranchTy M))))
                    (eqSubDerivTyComp
                      (assocTy dm)
                      (composeTwoBindersEq fits dAσ dBσ fitsEq2))))
        in
        subst
          (λ J -> HypComputable J)
          (cong
            (hasTy (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ [])
              (subTm (liftSubst (liftSubst sigma)) m))
            (sigmaBranchTyLiftComp sigma M))
          (subst
            (λ J -> HypComputable J)
            (cong₂
              (hasTy (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []))
              (cong (λ rho -> subTm rho m) (liftSubstCompKeep (liftSubst sigma)))
              (cong (λ rho -> subTy rho (sigmaBranchTy M))
                (liftSubstCompKeep (liftSubst sigma))))
            (hypTmOpen
              nonemptyNeNil
              (substTmRule dm (liftFits lifted1 dBσ))
              (subst
                (λ T' ->
                  HypComputable (isType (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) T'))
                (sym
                  (cong (λ rho -> subTy rho (sigmaBranchTy M))
                    (liftSubstCompKeep (liftSubst sigma))))
                compBranchTy)
              (λ rho fits2 _ ->
                subst
                  (λ J -> Computable J)
                  (sym
                    (cong₂ (hasTy [])
                      (cong (λ theta -> subTm rho (subTm theta m))
                        (liftSubstCompKeep (liftSubst sigma))
                        ∙ subTmComp rho (liftSubst (liftSubst sigma)) m)
                      (cong (λ theta -> subTy rho (subTy theta (sigmaBranchTy M)))
                        (liftSubstCompKeep (liftSubst sigma))
                        ∙ subTyComp rho (liftSubst (liftSubst sigma)) (sigmaBranchTy M))))
                  (substDerivTmComp
                    dm
                    (composeTwoBinders fits dAσ dBσ fits2)))
              (λ rho eta fitsEq2 _ ->
                subst
                  (λ J -> Computable J)
                  (sym
                    (cong₃ (termEq [])
                      (cong (λ theta -> subTm rho (subTm theta m))
                        (liftSubstCompKeep (liftSubst sigma))
                        ∙ subTmComp rho (liftSubst (liftSubst sigma)) m)
                      (cong (λ theta -> subTm eta (subTm theta m))
                        (liftSubstCompKeep (liftSubst sigma))
                        ∙ subTmComp eta (liftSubst (liftSubst sigma)) m)
                      (cong (λ theta -> subTy rho (subTy theta (sigmaBranchTy M)))
                        (liftSubstCompKeep (liftSubst sigma))
                        ∙ subTyComp rho (liftSubst (liftSubst sigma)) (sigmaBranchTy M))))
                  (eqSubDerivTmComp
                    dm
                    (composeTwoBindersEq fits dAσ dBσ fitsEq2)))))

      resultPath :
        hasTy [] (subTm sigma (tmElSigma d m)) (subTy sigma (subTy (singleSubst d) M))
          ≡
        hasTy []
          (tmElSigma (subTm sigma d) (subTm (liftSubst (liftSubst sigma)) m))
          (subTy (singleSubst (subTm sigma d)) (subTy (liftSubst sigma) M))
      resultPath =
        cong₂
          (hasTy [])
          refl
          (subTyComp sigma (singleSubst d) M
            ∙ cong (λ rho -> subTy rho M) (sym (singleSubstCompLift sigma d))
            ∙ sym (subTyComp (singleSubst (subTm sigma d)) (liftSubst sigma) M))
    in
    subst
      (λ J -> Computable J)
      (sym resultPath)
      (compTmEqLeft
        (compESigmaClosed compTransTmClosed compConvTmEqClosed
          compM (compReflTm compdd) (hypReflTm compdm)))
  substDerivTmComp (eQtr dL dp dl dcoh) fits =
    substDerivTmCompEQtr dL dp dl dcoh fits
  substDerivTmComp (conv d dAB) fits =
    compConvTmClosed (substDerivTmComp d fits) (substDerivTyEqComp dAB fits)
  substDerivTmComp {sigma = sigma} (weakenTm {delta = delta} {t = t} {A = A} d wf) fits =
    subst
      (λ J -> Computable J)
      (cong₂ (hasTy [])
        (sym (subTmWkBy sigma (length delta) t))
        (sym (subTyWkBy sigma (length delta) A)))
      (substDerivTmComp d (dropFits delta fits))
  substDerivTmComp {sigma = sigma} (substTmRule {sigma = sigma'} {t = t} {A = A} d fits') fits =
    let
      composedFits = composeFits fits fits'
    in
    subst
      (λ J -> Computable J)
      (cong₂ (hasTy [])
        (sym (subTmComp sigma sigma' t))
        (sym (subTyComp sigma sigma' A)))
      (substDerivTmComp d composedFits)
  substDerivTmEqCompESigmaEq
    : {gamma : Ctx} {A B M : RawType} {d d' m m' : RawTerm} {sigma : Subst}
    -> Derivable (isType ((tySigma A B) ∷ gamma) M)
    -> Derivable (termEq gamma d d' (tySigma A B))
    -> Derivable (termEq (B ∷ A ∷ gamma) m m' (sigmaBranchTy M))
    -> FitsSubst [] gamma sigma
    -> Computable
         (termEq []
           (subTm sigma (tmElSigma d m))
           (subTm sigma (tmElSigma d' m'))
           (subTy sigma (subTy (singleSubst d) M)))
  substDerivTmEqCompESigmaEq
    {gamma = gamma} {A = A} {B = B} {M = M} {d = d} {d' = d'} {m = m} {m' = m'} {sigma = sigma}
    dM dd dm fits =
    let
      compdd = substDerivTmEqComp dd fits
      compSigma = compTmToCompTy (compTmEqLeft compdd)
      dSigmaσ = compToDerivable compSigma
      tyInv = invertSigmaTy compSigma evalSigma
      compAσ = ClosedSigmaTyInv.sigmaTyCompHead tyInv
      dAσ = compToDerivable compAσ
      compBσ = hypComputableTy (ClosedSigmaTyInv.sigmaTyFamDeriv tyInv)
      dBσ = hypCompToDerivable compBσ
      compM = openHypTy1 fits dSigmaσ dM

      compdm =
        let
          lifted1 : FitsSubst (subTy sigma A ∷ []) (A ∷ gamma) (liftSubst sigma)
          lifted1 =
            subst
              (λ rho -> FitsSubst (subTy sigma A ∷ []) (A ∷ gamma) rho)
              (liftSubstCompKeep sigma)
              (liftFitsOne fits dAσ)
          compBranchTy =
            subst
              (λ T' ->
                HypComputable (isType (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) T'))
              (cong (λ rho -> subTy rho (sigmaBranchTy M))
                (liftSubstCompKeep (liftSubst sigma)))
              (hypTyOpen
                nonemptyNeNil
                (substTyRule (assocTy (assocTmLeft dm)) (liftFits lifted1 dBσ))
                (λ rho fits2 _ ->
                  subst
                    (λ T' -> Computable (isType [] T'))
                    (sym
                      (cong (λ theta -> subTy rho (subTy theta (sigmaBranchTy M)))
                        (liftSubstCompKeep (liftSubst sigma))
                        ∙ subTyComp rho (liftSubst (liftSubst sigma)) (sigmaBranchTy M)))
                    (substDerivTyComp
                      (assocTy (assocTmLeft dm))
                      (composeTwoBinders fits dAσ dBσ fits2)))
                (λ rho eta fitsEq2 _ ->
                  subst
                    (λ J -> Computable J)
                    (sym
                      (cong₂ (typeEq [])
                        (cong (λ theta -> subTy rho (subTy theta (sigmaBranchTy M)))
                          (liftSubstCompKeep (liftSubst sigma))
                          ∙ subTyComp rho (liftSubst (liftSubst sigma)) (sigmaBranchTy M))
                        (cong (λ theta -> subTy eta (subTy theta (sigmaBranchTy M)))
                          (liftSubstCompKeep (liftSubst sigma))
                          ∙ subTyComp eta (liftSubst (liftSubst sigma)) (sigmaBranchTy M))))
                    (eqSubDerivTyComp
                      (assocTy (assocTmLeft dm))
                      (composeTwoBindersEq fits dAσ dBσ fitsEq2))))
          compAssoc =
            subst
              (λ J -> HypComputable J)
              (cong₂
                (hasTy (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []))
                (cong (λ rho -> subTm rho m) (liftSubstCompKeep (liftSubst sigma)))
                (cong (λ rho -> subTy rho (sigmaBranchTy M))
                  (liftSubstCompKeep (liftSubst sigma))))
              (hypTmOpen
                nonemptyNeNil
                (substTmRule (assocTmLeft dm) (liftFits lifted1 dBσ))
                (subst
                  (λ T' ->
                    HypComputable (isType (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) T'))
                  (sym
                    (cong (λ rho -> subTy rho (sigmaBranchTy M))
                      (liftSubstCompKeep (liftSubst sigma))))
                  compBranchTy)
                (λ rho fits2 _ ->
                  subst
                    (λ J -> Computable J)
                    (sym
                      (cong₂ (hasTy [])
                        (cong (λ theta -> subTm rho (subTm theta m))
                          (liftSubstCompKeep (liftSubst sigma))
                          ∙ subTmComp rho (liftSubst (liftSubst sigma)) m)
                        (cong (λ theta -> subTy rho (subTy theta (sigmaBranchTy M)))
                          (liftSubstCompKeep (liftSubst sigma))
                          ∙ subTyComp rho (liftSubst (liftSubst sigma)) (sigmaBranchTy M))))
                    (substDerivTmComp
                      (assocTmLeft dm)
                      (composeTwoBinders fits dAσ dBσ fits2)))
                (λ rho eta fitsEq2 _ ->
                  subst
                    (λ J -> Computable J)
                    (sym
                      (cong₃ (termEq [])
                        (cong (λ theta -> subTm rho (subTm theta m))
                          (liftSubstCompKeep (liftSubst sigma))
                          ∙ subTmComp rho (liftSubst (liftSubst sigma)) m)
                        (cong (λ theta -> subTm eta (subTm theta m))
                          (liftSubstCompKeep (liftSubst sigma))
                          ∙ subTmComp eta (liftSubst (liftSubst sigma)) m)
                        (cong (λ theta -> subTy rho (subTy theta (sigmaBranchTy M)))
                          (liftSubstCompKeep (liftSubst sigma))
                          ∙ subTyComp rho (liftSubst (liftSubst sigma)) (sigmaBranchTy M))))
                    (eqSubDerivTmComp
                      (assocTmLeft dm)
                      (composeTwoBindersEq fits dAσ dBσ fitsEq2))))
        in
        subst
          (λ J -> HypComputable J)
          (cong
            (termEq (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ [])
              (subTm (liftSubst (liftSubst sigma)) m)
              (subTm (liftSubst (liftSubst sigma)) m'))
            (sigmaBranchTyLiftComp sigma M))
          (subst
            (λ J -> HypComputable J)
            (cong₃
              (termEq (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []))
              (cong (λ rho -> subTm rho m) (liftSubstCompKeep (liftSubst sigma)))
              (cong (λ rho -> subTm rho m') (liftSubstCompKeep (liftSubst sigma)))
              (cong (λ rho -> subTy rho (sigmaBranchTy M))
                (liftSubstCompKeep (liftSubst sigma))))
            (hypTmEqOpen
              nonemptyNeNil
              (substTmEqRule dm (liftFits lifted1 dBσ))
              (subst
                (λ J -> HypComputable J)
                (sym
                  (cong₂
                    (hasTy (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []))
                    (cong (λ rho -> subTm rho m) (liftSubstCompKeep (liftSubst sigma)))
                    (cong (λ rho -> subTy rho (sigmaBranchTy M))
                      (liftSubstCompKeep (liftSubst sigma)))))
                compAssoc)
              (λ rho fits2 _ ->
                subst
                  (λ J -> Computable J)
                  (sym
                    (cong₃ (termEq [])
                      (cong (λ theta -> subTm rho (subTm theta m))
                        (liftSubstCompKeep (liftSubst sigma))
                        ∙ subTmComp rho (liftSubst (liftSubst sigma)) m)
                      (cong (λ theta -> subTm rho (subTm theta m'))
                        (liftSubstCompKeep (liftSubst sigma))
                        ∙ subTmComp rho (liftSubst (liftSubst sigma)) m')
                      (cong (λ theta -> subTy rho (subTy theta (sigmaBranchTy M)))
                        (liftSubstCompKeep (liftSubst sigma))
                        ∙ subTyComp rho (liftSubst (liftSubst sigma)) (sigmaBranchTy M))))
                  (substDerivTmEqComp
                    dm
                    (composeTwoBinders fits dAσ dBσ fits2)))
              (λ rho eta fitsEq2 _ ->
                subst
                  (λ J -> Computable J)
                  (sym
                    (cong₃ (termEq [])
                      (cong (λ theta -> subTm rho (subTm theta m))
                        (liftSubstCompKeep (liftSubst sigma))
                        ∙ subTmComp rho (liftSubst (liftSubst sigma)) m)
                      (cong (λ theta -> subTm eta (subTm theta m'))
                        (liftSubstCompKeep (liftSubst sigma))
                        ∙ subTmComp eta (liftSubst (liftSubst sigma)) m')
                      (cong (λ theta -> subTy rho (subTy theta (sigmaBranchTy M)))
                        (liftSubstCompKeep (liftSubst sigma))
                        ∙ subTyComp rho (liftSubst (liftSubst sigma)) (sigmaBranchTy M))))
                  (eqSubDerivTmEqComp
                    dm
                    (composeTwoBindersEq fits dAσ dBσ fitsEq2)))))

      resultPath :
        termEq []
          (subTm sigma (tmElSigma d m))
          (subTm sigma (tmElSigma d' m'))
          (subTy sigma (subTy (singleSubst d) M))
          ≡
        termEq []
          (tmElSigma (subTm sigma d) (subTm (liftSubst (liftSubst sigma)) m))
          (tmElSigma (subTm sigma d') (subTm (liftSubst (liftSubst sigma)) m'))
          (subTy (singleSubst (subTm sigma d)) (subTy (liftSubst sigma) M))
      resultPath =
        cong₃
          (termEq [])
          refl
          refl
          (subTyComp sigma (singleSubst d) M
            ∙ cong (λ rho -> subTy rho M) (sym (singleSubstCompLift sigma d))
            ∙ sym (subTyComp (singleSubst (subTm sigma d)) (liftSubst sigma) M))
    in
    subst
      (λ J -> Computable J)
      (sym resultPath)
      (compESigmaClosed compTransTmClosed compConvTmEqClosed compM compdd compdm)

  substDerivTmEqCompEQtrEq
    : {gamma : Ctx} {A L : RawType} {l l' p p' : RawTerm} {sigma : Subst}
    -> Derivable (isType ((tyQtr A) ∷ gamma) L)
    -> Derivable (termEq gamma p p' (tyQtr A))
    -> Derivable (termEq (A ∷ gamma) l l' (qtrBranchTy L))
    -> Derivable
         (termEq (wkTyBy 1 A ∷ A ∷ gamma)
           (wkTmBy 1 l)
           (renTm qtrSecondBranchRen l)
           (qtrCohTy L))
    -> Derivable
         (termEq (wkTyBy 1 A ∷ A ∷ gamma)
           (wkTmBy 1 l')
           (renTm qtrSecondBranchRen l')
           (qtrCohTy L))
    -> FitsSubst [] gamma sigma
    -> Computable
         (termEq []
           (subTm sigma (tmElQtr l p))
           (subTm sigma (tmElQtr l' p'))
           (subTy sigma (subTy (singleSubst p) L)))
  substDerivTmEqCompEQtrEq
    {gamma = gamma} {A = A} {L = L} {l = l} {l' = l'} {p = p} {p' = p'} {sigma = sigma}
    dL dp dl dcoh dcoh' fits =
    let
      compdp = substDerivTmEqComp dp fits
      compQtrσ = compTmToCompTy (compTmEqLeft compdp)
      dQtrσ = compToDerivable compQtrσ
      tyInv = invertQtrTy compQtrσ evalQtr
      compAσ = ClosedQtrTyInv.qtrTyCompBase tyInv
      dAσ = compToDerivable compAσ
      dWkAσ =
        subst
          (λ T -> Derivable (isType (subTy sigma A ∷ []) T))
          (sym (wkTyLiftSubst sigma A))
          (weakenTy dAσ (wfCons wfNil dAσ))
      compL = openHypTy1 fits dQtrσ dL

      compl =
        subst
          (λ T ->
            HypComputable
              (termEq (subTy sigma A ∷ [])
                (subTm (liftSubst sigma) l)
                (subTm (liftSubst sigma) l')
                T))
          (qtrBranchTyLiftComp sigma L)
          (openHypTmEq1
            fits
            dAσ
            dl)

      compcoh =
        subst
          (λ J -> HypComputable J)
          (cong
            (λ T ->
              termEq (T ∷ subTy sigma A ∷ [])
                (subTm (liftSubst (liftSubst sigma)) (wkTmBy 1 l))
                (subTm (liftSubst (liftSubst sigma)) (renTm qtrSecondBranchRen l))
                (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
            (wkTyLiftSubst sigma A)
            ∙ cong
                (λ t ->
                  termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                    t
                    (subTm (liftSubst (liftSubst sigma)) (renTm qtrSecondBranchRen l))
                    (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
                (wkTmLiftSubst (liftSubst sigma) l)
            ∙ cong
                (λ u ->
                  termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                    (wkTmBy 1 (subTm (liftSubst sigma) l))
                    u
                    (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
                (qtrSecondBranchTmLiftComp sigma l)
            ∙ cong
                (λ T ->
                  termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                    (wkTmBy 1 (subTm (liftSubst sigma) l))
                    (renTm qtrSecondBranchRen (subTm (liftSubst sigma) l))
                    T)
                (qtrCohTyLiftComp sigma L))
          (openHypTmEq2
            fits
            dAσ
            dWkAσ
            dcoh)

      compcoh' =
        subst
          (λ J -> HypComputable J)
          (cong
            (λ T ->
              termEq (T ∷ subTy sigma A ∷ [])
                (subTm (liftSubst (liftSubst sigma)) (wkTmBy 1 l'))
                (subTm (liftSubst (liftSubst sigma)) (renTm qtrSecondBranchRen l'))
                (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
            (wkTyLiftSubst sigma A)
            ∙ cong
                (λ t ->
                  termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                    t
                    (subTm (liftSubst (liftSubst sigma)) (renTm qtrSecondBranchRen l'))
                    (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
                (wkTmLiftSubst (liftSubst sigma) l')
            ∙ cong
                (λ u ->
                  termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                    (wkTmBy 1 (subTm (liftSubst sigma) l'))
                    u
                    (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
                (qtrSecondBranchTmLiftComp sigma l')
            ∙ cong
                (λ T ->
                  termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                    (wkTmBy 1 (subTm (liftSubst sigma) l'))
                    (renTm qtrSecondBranchRen (subTm (liftSubst sigma) l'))
                    T)
                (qtrCohTyLiftComp sigma L))
          (openHypTmEq2
            fits
            dAσ
            dWkAσ
            dcoh')

      resultPath :
        termEq []
          (subTm sigma (tmElQtr l p))
          (subTm sigma (tmElQtr l' p'))
          (subTy sigma (subTy (singleSubst p) L))
          ≡
        termEq []
          (tmElQtr (subTm (liftSubst sigma) l) (subTm sigma p))
          (tmElQtr (subTm (liftSubst sigma) l') (subTm sigma p'))
          (subTy (singleSubst (subTm sigma p)) (subTy (liftSubst sigma) L))
      resultPath =
        cong₃
          (termEq [])
          refl
          refl
          (subTyComp sigma (singleSubst p) L
            ∙ cong (λ rho -> subTy rho L) (sym (singleSubstCompLift sigma p))
            ∙ sym (subTyComp (singleSubst (subTm sigma p)) (liftSubst sigma) L))
    in
    subst
      (λ J -> Computable J)
      (sym resultPath)
      (compEQtrClosed compTransTmClosed compSymTmClosed compConvTmEqClosed
        compL compdp compl compcoh compcoh')

  substDerivTmEqCompCQtr
    : {gamma : Ctx} {A L : RawType} {a l : RawTerm} {sigma : Subst}
    -> Derivable (isType ((tyQtr A) ∷ gamma) L)
    -> Derivable (hasTy gamma a A)
    -> Derivable (hasTy (A ∷ gamma) l (qtrBranchTy L))
    -> Derivable
         (termEq (wkTyBy 1 A ∷ A ∷ gamma)
           (wkTmBy 1 l)
           (renTm qtrSecondBranchRen l)
           (qtrCohTy L))
    -> FitsSubst [] gamma sigma
    -> Computable
         (termEq []
           (subTm sigma (tmElQtr l (tmClass a)))
           (subTm sigma (subTm (qtrCompSub a) l))
           (subTy sigma (subTy (singleSubst (tmClass a)) L)))
  substDerivTmEqCompCQtr
    {gamma = gamma} {A = A} {L = L} {a = a} {l = l} {sigma = sigma}
    dL da dl dcoh fits =
    let
      compa = substDerivTmComp da fits
      compAσ = compTmToCompTy compa
      dAσ = compToDerivable compAσ
      dQtrσ = compToDerivable (compFQtrClosed compAσ)
      dWkAσ =
        subst
          (λ T -> Derivable (isType (subTy sigma A ∷ []) T))
          (sym (wkTyLiftSubst sigma A))
          (weakenTy dAσ (wfCons wfNil dAσ))
      compL = openHypTy1 fits dQtrσ dL

      compl =
        subst
          (λ T ->
            HypComputable
              (hasTy (subTy sigma A ∷ [])
                (subTm (liftSubst sigma) l)
                T))
          (qtrBranchTyLiftComp sigma L)
          (openHypTm1
            fits
            dAσ
            dl)

      compcoh =
        subst
          (λ J -> HypComputable J)
          (cong
            (λ T ->
              termEq (T ∷ subTy sigma A ∷ [])
                (subTm (liftSubst (liftSubst sigma)) (wkTmBy 1 l))
                (subTm (liftSubst (liftSubst sigma)) (renTm qtrSecondBranchRen l))
                (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
            (wkTyLiftSubst sigma A)
            ∙ cong
                (λ t ->
                  termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                    t
                    (subTm (liftSubst (liftSubst sigma)) (renTm qtrSecondBranchRen l))
                    (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
                (wkTmLiftSubst (liftSubst sigma) l)
            ∙ cong
                (λ u ->
                  termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                    (wkTmBy 1 (subTm (liftSubst sigma) l))
                    u
                    (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
                (qtrSecondBranchTmLiftComp sigma l)
            ∙ cong
                (λ T ->
                  termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                    (wkTmBy 1 (subTm (liftSubst sigma) l))
                    (renTm qtrSecondBranchRen (subTm (liftSubst sigma) l))
                    T)
                (qtrCohTyLiftComp sigma L))
          (openHypTmEq2
            fits
            dAσ
            dWkAσ
            dcoh)

      resultPath :
        termEq []
          (subTm sigma (tmElQtr l (tmClass a)))
          (subTm sigma (subTm (qtrCompSub a) l))
          (subTy sigma (subTy (singleSubst (tmClass a)) L))
          ≡
        termEq []
          (tmElQtr (subTm (liftSubst sigma) l) (tmClass (subTm sigma a)))
          (subTm (qtrCompSub (subTm sigma a)) (subTm (liftSubst sigma) l))
          (subTy (singleSubst (tmClass (subTm sigma a))) (subTy (liftSubst sigma) L))
      resultPath =
        cong₃
          (termEq [])
          refl
          (subTmComp sigma (qtrCompSub a) l
            ∙ cong (λ rho -> subTm rho l) (qtrCompSubLiftComp sigma a)
            ∙ sym (subTmComp (qtrCompSub (subTm sigma a)) (liftSubst sigma) l))
          (subTyComp sigma (singleSubst (tmClass a)) L
            ∙ cong (λ rho -> subTy rho L) (sym (singleSubstCompLift sigma (tmClass a)))
            ∙ sym (subTyComp (singleSubst (tmClass (subTm sigma a))) (liftSubst sigma) L))
    in
    subst
      (λ J -> Computable J)
      (sym resultPath)
      (compCQtrClosed compL compa compl compcoh)

  substDerivTmEqComp (reflTm d) fits =
    compReflTmClosed (substDerivTmComp d fits)
  substDerivTmEqComp (symTm d) fits =
    compSymTmClosed (substDerivTmEqComp d fits)
  substDerivTmEqComp (transTm d₁ d₂) fits =
    compTransTmClosed (substDerivTmEqComp d₁ fits) (substDerivTmEqComp d₂ fits)
  substDerivTmEqComp (convEq d dAB) fits =
    compConvTmEqClosed (substDerivTmEqComp d fits) (substDerivTyEqComp dAB fits)
  substDerivTmEqComp (cTop d) fits =
    compCTopClosed (substDerivTmComp d fits)
  substDerivTmEqComp {sigma = sigma}
    (iSigmaEq {a = a} {b = b} {d = d} {A = A} {B = B} dac dbd dA dB) fits =
    let
      compac = substDerivTmEqComp dac fits
      compbdRaw = substDerivTmEqComp dbd fits
      compA = substDerivTyComp dA fits
      dAσ = compToDerivable compA
      compB = openHypTy1 fits dAσ dB
      compa = compTmEqLeft compac
      compcA = compTmEqRightClosed compac
      compbd =
        subst
          (λ T -> Computable (termEq [] (subTm sigma b) (subTm sigma d) T))
          (subTyComp sigma (singleSubst a) B
            ∙ cong (λ rho -> subTy rho B) (sym (singleSubstCompLift sigma a))
            ∙ sym (subTyComp (singleSubst (subTm sigma a)) (liftSubst sigma) B))
          compbdRaw
      compb = compTmEqLeft compbd
      compdA = compTmEqRightClosed compbd
      compd =
        compConvTmClosed compdA (compSingleEqSubstTyClosed compB compac)
      compPairLeft = compISigmaClosed compa compb (compFSigmaClosed compA compB)
      compPairRight = compISigmaClosed compcA compd (compFSigmaClosed compA compB)
    in
    compTmEqClosedSigma
      (iSigmaEq (compToDerivable compac) (compToDerivable compbd) dAσ (hypCompToDerivable compB))
      compPairLeft
      compPairRight
      evalSigma
      evalPair
      evalPair
      compac
      compbd
  substDerivTmEqComp (eSigmaEq dM dd dm) fits =
    substDerivTmEqCompESigmaEq dM dd dm fits
  substDerivTmEqComp (eQtrEq dL dp dl dcoh dcoh') fits =
    substDerivTmEqCompEQtrEq dL dp dl dcoh dcoh' fits
  substDerivTmEqComp {gamma = gamma} {sigma = sigma}
    (cSigma {A = A} {B = B} {M = M} {b = b} {c = c} {m = m} dM db dc dm) fits =
    let
      compb = substDerivTmComp db fits
      sigmaTy = ctxSuffixTy {delta = []} {gamma = gamma} {A = tySigma A B} (derivToCtxWF dM)
      compSigma = substDerivTyComp sigmaTy fits
      dSigmaσ = compToDerivable compSigma
      tyInv = invertSigmaTy compSigma evalSigma
      compAσ = ClosedSigmaTyInv.sigmaTyCompHead tyInv
      dAσ = compToDerivable compAσ
      compBσ = hypComputableTy (ClosedSigmaTyInv.sigmaTyFamDeriv tyInv)
      dBσ = hypCompToDerivable compBσ
      compM = openHypTy1 fits dSigmaσ dM

      compdm =
        let
          lifted1 : FitsSubst (subTy sigma A ∷ []) (A ∷ gamma) (liftSubst sigma)
          lifted1 =
            subst
              (λ rho -> FitsSubst (subTy sigma A ∷ []) (A ∷ gamma) rho)
              (liftSubstCompKeep sigma)
              (liftFitsOne fits dAσ)
          compBranchTy =
            subst
              (λ T' ->
                HypComputable (isType (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) T'))
              (cong (λ rho -> subTy rho (sigmaBranchTy M))
                (liftSubstCompKeep (liftSubst sigma)))
              (hypTyOpen
                nonemptyNeNil
                (substTyRule (assocTy dm) (liftFits lifted1 dBσ))
                (λ rho fits2 _ ->
                  subst
                    (λ T' -> Computable (isType [] T'))
                    (sym
                      (cong (λ theta -> subTy rho (subTy theta (sigmaBranchTy M)))
                        (liftSubstCompKeep (liftSubst sigma))
                        ∙ subTyComp rho (liftSubst (liftSubst sigma)) (sigmaBranchTy M)))
                    (substDerivTyComp
                      (assocTy dm)
                      (composeTwoBinders fits dAσ dBσ fits2)))
                (λ rho eta fitsEq2 _ ->
                  subst
                    (λ J -> Computable J)
                    (sym
                      (cong₂ (typeEq [])
                        (cong (λ theta -> subTy rho (subTy theta (sigmaBranchTy M)))
                          (liftSubstCompKeep (liftSubst sigma))
                          ∙ subTyComp rho (liftSubst (liftSubst sigma)) (sigmaBranchTy M))
                        (cong (λ theta -> subTy eta (subTy theta (sigmaBranchTy M)))
                          (liftSubstCompKeep (liftSubst sigma))
                          ∙ subTyComp eta (liftSubst (liftSubst sigma)) (sigmaBranchTy M))))
                    (eqSubDerivTyComp
                      (assocTy dm)
                      (composeTwoBindersEq fits dAσ dBσ fitsEq2))))
        in
        subst
          (λ J -> HypComputable J)
          (cong
            (hasTy (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ [])
              (subTm (liftSubst (liftSubst sigma)) m))
            (sigmaBranchTyLiftComp sigma M))
          (subst
            (λ J -> HypComputable J)
            (cong₂
              (hasTy (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []))
              (cong (λ rho -> subTm rho m) (liftSubstCompKeep (liftSubst sigma)))
              (cong (λ rho -> subTy rho (sigmaBranchTy M))
                (liftSubstCompKeep (liftSubst sigma))))
            (hypTmOpen
              nonemptyNeNil
              (substTmRule dm (liftFits lifted1 dBσ))
              (subst
                (λ T' ->
                  HypComputable (isType (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) T'))
                (sym
                  (cong (λ rho -> subTy rho (sigmaBranchTy M))
                    (liftSubstCompKeep (liftSubst sigma))))
                compBranchTy)
              (λ rho fits2 _ ->
                subst
                  (λ J -> Computable J)
                  (sym
                    (cong₂ (hasTy [])
                      (cong (λ theta -> subTm rho (subTm theta m))
                        (liftSubstCompKeep (liftSubst sigma))
                        ∙ subTmComp rho (liftSubst (liftSubst sigma)) m)
                      (cong (λ theta -> subTy rho (subTy theta (sigmaBranchTy M)))
                        (liftSubstCompKeep (liftSubst sigma))
                        ∙ subTyComp rho (liftSubst (liftSubst sigma)) (sigmaBranchTy M))))
                  (substDerivTmComp
                    dm
                    (composeTwoBinders fits dAσ dBσ fits2)))
              (λ rho eta fitsEq2 _ ->
                subst
                  (λ J -> Computable J)
                  (sym
                    (cong₃ (termEq [])
                      (cong (λ theta -> subTm rho (subTm theta m))
                        (liftSubstCompKeep (liftSubst sigma))
                        ∙ subTmComp rho (liftSubst (liftSubst sigma)) m)
                      (cong (λ theta -> subTm eta (subTm theta m))
                        (liftSubstCompKeep (liftSubst sigma))
                        ∙ subTmComp eta (liftSubst (liftSubst sigma)) m)
                      (cong (λ theta -> subTy rho (subTy theta (sigmaBranchTy M)))
                        (liftSubstCompKeep (liftSubst sigma))
                        ∙ subTyComp rho (liftSubst (liftSubst sigma)) (sigmaBranchTy M))))
                  (eqSubDerivTmComp
                    dm
                    (composeTwoBindersEq fits dAσ dBσ fitsEq2)))))

      compcRaw = substDerivTmComp dc fits
      compc =
        subst
          (λ T -> Computable (hasTy [] (subTm sigma c) T))
          (subTyComp sigma (singleSubst b) B
            ∙ cong (λ rho -> subTy rho B) (sym (singleSubstCompLift sigma b))
            ∙ sym (subTyComp (singleSubst (subTm sigma b)) (liftSubst sigma) B))
          compcRaw

      resultPath :
        termEq []
          (subTm sigma (tmElSigma (tmPair b c) m))
          (subTm sigma (subTm (sigmaCompSub b c) m))
          (subTy sigma (subTy (singleSubst (tmPair b c)) M))
          ≡
        termEq []
          (tmElSigma (tmPair (subTm sigma b) (subTm sigma c))
            (subTm (liftSubst (liftSubst sigma)) m))
          (subTm (sigmaCompSub (subTm sigma b) (subTm sigma c))
            (subTm (liftSubst (liftSubst sigma)) m))
          (subTy (singleSubst (tmPair (subTm sigma b) (subTm sigma c)))
            (subTy (liftSubst sigma) M))
      resultPath =
        cong₃
          (termEq [])
          refl
          (subTmComp sigma (sigmaCompSub b c) m
            ∙ cong (λ rho -> subTm rho m) (sigmaCompSubLiftComp sigma b c)
            ∙ sym (subTmComp (sigmaCompSub (subTm sigma b) (subTm sigma c))
                (liftSubst (liftSubst sigma)) m))
          (subTyComp sigma (singleSubst (tmPair b c)) M
            ∙ cong (λ rho -> subTy rho M) (sym (singleSubstCompLift sigma (tmPair b c)))
            ∙ sym (subTyComp (singleSubst (tmPair (subTm sigma b) (subTm sigma c)))
                (liftSubst sigma) M))
    in
    subst
      (λ J -> Computable J)
      (sym resultPath)
      (compCSigmaClosed compM compb compc compdm)
  substDerivTmEqComp (iEqEq d) fits =
    compReflTm (compIEqClosed (compTmEqLeft (substDerivTmEqComp d fits)))
  substDerivTmEqComp (eEqStar dp dA da db) fits =
    compEEqClosed (substDerivTmComp dp fits)
  substDerivTmEqComp (cEq dp dA da db) fits =
    compCEqClosed (substDerivTmComp dp fits)
  substDerivTmEqComp (iQtrEq da db) fits =
    compIQtrEqClosed (substDerivTmComp da fits) (substDerivTmComp db fits)
  substDerivTmEqComp (cQtr dL da dl dcoh) fits =
    substDerivTmEqCompCQtr dL da dl dcoh fits
  substDerivTmEqComp {sigma = sigma} (weakenTmEq {delta = delta} {t = t} {u = u} {A = A} d wf) fits =
    subst
      (λ J -> Computable J)
      (cong₃ (termEq [])
        (sym (subTmWkBy sigma (length delta) t))
        (sym (subTmWkBy sigma (length delta) u))
        (sym (subTyWkBy sigma (length delta) A)))
      (substDerivTmEqComp d (dropFits delta fits))
  substDerivTmEqComp {sigma = sigma} (substTmEqRule {sigma = sigma'} {t = t} {u = u} {A = A} d fits') fits =
    let
      composedFits = composeFits fits fits'
    in
    subst
      (λ J -> Computable J)
      (cong₃ (termEq [])
        (sym (subTmComp sigma sigma' t))
        (sym (subTmComp sigma sigma' u))
        (sym (subTyComp sigma sigma' A)))
      (substDerivTmEqComp d composedFits)
  substDerivTmEqComp {sigma = sigma}
    (eqSubTmRule {sigma = sigma'} {tau = tau'} {t = t} {A = A} d fitsEq') fits =
    let
      composedFitsEq = composeFitsEq fits fitsEq'
    in
    subst
      (λ J -> Computable J)
      (cong₃ (termEq [])
        (sym (subTmComp sigma sigma' t))
        (sym (subTmComp sigma tau' t))
        (sym (subTyComp sigma sigma' A)))
      (eqSubDerivTmComp d composedFitsEq)
  substDerivTmEqComp {sigma = sigma}
    (eqSubTmEqRule {sigma = sigma'} {tau = tau'} {t = t} {u = u} {A = A} d fitsEq') fits =
    let
      composedFitsEq = composeFitsEq fits fitsEq'
    in
    subst
      (λ J -> Computable J)
      (cong₃ (termEq [])
        (sym (subTmComp sigma sigma' t))
        (sym (subTmComp sigma tau' u))
        (sym (subTyComp sigma sigma' A)))
      (eqSubDerivTmEqComp d composedFitsEq)
  eqSubDerivTyComp (fTop wf) fitsEq = compReflTy compFTopClosed
  eqSubDerivTyComp {gamma = gamma} {sigma = sigma} {tau = tau}
    (fSigma {A = A} {B = B} dA dB) fitsEq =
    let
      sigmaFits = fitsEqSubstLeft fitsEq
      compAA' = eqSubDerivTyComp dA fitsEq
      compA = compTyEqLeft compAA'
      compA' = compTyEqRightClosed compAA'
      dAσ = substTyRule dA sigmaFits
      compB =
        subst
          (λ T -> HypComputable (isType (subTy sigma A ∷ []) T))
          (cong (λ rho -> subTy rho B) (liftSubstCompKeepNR sigma))
          (hypTyOpen
            nonemptyNeNil
            (substTyRule dB (liftFitsOneNR sigmaFits dAσ))
            (λ rho fits2 _ ->
              subst
                (λ T -> Computable (isType [] T))
                (sym
                  (cong (λ theta -> subTy rho (subTy theta B)) (liftSubstCompKeepNR sigma)
                    ∙ subTyComp rho (liftSubst sigma) B))
                (substDerivTyComp
                  dB
                  (composeOneBinderNR sigmaFits dAσ fits2)))
            (λ rho eta fitsEq2 _ ->
              subst
                (λ J -> Computable J)
                (sym
                  (cong₂ (typeEq [])
                    (cong (λ theta -> subTy rho (subTy theta B)) (liftSubstCompKeepNR sigma)
                      ∙ subTyComp rho (liftSubst sigma) B)
                    (cong (λ theta -> subTy eta (subTy theta B)) (liftSubstCompKeepNR sigma)
                      ∙ subTyComp eta (liftSubst sigma) B)))
                (eqSubDerivTyComp
                  dB
                  (composeOneBinderEqNR sigmaFits dAσ fitsEq2))))
      compBD =
        let
          liftedEq :
            FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma)
              (liftSubst sigma)
              (liftSubst tau)
          liftedEq =
            subst
              (λ rho -> FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma) rho (liftSubst tau))
              (liftSubstCompKeepNR sigma)
              (subst
                (λ rho ->
                  FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma)
                    (consSubst (var zero) (compSub (keepSubstBy 1) sigma))
                    rho)
                (liftSubstCompKeepNR tau)
                (liftFitsEqOneNR fitsEq dAσ))
        in
        hypTyEqOpen
          nonemptyNeNil
          (eqSubTyRule dB liftedEq)
          compB
          (λ rho fits2 _ ->
            let
              composedFitsEq = composeFitsEq fits2 liftedEq
            in
            subst
              (λ J -> Computable J)
              (sym
                (cong₂ (typeEq [])
                  (subTyComp rho (liftSubst sigma) B)
                  (subTyComp rho (liftSubst tau) B)))
              (eqSubDerivTyComp
                dB
                composedFitsEq))
          (λ rho eta fitsEq2 _ ->
            let
              composedFitsEq = composeEqFitsEq fitsEq2 liftedEq
            in
            subst
              (λ J -> Computable J)
              (sym
                (cong₂ (typeEq [])
                  (subTyComp rho (liftSubst sigma) B)
                  (subTyComp eta (liftSubst tau) B)))
              (eqSubDerivTyComp
                dB
                composedFitsEq))
      compSigmaA = compFSigmaClosed compA (hypTyEqLeft compBD)
      compSigmaA' = compFSigmaClosed compA' (compTransportFamilyTy compAA' (hypTyEqRight compBD))
    in
    compTyEqClosedSigma
      (fSigmaEq (compToDerivable compAA') (hypCompToDerivable compBD))
      compSigmaA
      compSigmaA'
      evalSigma
      evalSigma
      compAA'
      (hypCompToDerivable compBD)
  eqSubDerivTyComp (fEq dA da db) fitsEq =
    let
      compAA' = eqSubDerivTyComp dA fitsEq
      compac = eqSubDerivTmComp da fitsEq
      compbd = eqSubDerivTmComp db fitsEq
      compA = compTyEqLeft compAA'
      compA' = compTyEqRightClosed compAA'
      compa = compTmEqLeft compac
      compb = compTmEqLeft compbd
      compcA = compTmEqRightClosed compac
      compdA = compTmEqRightClosed compbd
      compc = compConvTmClosed compcA compAA'
      compd = compConvTmClosed compdA compAA'
      compEqA = compFEqClosed compA compa compb
      compEqA' = compFEqClosed compA' compc compd
    in
    compTyEqClosedEq
      (fEqEq (compToDerivable compAA') (compToDerivable compac) (compToDerivable compbd))
      compEqA
      compEqA'
      evalEq
      evalEq
      compAA'
      compac
      compbd
  eqSubDerivTyComp (fQtr dA) fitsEq =
    let
      compAA' = eqSubDerivTyComp dA fitsEq
    in
    compTyEqClosedQtr
      (fQtrEq (compToDerivable compAA'))
      (compFQtrClosed (compTyEqLeft compAA'))
      (compFQtrClosed (compTyEqRightClosed compAA'))
      evalQtr
      evalQtr
      compAA'
  eqSubDerivTyComp {sigma = sigma} {tau = tau}
    (weakenTy {delta = delta} {A = A} d wf) fitsEq =
    subst
      (λ J -> Computable J)
      (cong₂ (typeEq [])
        (sym (subTyWkBy sigma (length delta) A))
        (sym (subTyWkBy tau (length delta) A)))
      (eqSubDerivTyComp d (dropFitsEq delta fitsEq))
  eqSubDerivTyComp {sigma = sigma} {tau = tau}
    (substTyRule {sigma = sigma'} {A = A} d fits') fitsEq =
    let
      composedFitsEq = composeEqFits fitsEq fits'
    in
    subst
      (λ J -> Computable J)
      (cong₂ (typeEq [])
        (sym (subTyComp sigma sigma' A))
        (sym (subTyComp tau sigma' A)))
      (eqSubDerivTyComp d composedFitsEq)

  eqSubDerivTyEqComp : {gamma : Ctx} {A B : RawType} {sigma tau : Subst}
    -> Derivable (typeEq gamma A B)
    -> FitsEqSubst [] gamma sigma tau
    -> Computable (typeEq [] (subTy sigma A) (subTy tau B))
  eqSubDerivTyEqComp (reflTy d) fitsEq =
    eqSubDerivTyComp d fitsEq
  eqSubDerivTyEqComp (symTy d) fitsEq =
    let
      sigmaFits = fitsEqSubstLeft fitsEq
    in
    compTransTyClosed
      (compSymTyClosed (substDerivTyEqComp d sigmaFits))
      (eqSubDerivTyComp (assocTyLeft d) fitsEq)
  eqSubDerivTyEqComp (transTy d₁ d₂) fitsEq =
    let
      sigmaFits = fitsEqSubstLeft fitsEq
    in
    compTransTyClosed
      (substDerivTyEqComp d₁ sigmaFits)
      (eqSubDerivTyEqComp d₂ fitsEq)
  eqSubDerivTyEqComp {gamma = gamma} {sigma = sigma} {tau = tau}
    (fSigmaEq {A = A} {B = B} {D = D} dAC dBD) fitsEq =
    let
      sigmaFits = fitsEqSubstLeft fitsEq
      compAC = eqSubDerivTyEqComp dAC fitsEq
      compA = compTyEqLeft compAC
      compC = compTyEqRightClosed compAC
      dAσ = compToDerivable compA
      compBD =
        let
          liftedEq :
            FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma)
              (liftSubst sigma)
              (liftSubst tau)
          liftedEq =
            subst
              (λ rho -> FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma) rho (liftSubst tau))
              (liftSubstCompKeep sigma)
              (subst
                (λ rho ->
                  FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma)
                    (consSubst (var zero) (compSub (keepSubstBy 1) sigma))
                    rho)
                (liftSubstCompKeep tau)
                (liftFitsEqOne fitsEq dAσ))
        in
        hypTyEqOpen
          nonemptyNeNil
          (eqSubTyEqRule dBD liftedEq)
          (openHypTy1 sigmaFits dAσ (assocTyLeft dBD))
          (λ rho fits2 _ ->
            let
              composedFitsEq = composeFitsEq fits2 liftedEq
            in
            subst
              (λ J -> Computable J)
              (sym
                (cong₂ (typeEq [])
                  (subTyComp rho (liftSubst sigma) B)
                  (subTyComp rho (liftSubst tau) D)))
              (eqSubDerivTyEqComp
                dBD
                composedFitsEq))
          (λ rho eta fitsEq2 _ ->
            let
              composedFitsEq = composeEqFitsEq fitsEq2 liftedEq
            in
            subst
              (λ J -> Computable J)
              (sym
                (cong₂ (typeEq [])
                  (subTyComp rho (liftSubst sigma) B)
                  (subTyComp eta (liftSubst tau) D)))
              (eqSubDerivTyEqComp
                dBD
                composedFitsEq))
      compSigmaA = compFSigmaClosed compA (hypTyEqLeft compBD)
      compSigmaC = compFSigmaClosed compC (compTransportFamilyTy compAC (hypTyEqRight compBD))
    in
    compTyEqClosedSigma
      (fSigmaEq (compToDerivable compAC) (hypCompToDerivable compBD))
      compSigmaA
      compSigmaC
      evalSigma
      evalSigma
      compAC
      (hypCompToDerivable compBD)
  eqSubDerivTyEqComp {sigma = sigma} {tau = tau}
    (weakenTyEq {delta = delta} {A = A} {B = B} d wf) fitsEq =
    subst
      (λ J -> Computable J)
      (cong₂ (typeEq [])
        (sym (subTyWkBy sigma (length delta) A))
        (sym (subTyWkBy tau (length delta) B)))
      (eqSubDerivTyEqComp d (dropFitsEq delta fitsEq))
  eqSubDerivTyEqComp {sigma = sigma} {tau = tau}
    (substTyEqRule {sigma = sigma'} {A = A} {B = B} d fits') fitsEq =
    let
      composedFitsEq = composeEqFits fitsEq fits'
    in
    subst
      (λ J -> Computable J)
      (cong₂ (typeEq [])
        (sym (subTyComp sigma sigma' A))
        (sym (subTyComp tau sigma' B)))
      (eqSubDerivTyEqComp d composedFitsEq)
  eqSubDerivTyEqComp {sigma = sigma} {tau = tau}
    (eqSubTyRule {sigma = sigma'} {tau = tau'} {A = A} d fitsEq') fitsEq =
    let
      composedFitsEq = composeEqFitsEq fitsEq fitsEq'
    in
    subst
      (λ J -> Computable J)
      (cong₂ (typeEq [])
        (sym (subTyComp sigma sigma' A))
        (sym (subTyComp tau tau' A)))
      (eqSubDerivTyComp d composedFitsEq)
  eqSubDerivTyEqComp {sigma = sigma} {tau = tau}
    (eqSubTyEqRule {sigma = sigma'} {tau = tau'} {A = A} {B = B} d fitsEq') fitsEq =
    let
      composedFitsEq = composeEqFitsEq fitsEq fitsEq'
    in
    subst
      (λ J -> Computable J)
      (cong₂ (typeEq [])
        (sym (subTyComp sigma sigma' A))
        (sym (subTyComp tau tau' B)))
      (eqSubDerivTyEqComp d composedFitsEq)
  eqSubDerivTyEqComp (fEqEq dAC dac dbd) fitsEq =
    let
      compAC = eqSubDerivTyEqComp dAC fitsEq
      compac = eqSubDerivTmEqComp dac fitsEq
      compbd = eqSubDerivTmEqComp dbd fitsEq
      compA = compTyEqLeft compAC
      compC = compTyEqRightClosed compAC
      compa = compTmEqLeft compac
      compb = compTmEqLeft compbd
      compcA = compTmEqRightClosed compac
      compdA = compTmEqRightClosed compbd
      compc = compConvTmClosed compcA compAC
      compd = compConvTmClosed compdA compAC
      compEqA = compFEqClosed compA compa compb
      compEqC = compFEqClosed compC compc compd
    in
    compTyEqClosedEq
      (fEqEq (compToDerivable compAC) (compToDerivable compac) (compToDerivable compbd))
      compEqA
      compEqC
      evalEq
      evalEq
      compAC
      compac
      compbd
  eqSubDerivTyEqComp (fQtrEq dAB) fitsEq =
    let
      compAB = eqSubDerivTyEqComp dAB fitsEq
    in
    compTyEqClosedQtr
      (fQtrEq (compToDerivable compAB))
      (compFQtrClosed (compTyEqLeft compAB))
      (compFQtrClosed (compTyEqRightClosed compAB))
      evalQtr
      evalQtr
      compAB

  eqSubDerivTmCompEQtr
    : {gamma : Ctx} {A L : RawType} {l p : RawTerm} {sigma tau : Subst}
    -> Derivable (isType ((tyQtr A) ∷ gamma) L)
    -> Derivable (hasTy gamma p (tyQtr A))
    -> Derivable (hasTy (A ∷ gamma) l (qtrBranchTy L))
    -> Derivable
         (termEq (wkTyBy 1 A ∷ A ∷ gamma)
           (wkTmBy 1 l)
           (renTm qtrSecondBranchRen l)
           (qtrCohTy L))
    -> FitsEqSubst [] gamma sigma tau
    -> Computable
         (termEq []
           (subTm sigma (tmElQtr l p))
           (subTm tau (tmElQtr l p))
           (subTy sigma (subTy (singleSubst p) L)))
  eqSubDerivTmCompEQtr
    {gamma = gamma} {A = A} {L = L} {l = l} {p = p} {sigma = sigma} {tau = tau}
    dL dp dl dcoh fitsEq =
    let
      sigmaFits = fitsEqSubstLeft fitsEq
      compp = eqSubDerivTmComp dp fitsEq
      compQtrσ = compTmToCompTy (compTmEqLeft compp)
      dQtrσ = compToDerivable compQtrσ
      tyInv = invertQtrTy compQtrσ evalQtr
      compAσ = ClosedQtrTyInv.qtrTyCompBase tyInv
      dAσ = compToDerivable compAσ
      dWkBaseσ = weakenTy dAσ (wfCons wfNil dAσ)
      dWkAσ =
        subst
          (λ T -> Derivable (isType (subTy sigma A ∷ []) T))
          (sym (wkTyLiftSubst sigma A))
          dWkBaseσ
      wkCtxWF : CtxWF (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
      wkCtxWF = wfCons (wfCons wfNil dAσ) dWkBaseσ
      compL = openHypTy1 sigmaFits dQtrσ dL

      branchEq =
        subst
          (λ T ->
            HypComputable
              (termEq (subTy sigma A ∷ [])
                (subTm (liftSubst sigma) l)
                (subTm (liftSubst tau) l)
                T))
          (qtrBranchTyLiftComp sigma L)
          (let
             liftedEq :
               FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma)
                 (liftSubst sigma)
                 (liftSubst tau)
             liftedEq =
               subst
                 (λ rho -> FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma) rho (liftSubst tau))
                 (liftSubstCompKeep sigma)
                 (subst
                   (λ rho ->
                     FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma)
                       (consSubst (var zero) (compSub (keepSubstBy 1) sigma))
                       rho)
                   (liftSubstCompKeep tau)
                   (liftFitsEqOne fitsEq dAσ))
           in
           hypTmEqOpen
             nonemptyNeNil
             (eqSubTmRule dl liftedEq)
             (openHypTm1
               sigmaFits
               dAσ
               dl)
             (λ rho fits2 _ ->
               let
                 composedFitsEq = composeFitsEq fits2 liftedEq
               in
               subst
                 (λ J -> Computable J)
                 (sym
                   (cong₃ (termEq [])
                     (subTmComp rho (liftSubst sigma) l)
                     (subTmComp rho (liftSubst tau) l)
                     (subTyComp rho (liftSubst sigma) (qtrBranchTy L))))
                 (eqSubDerivTmComp
                   dl
                   composedFitsEq))
             (λ rho eta fitsEq2 _ ->
               let
                 composedFitsEq = composeEqFitsEq fitsEq2 liftedEq
               in
               subst
                 (λ J -> Computable J)
                 (sym
                   (cong₃ (termEq [])
                     (subTmComp rho (liftSubst sigma) l)
                     (subTmComp eta (liftSubst tau) l)
                     (subTyComp rho (liftSubst sigma) (qtrBranchTy L))))
                 (eqSubDerivTmComp
                   dl
                   composedFitsEq)))

      branchEqWk =
        subst
          (λ J -> HypComputable J)
          (cong
            (λ T ->
              termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                (wkTmBy 1 (subTm (liftSubst sigma) l))
                (wkTmBy 1 (subTm (liftSubst tau) l))
                T)
            (qtrBranchTyWk (subTy (liftSubst sigma) L)))
          (weakenOneOpenTmEq branchEq wkCtxWF)

      cohσ =
        subst
          (λ J -> HypComputable J)
          (cong
            (λ T ->
              termEq (T ∷ subTy sigma A ∷ [])
                (subTm (liftSubst (liftSubst sigma)) (wkTmBy 1 l))
                (subTm (liftSubst (liftSubst sigma)) (renTm qtrSecondBranchRen l))
                (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
            (wkTyLiftSubst sigma A)
            ∙ cong
                (λ t ->
                  termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                    t
                    (subTm (liftSubst (liftSubst sigma)) (renTm qtrSecondBranchRen l))
                    (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
                (wkTmLiftSubst (liftSubst sigma) l)
            ∙ cong
                (λ u ->
                  termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                    (wkTmBy 1 (subTm (liftSubst sigma) l))
                    u
                    (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
                (qtrSecondBranchTmLiftComp sigma l)
            ∙ cong
                (λ T ->
                  termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                    (wkTmBy 1 (subTm (liftSubst sigma) l))
                    (renTm qtrSecondBranchRen (subTm (liftSubst sigma) l))
                    T)
                (qtrCohTyLiftComp sigma L))
          (openHypTmEq2
            sigmaFits
            dAσ
            dWkAσ
            dcoh)

      cohστ =
        subst
          (λ J -> HypComputable J)
          (cong
            (λ T ->
              termEq (T ∷ subTy sigma A ∷ [])
                (subTm (liftSubst (liftSubst sigma)) (wkTmBy 1 l))
                (subTm (liftSubst (liftSubst tau)) (renTm qtrSecondBranchRen l))
                (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
            (wkTyLiftSubst sigma A)
            ∙ cong
                (λ t ->
                  termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                    t
                    (subTm (liftSubst (liftSubst tau)) (renTm qtrSecondBranchRen l))
                    (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
                (wkTmLiftSubst (liftSubst sigma) l)
            ∙ cong
                (λ u ->
                  termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                    (wkTmBy 1 (subTm (liftSubst sigma) l))
                    u
                    (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
                (qtrSecondBranchTmLiftComp tau l)
            ∙ cong
                (λ T ->
                  termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                    (wkTmBy 1 (subTm (liftSubst sigma) l))
                    (renTm qtrSecondBranchRen (subTm (liftSubst tau) l))
                    T)
                (qtrCohTyLiftComp sigma L))
          (let
             lifted1Eq :
               FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma)
                 (liftSubst sigma)
                 (liftSubst tau)
             lifted1Eq =
               subst
                 (λ rho -> FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma) rho (liftSubst tau))
                 (liftSubstCompKeep sigma)
                 (subst
                   (λ rho ->
                     FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma)
                       (consSubst (var zero) (compSub (keepSubstBy 1) sigma))
                       rho)
                   (liftSubstCompKeep tau)
                   (liftFitsEqOne fitsEq dAσ))
             lifted2Eq :
               FitsEqSubst (subTy (liftSubst sigma) (wkTyBy 1 A) ∷ subTy sigma A ∷ [])
                 (wkTyBy 1 A ∷ A ∷ gamma)
                 (liftSubst (liftSubst sigma))
                 (liftSubst (liftSubst tau))
             lifted2Eq =
               subst
                 (λ rho ->
                   FitsEqSubst (subTy (liftSubst sigma) (wkTyBy 1 A) ∷ subTy sigma A ∷ [])
                     (wkTyBy 1 A ∷ A ∷ gamma)
                     rho
                     (liftSubst (liftSubst tau)))
                 (liftSubstCompKeep (liftSubst sigma))
                 (subst
                   (λ rho ->
                     FitsEqSubst (subTy (liftSubst sigma) (wkTyBy 1 A) ∷ subTy sigma A ∷ [])
                       (wkTyBy 1 A ∷ A ∷ gamma)
                       (consSubst (var zero) (compSub (keepSubstBy 1) (liftSubst sigma)))
                       rho)
                   (liftSubstCompKeep (liftSubst tau))
                   (liftFitsEq lifted1Eq dWkAσ))
           in
           hypTmEqOpen
             nonemptyNeNil
             (eqSubTmEqRule dcoh lifted2Eq)
             (openHypTm2
               sigmaFits
               dAσ
               dWkAσ
               (assocTmLeft dcoh))
             (λ rho fits2 _ ->
               let
                 composedFitsEq = composeFitsEq fits2 lifted2Eq
               in
               subst
                 (λ J -> Computable J)
                 (sym
                   (cong₃ (termEq [])
                     (subTmComp rho (liftSubst (liftSubst sigma)) (wkTmBy 1 l))
                     (subTmComp rho (liftSubst (liftSubst tau)) (renTm qtrSecondBranchRen l))
                     (subTyComp rho (liftSubst (liftSubst sigma)) (qtrCohTy L))))
                 (eqSubDerivTmEqComp
                   dcoh
                   composedFitsEq))
             (λ rho eta fitsEq2 _ ->
               let
                 composedFitsEq = composeEqFitsEq fitsEq2 lifted2Eq
               in
               subst
                 (λ J -> Computable J)
                 (sym
                   (cong₃ (termEq [])
                     (subTmComp rho (liftSubst (liftSubst sigma)) (wkTmBy 1 l))
                     (subTmComp eta (liftSubst (liftSubst tau)) (renTm qtrSecondBranchRen l))
                     (subTyComp rho (liftSubst (liftSubst sigma)) (qtrCohTy L))))
                 (eqSubDerivTmEqComp
                   dcoh
                   composedFitsEq)))

      cohτ = compTransTm (compSymTm branchEqWk) cohστ

      resultPath :
        termEq []
          (subTm sigma (tmElQtr l p))
          (subTm tau (tmElQtr l p))
          (subTy sigma (subTy (singleSubst p) L))
          ≡
        termEq []
          (tmElQtr (subTm (liftSubst sigma) l) (subTm sigma p))
          (tmElQtr (subTm (liftSubst tau) l) (subTm tau p))
          (subTy (singleSubst (subTm sigma p)) (subTy (liftSubst sigma) L))
      resultPath =
        cong₃
          (termEq [])
          refl
          refl
          (subTyComp sigma (singleSubst p) L
            ∙ cong (λ rho -> subTy rho L) (sym (singleSubstCompLift sigma p))
            ∙ sym (subTyComp (singleSubst (subTm sigma p)) (liftSubst sigma) L))
    in
    subst
      (λ J -> Computable J)
      (sym resultPath)
      (compEQtrClosed compTransTmClosed compSymTmClosed compConvTmEqClosed
        compL compp branchEq cohσ cohτ)

  eqSubDerivTmEqCompEQtrEq
    : {gamma : Ctx} {A L : RawType} {l l' p p' : RawTerm} {sigma tau : Subst}
    -> Derivable (isType ((tyQtr A) ∷ gamma) L)
    -> Derivable (termEq gamma p p' (tyQtr A))
    -> Derivable (termEq (A ∷ gamma) l l' (qtrBranchTy L))
    -> Derivable
         (termEq (wkTyBy 1 A ∷ A ∷ gamma)
           (wkTmBy 1 l)
           (renTm qtrSecondBranchRen l)
           (qtrCohTy L))
    -> Derivable
         (termEq (wkTyBy 1 A ∷ A ∷ gamma)
           (wkTmBy 1 l')
           (renTm qtrSecondBranchRen l')
           (qtrCohTy L))
    -> FitsEqSubst [] gamma sigma tau
    -> Computable
         (termEq []
           (subTm sigma (tmElQtr l p))
           (subTm tau (tmElQtr l' p'))
           (subTy sigma (subTy (singleSubst p) L)))
  eqSubDerivTmEqCompEQtrEq
    {gamma = gamma} {A = A} {L = L} {l = l} {l' = l'} {p = p} {p' = p'} {sigma = sigma} {tau = tau}
    dL dp dl dcoh dcoh' fitsEq =
    let
      sigmaFits = fitsEqSubstLeft fitsEq
      compp = eqSubDerivTmEqComp dp fitsEq
      compQtrσ = compTmToCompTy (compTmEqLeft compp)
      dQtrσ = compToDerivable compQtrσ
      tyInv = invertQtrTy compQtrσ evalQtr
      compAσ = ClosedQtrTyInv.qtrTyCompBase tyInv
      dAσ = compToDerivable compAσ
      dWkBaseσ = weakenTy dAσ (wfCons wfNil dAσ)
      dWkAσ =
        subst
          (λ T -> Derivable (isType (subTy sigma A ∷ []) T))
          (sym (wkTyLiftSubst sigma A))
          dWkBaseσ
      wkCtxWF : CtxWF (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
      wkCtxWF = wfCons (wfCons wfNil dAσ) dWkBaseσ
      compL = openHypTy1 sigmaFits dQtrσ dL

      branchEq =
        subst
          (λ T ->
            HypComputable
              (termEq (subTy sigma A ∷ [])
                (subTm (liftSubst sigma) l)
                (subTm (liftSubst tau) l')
                T))
          (qtrBranchTyLiftComp sigma L)
          (let
             liftedEq :
               FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma)
                 (liftSubst sigma)
                 (liftSubst tau)
             liftedEq =
               subst
                 (λ rho -> FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma) rho (liftSubst tau))
                 (liftSubstCompKeep sigma)
                 (subst
                   (λ rho ->
                     FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma)
                       (consSubst (var zero) (compSub (keepSubstBy 1) sigma))
                       rho)
                   (liftSubstCompKeep tau)
                   (liftFitsEqOne fitsEq dAσ))
           in
           hypTmEqOpen
             nonemptyNeNil
             (eqSubTmEqRule dl liftedEq)
             (openHypTm1
               sigmaFits
               dAσ
               (assocTmLeft dl))
             (λ rho fits2 _ ->
               let
                 composedFitsEq = composeFitsEq fits2 liftedEq
               in
               subst
                 (λ J -> Computable J)
                 (sym
                   (cong₃ (termEq [])
                     (subTmComp rho (liftSubst sigma) l)
                     (subTmComp rho (liftSubst tau) l')
                     (subTyComp rho (liftSubst sigma) (qtrBranchTy L))))
                 (eqSubDerivTmEqComp
                   dl
                   composedFitsEq))
             (λ rho eta fitsEq2 _ ->
               let
                 composedFitsEq = composeEqFitsEq fitsEq2 liftedEq
               in
               subst
                 (λ J -> Computable J)
                 (sym
                   (cong₃ (termEq [])
                     (subTmComp rho (liftSubst sigma) l)
                     (subTmComp eta (liftSubst tau) l')
                     (subTyComp rho (liftSubst sigma) (qtrBranchTy L))))
                 (eqSubDerivTmEqComp
                   dl
                   composedFitsEq)))

      branchEqRight =
        subst
          (λ T ->
            HypComputable
              (termEq (subTy sigma A ∷ [])
                (subTm (liftSubst sigma) l')
                (subTm (liftSubst tau) l')
                T))
          (qtrBranchTyLiftComp sigma L)
          (let
             liftedEq :
               FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma)
                 (liftSubst sigma)
                 (liftSubst tau)
             liftedEq =
               subst
                 (λ rho -> FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma) rho (liftSubst tau))
                 (liftSubstCompKeep sigma)
                 (subst
                   (λ rho ->
                     FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma)
                       (consSubst (var zero) (compSub (keepSubstBy 1) sigma))
                       rho)
                   (liftSubstCompKeep tau)
                   (liftFitsEqOne fitsEq dAσ))
           in
           hypTmEqOpen
             nonemptyNeNil
             (eqSubTmRule (assocTmRight dl) liftedEq)
             (openHypTm1
               sigmaFits
               dAσ
               (assocTmRight dl))
             (λ rho fits2 _ ->
               let
                 composedFitsEq = composeFitsEq fits2 liftedEq
               in
               subst
                 (λ J -> Computable J)
                 (sym
                   (cong₃ (termEq [])
                     (subTmComp rho (liftSubst sigma) l')
                     (subTmComp rho (liftSubst tau) l')
                     (subTyComp rho (liftSubst sigma) (qtrBranchTy L))))
                 (eqSubDerivTmComp
                   (assocTmRight dl)
                   composedFitsEq))
             (λ rho eta fitsEq2 _ ->
               let
                 composedFitsEq = composeEqFitsEq fitsEq2 liftedEq
               in
               subst
                 (λ J -> Computable J)
                 (sym
                   (cong₃ (termEq [])
                     (subTmComp rho (liftSubst sigma) l')
                     (subTmComp eta (liftSubst tau) l')
                     (subTyComp rho (liftSubst sigma) (qtrBranchTy L))))
                 (eqSubDerivTmComp
                   (assocTmRight dl)
                   composedFitsEq)))

      branchEqRightWk =
        subst
          (λ J -> HypComputable J)
          (cong
            (λ T ->
              termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                (wkTmBy 1 (subTm (liftSubst sigma) l'))
                (wkTmBy 1 (subTm (liftSubst tau) l'))
                T)
            (qtrBranchTyWk (subTy (liftSubst sigma) L)))
          (weakenOneOpenTmEq branchEqRight wkCtxWF)

      cohσ =
        subst
          (λ J -> HypComputable J)
          (cong
            (λ T ->
              termEq (T ∷ subTy sigma A ∷ [])
                (subTm (liftSubst (liftSubst sigma)) (wkTmBy 1 l))
                (subTm (liftSubst (liftSubst sigma)) (renTm qtrSecondBranchRen l))
                (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
            (wkTyLiftSubst sigma A)
            ∙ cong
                (λ t ->
                  termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                    t
                    (subTm (liftSubst (liftSubst sigma)) (renTm qtrSecondBranchRen l))
                    (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
                (wkTmLiftSubst (liftSubst sigma) l)
            ∙ cong
                (λ u ->
                  termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                    (wkTmBy 1 (subTm (liftSubst sigma) l))
                    u
                    (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
                (qtrSecondBranchTmLiftComp sigma l)
            ∙ cong
                (λ T ->
                  termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                    (wkTmBy 1 (subTm (liftSubst sigma) l))
                    (renTm qtrSecondBranchRen (subTm (liftSubst sigma) l))
                    T)
                (qtrCohTyLiftComp sigma L))
          (openHypTmEq2
            sigmaFits
            dAσ
            dWkAσ
            dcoh)

      coh'στ =
        subst
          (λ J -> HypComputable J)
          (cong
            (λ T ->
              termEq (T ∷ subTy sigma A ∷ [])
                (subTm (liftSubst (liftSubst sigma)) (wkTmBy 1 l'))
                (subTm (liftSubst (liftSubst tau)) (renTm qtrSecondBranchRen l'))
                (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
            (wkTyLiftSubst sigma A)
            ∙ cong
                (λ t ->
                  termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                    t
                    (subTm (liftSubst (liftSubst tau)) (renTm qtrSecondBranchRen l'))
                    (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
                (wkTmLiftSubst (liftSubst sigma) l')
            ∙ cong
                (λ u ->
                  termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                    (wkTmBy 1 (subTm (liftSubst sigma) l'))
                    u
                    (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
                (qtrSecondBranchTmLiftComp tau l')
            ∙ cong
                (λ T ->
                  termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                    (wkTmBy 1 (subTm (liftSubst sigma) l'))
                    (renTm qtrSecondBranchRen (subTm (liftSubst tau) l'))
                    T)
                (qtrCohTyLiftComp sigma L))
          (let
             lifted1Eq :
               FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma)
                 (liftSubst sigma)
                 (liftSubst tau)
             lifted1Eq =
               subst
                 (λ rho -> FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma) rho (liftSubst tau))
                 (liftSubstCompKeep sigma)
                 (subst
                   (λ rho ->
                     FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma)
                       (consSubst (var zero) (compSub (keepSubstBy 1) sigma))
                       rho)
                   (liftSubstCompKeep tau)
                   (liftFitsEqOne fitsEq dAσ))
             lifted2Eq :
               FitsEqSubst (subTy (liftSubst sigma) (wkTyBy 1 A) ∷ subTy sigma A ∷ [])
                 (wkTyBy 1 A ∷ A ∷ gamma)
                 (liftSubst (liftSubst sigma))
                 (liftSubst (liftSubst tau))
             lifted2Eq =
               subst
                 (λ rho ->
                   FitsEqSubst (subTy (liftSubst sigma) (wkTyBy 1 A) ∷ subTy sigma A ∷ [])
                     (wkTyBy 1 A ∷ A ∷ gamma)
                     rho
                     (liftSubst (liftSubst tau)))
                 (liftSubstCompKeep (liftSubst sigma))
                 (subst
                   (λ rho ->
                     FitsEqSubst (subTy (liftSubst sigma) (wkTyBy 1 A) ∷ subTy sigma A ∷ [])
                       (wkTyBy 1 A ∷ A ∷ gamma)
                       (consSubst (var zero) (compSub (keepSubstBy 1) (liftSubst sigma)))
                       rho)
                   (liftSubstCompKeep (liftSubst tau))
                   (liftFitsEq lifted1Eq dWkAσ))
           in
           hypTmEqOpen
             nonemptyNeNil
             (eqSubTmEqRule dcoh' lifted2Eq)
             (openHypTm2
               sigmaFits
               dAσ
               dWkAσ
               (assocTmLeft dcoh'))
             (λ rho fits2 _ ->
               let
                 composedFitsEq = composeFitsEq fits2 lifted2Eq
               in
               subst
                 (λ J -> Computable J)
                 (sym
                   (cong₃ (termEq [])
                     (subTmComp rho (liftSubst (liftSubst sigma)) (wkTmBy 1 l'))
                     (subTmComp rho (liftSubst (liftSubst tau)) (renTm qtrSecondBranchRen l'))
                     (subTyComp rho (liftSubst (liftSubst sigma)) (qtrCohTy L))))
                 (eqSubDerivTmEqComp
                   dcoh'
                   composedFitsEq))
             (λ rho eta fitsEq2 _ ->
               let
                 composedFitsEq = composeEqFitsEq fitsEq2 lifted2Eq
               in
               subst
                 (λ J -> Computable J)
                 (sym
                   (cong₃ (termEq [])
                     (subTmComp rho (liftSubst (liftSubst sigma)) (wkTmBy 1 l'))
                     (subTmComp eta (liftSubst (liftSubst tau)) (renTm qtrSecondBranchRen l'))
                     (subTyComp rho (liftSubst (liftSubst sigma)) (qtrCohTy L))))
                 (eqSubDerivTmEqComp
                   dcoh'
                   composedFitsEq)))

      cohτ = compTransTm (compSymTm branchEqRightWk) coh'στ

      resultPath :
        termEq []
          (subTm sigma (tmElQtr l p))
          (subTm tau (tmElQtr l' p'))
          (subTy sigma (subTy (singleSubst p) L))
          ≡
        termEq []
          (tmElQtr (subTm (liftSubst sigma) l) (subTm sigma p))
          (tmElQtr (subTm (liftSubst tau) l') (subTm tau p'))
          (subTy (singleSubst (subTm sigma p)) (subTy (liftSubst sigma) L))
      resultPath =
        cong₃
          (termEq [])
          refl
          refl
          (subTyComp sigma (singleSubst p) L
            ∙ cong (λ rho -> subTy rho L) (sym (singleSubstCompLift sigma p))
            ∙ sym (subTyComp (singleSubst (subTm sigma p)) (liftSubst sigma) L))
    in
    subst
      (λ J -> Computable J)
      (sym resultPath)
      (compEQtrClosed compTransTmClosed compSymTmClosed compConvTmEqClosed
        compL compp branchEq cohσ cohτ)

  eqSubDerivTmEqCompCQtr
    : {gamma : Ctx} {A L : RawType} {a l : RawTerm} {sigma tau : Subst}
    -> Derivable (isType ((tyQtr A) ∷ gamma) L)
    -> Derivable (hasTy gamma a A)
    -> Derivable (hasTy (A ∷ gamma) l (qtrBranchTy L))
    -> Derivable
         (termEq (wkTyBy 1 A ∷ A ∷ gamma)
           (wkTmBy 1 l)
           (renTm qtrSecondBranchRen l)
           (qtrCohTy L))
    -> FitsEqSubst [] gamma sigma tau
    -> Computable
         (termEq []
           (subTm sigma (tmElQtr l (tmClass a)))
           (subTm tau (subTm (qtrCompSub a) l))
           (subTy sigma (subTy (singleSubst (tmClass a)) L)))
  eqSubDerivTmEqCompCQtr
    {gamma = gamma} {A = A} {L = L} {a = a} {l = l} {sigma = sigma} {tau = tau}
    dL da dl dcoh fitsEq =
    let
      sigmaFits = fitsEqSubstLeft fitsEq
      compa = eqSubDerivTmComp da fitsEq
      compaσ = compTmEqLeft compa
      compAσ = compTmToCompTy compaσ
      dAσ = compToDerivable compAσ
      dQtrσ = compToDerivable (compFQtrClosed compAσ)
      dWkBaseσ = weakenTy dAσ (wfCons wfNil dAσ)
      dWkAσ =
        subst
          (λ T -> Derivable (isType (subTy sigma A ∷ []) T))
          (sym (wkTyLiftSubst sigma A))
          dWkBaseσ
      compL = openHypTy1 sigmaFits dQtrσ dL

      complσ =
        subst
          (λ T ->
            HypComputable
              (hasTy (subTy sigma A ∷ [])
                (subTm (liftSubst sigma) l)
                T))
          (qtrBranchTyLiftComp sigma L)
          (openHypTm1
            sigmaFits
            dAσ
            dl)

      compcohσ =
        subst
          (λ J -> HypComputable J)
          (cong
            (λ T ->
              termEq (T ∷ subTy sigma A ∷ [])
                (subTm (liftSubst (liftSubst sigma)) (wkTmBy 1 l))
                (subTm (liftSubst (liftSubst sigma)) (renTm qtrSecondBranchRen l))
                (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
            (wkTyLiftSubst sigma A)
            ∙ cong
                (λ t ->
                  termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                    t
                    (subTm (liftSubst (liftSubst sigma)) (renTm qtrSecondBranchRen l))
                    (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
                (wkTmLiftSubst (liftSubst sigma) l)
            ∙ cong
                (λ u ->
                  termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                    (wkTmBy 1 (subTm (liftSubst sigma) l))
                    u
                    (subTy (liftSubst (liftSubst sigma)) (qtrCohTy L)))
                (qtrSecondBranchTmLiftComp sigma l)
            ∙ cong
                (λ T ->
                  termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                    (wkTmBy 1 (subTm (liftSubst sigma) l))
                    (renTm qtrSecondBranchRen (subTm (liftSubst sigma) l))
                    T)
                (qtrCohTyLiftComp sigma L))
          (openHypTmEq2
            sigmaFits
            dAσ
            dWkAσ
            dcoh)

      leftCan = compCQtrClosed compL compaσ complσ compcohσ

      complEq =
        subst
          (λ T ->
            HypComputable
              (termEq (subTy sigma A ∷ [])
                (subTm (liftSubst sigma) l)
                (subTm (liftSubst tau) l)
                T))
          (qtrBranchTyLiftComp sigma L)
          (let
             liftedEq :
               FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma)
                 (liftSubst sigma)
                 (liftSubst tau)
             liftedEq =
               subst
                 (λ rho -> FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma) rho (liftSubst tau))
                 (liftSubstCompKeep sigma)
                 (subst
                   (λ rho ->
                     FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma)
                       (consSubst (var zero) (compSub (keepSubstBy 1) sigma))
                       rho)
                   (liftSubstCompKeep tau)
                   (liftFitsEqOne fitsEq dAσ))
           in
           hypTmEqOpen
             nonemptyNeNil
             (eqSubTmRule dl liftedEq)
          (openHypTm1
               sigmaFits
               dAσ
               dl)
             (λ rho fits2 _ ->
               let
                 composedFitsEq = composeFitsEq fits2 liftedEq
               in
               subst
                 (λ J -> Computable J)
                 (sym
                   (cong₃ (termEq [])
                     (subTmComp rho (liftSubst sigma) l)
                     (subTmComp rho (liftSubst tau) l)
                     (subTyComp rho (liftSubst sigma) (qtrBranchTy L))))
                 (eqSubDerivTmComp
                   dl
                   composedFitsEq))
             (λ rho eta fitsEq2 _ ->
               let
                 composedFitsEq = composeEqFitsEq fitsEq2 liftedEq
               in
               subst
                 (λ J -> Computable J)
                 (sym
                   (cong₃ (termEq [])
                     (subTmComp rho (liftSubst sigma) l)
                     (subTmComp eta (liftSubst tau) l)
                     (subTyComp rho (liftSubst sigma) (qtrBranchTy L))))
                 (eqSubDerivTmComp
                   dl
                   composedFitsEq)))

      branchFitsEqData =
        qtrCompComputableFitsEqHelper compa

      branchFitsEq :
        FitsEqSubst [] (subTy sigma A ∷ [])
          (qtrCompSub (subTm sigma a))
          (qtrCompSub (subTm tau a))
      branchFitsEq = fst branchFitsEqData

      branchCompFitsEq :
        ComputableFitsEq branchFitsEq
      branchCompFitsEq = snd branchFitsEqData

      compBodyEq = branchSubEq branchFitsEq branchCompFitsEq complEq

      resultPath :
        termEq []
          (subTm sigma (tmElQtr l (tmClass a)))
          (subTm tau (subTm (qtrCompSub a) l))
          (subTy sigma (subTy (singleSubst (tmClass a)) L))
          ≡
        termEq []
          (tmElQtr (subTm (liftSubst sigma) l) (tmClass (subTm sigma a)))
          (subTm (qtrCompSub (subTm tau a)) (subTm (liftSubst tau) l))
          (subTy (singleSubst (tmClass (subTm sigma a))) (subTy (liftSubst sigma) L))
      resultPath =
        cong₃
          (termEq [])
          refl
          (subTmComp tau (qtrCompSub a) l
            ∙ cong (λ rho -> subTm rho l) (qtrCompSubLiftComp tau a)
            ∙ sym (subTmComp (qtrCompSub (subTm tau a)) (liftSubst tau) l))
          (subTyComp sigma (singleSubst (tmClass a)) L
            ∙ cong (λ rho -> subTy rho L) (sym (singleSubstCompLift sigma (tmClass a)))
            ∙ sym (subTyComp (singleSubst (tmClass (subTm sigma a))) (liftSubst sigma) L))
    in
    subst
      (λ J -> Computable J)
      (sym resultPath)
      (compTransTmClosed leftCan compBodyEq)
    where
    branchSubEq :
      (branchFitsEq :
        FitsEqSubst [] (subTy sigma A ∷ [])
          (qtrCompSub (subTm sigma a))
          (qtrCompSub (subTm tau a)))
      -> ComputableFitsEq branchFitsEq
      -> HypComputable
           (termEq (subTy sigma A ∷ [])
             (subTm (liftSubst sigma) l)
             (subTm (liftSubst tau) l)
             (qtrBranchTy (subTy (liftSubst sigma) L)))
      -> Computable
           (termEq []
             (subTm (qtrCompSub (subTm sigma a)) (subTm (liftSubst sigma) l))
             (subTm (qtrCompSub (subTm tau a)) (subTm (liftSubst tau) l))
             (subTy (singleSubst (tmClass (subTm sigma a))) (subTy (liftSubst sigma) L)))
    branchSubEq branchFitsEq branchCompFitsEq (hypTmEqOpen _ _ _ _ subEqdl) =
      subst
        (λ J -> Computable J)
        (cong
          (termEq []
            (subTm (qtrCompSub (subTm sigma a)) (subTm (liftSubst sigma) l))
            (subTm (qtrCompSub (subTm tau a)) (subTm (liftSubst tau) l)))
          (qtrBranchTyComp (subTm sigma a) (subTy (liftSubst sigma) L)))
        (subEqdl
          (qtrCompSub (subTm sigma a))
          (qtrCompSub (subTm tau a))
          branchFitsEq
          branchCompFitsEq)

  eqSubDerivTmComp (varStar {delta = delta} {A = A} wf dA) fitsEq =
    computableTmEqClosed (lookupVarFitsEq {delta = delta} {A = A} fitsEq)
  eqSubDerivTmComp (iTop wf) fitsEq =
    compReflTm compITopClosed
  eqSubDerivTmComp {sigma = sigma} {tau = tau}
    (iSigma {a = a} {b = b} {A = A} {B = B} da db dSigma) fitsEq =
    let
      sigmaFits = fitsEqSubstLeft fitsEq
      compac = eqSubDerivTmComp da fitsEq
      compSigma = substDerivTyComp dSigma sigmaFits
      tyInv = invertSigmaTy compSigma evalSigma
      compAσ = ClosedSigmaTyInv.sigmaTyCompHead tyInv
      compBσ = hypComputableTy (ClosedSigmaTyInv.sigmaTyFamDeriv tyInv)
      compbdRaw = eqSubDerivTmComp db fitsEq
      compbd =
        subst
          (λ T -> Computable (termEq [] (subTm sigma b) (subTm tau b) T))
          (subTyComp sigma (singleSubst a) B
            ∙ cong (λ rho -> subTy rho B) (sym (singleSubstCompLift sigma a))
            ∙ sym (subTyComp (singleSubst (subTm sigma a)) (liftSubst sigma) B))
          compbdRaw
      compa = compTmEqLeft compac
      compcA = compTmEqRightClosed compac
      compb = compTmEqLeft compbd
      compdA = compTmEqRightClosed compbd
      compd =
        compConvTmClosed compdA (compSingleEqSubstTyClosed compBσ compac)
      compPairLeft = compISigmaClosed compa compb compSigma
      compPairRight = compISigmaClosed compcA compd compSigma
    in
    compTmEqClosedSigma
      (iSigmaEq (compToDerivable compac) (compToDerivable compbd)
        (compToDerivable compAσ) (hypCompToDerivable compBσ))
      compPairLeft
      compPairRight
      evalSigma
      evalPair
      evalPair
      compac
      compbd
  eqSubDerivTmComp (iEq da) fitsEq =
    compReflTm (compIEqClosed (compTmEqLeft (eqSubDerivTmComp da fitsEq)))
  eqSubDerivTmComp (iQtr da) fitsEq =
    let
      compab = eqSubDerivTmComp da fitsEq
    in
    compIQtrEqClosed (compTmEqLeft compab) (compTmEqRightClosed compab)
  eqSubDerivTmComp {gamma = gamma} {sigma = sigma} {tau = tau}
    (eSigma {A = A} {B = B} {M = M} {d = d} {m = m} dM dd dm) fitsEq =
    let
      sigmaFits = fitsEqSubstLeft fitsEq
      compdd = eqSubDerivTmComp dd fitsEq
      compSigma = compTmToCompTy (compTmEqLeft compdd)
      dSigmaσ = compToDerivable compSigma
      compM = openHypTy1 sigmaFits dSigmaσ dM

      tyInv = invertSigmaTy compSigma evalSigma
      compAσ = ClosedSigmaTyInv.sigmaTyCompHead tyInv
      dAσ = compToDerivable compAσ
      compBσ = hypComputableTy (ClosedSigmaTyInv.sigmaTyFamDeriv tyInv)
      dBσ = hypCompToDerivable compBσ

      compdm =
        let
          lifted1Eq :
            FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma)
              (liftSubst sigma)
              (liftSubst tau)
          lifted1Eq =
            subst
              (λ rho -> FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma) rho (liftSubst tau))
              (liftSubstCompKeep sigma)
              (subst
                (λ rho ->
                  FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma)
                    (consSubst (var zero) (compSub (keepSubstBy 1) sigma))
                    rho)
                (liftSubstCompKeep tau)
                (liftFitsEqOne fitsEq dAσ))
          lifted2Eq :
            FitsEqSubst (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) (B ∷ A ∷ gamma)
              (liftSubst (liftSubst sigma))
              (liftSubst (liftSubst tau))
          lifted2Eq =
            subst
              (λ rho ->
                FitsEqSubst (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) (B ∷ A ∷ gamma)
                  rho
                  (liftSubst (liftSubst tau)))
              (liftSubstCompKeep (liftSubst sigma))
              (subst
                (λ rho ->
                  FitsEqSubst (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) (B ∷ A ∷ gamma)
                    (consSubst (var zero) (compSub (keepSubstBy 1) (liftSubst sigma)))
                    rho)
                (liftSubstCompKeep (liftSubst tau))
                (liftFitsEq lifted1Eq dBσ))
        in
        subst
          (λ J -> HypComputable J)
          (cong
            (termEq (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ [])
              (subTm (liftSubst (liftSubst sigma)) m)
              (subTm (liftSubst (liftSubst tau)) m))
            (sigmaBranchTyLiftComp sigma M))
          (hypTmEqOpen
            nonemptyNeNil
            (eqSubTmRule dm lifted2Eq)
            (openHypTm2
              sigmaFits
              dAσ
              dBσ
              dm)
            (λ rho fits2 _ ->
              let
                composedFitsEq = composeFitsEq fits2 lifted2Eq
              in
              subst
                (λ J -> Computable J)
                (sym
                  (cong₃ (termEq [])
                    (subTmComp rho (liftSubst (liftSubst sigma)) m)
                    (subTmComp rho (liftSubst (liftSubst tau)) m)
                    (subTyComp rho (liftSubst (liftSubst sigma))
                      (sigmaBranchTy M))))
                (eqSubDerivTmComp
                  dm
                  composedFitsEq))
            (λ rho eta fitsEq2 _ ->
              let
                composedFitsEq = composeEqFitsEq fitsEq2 lifted2Eq
              in
              subst
                (λ J -> Computable J)
                (sym
                  (cong₃ (termEq [])
                    (subTmComp rho (liftSubst (liftSubst sigma)) m)
                    (subTmComp eta (liftSubst (liftSubst tau)) m)
                    (subTyComp rho (liftSubst (liftSubst sigma))
                      (sigmaBranchTy M))))
                (eqSubDerivTmComp
                  dm
                  composedFitsEq)))

      resultPath :
        termEq []
          (subTm sigma (tmElSigma d m))
          (subTm tau (tmElSigma d m))
          (subTy sigma (subTy (singleSubst d) M))
          ≡
        termEq []
          (tmElSigma (subTm sigma d) (subTm (liftSubst (liftSubst sigma)) m))
          (tmElSigma (subTm tau d) (subTm (liftSubst (liftSubst tau)) m))
          (subTy (singleSubst (subTm sigma d)) (subTy (liftSubst sigma) M))
      resultPath =
        cong₃
          (termEq [])
          refl
          refl
          (subTyComp sigma (singleSubst d) M
            ∙ cong (λ rho -> subTy rho M) (sym (singleSubstCompLift sigma d))
            ∙ sym (subTyComp (singleSubst (subTm sigma d)) (liftSubst sigma) M))
    in
    subst
      (λ J -> Computable J)
      (sym resultPath)
      (compESigmaClosed compTransTmClosed compConvTmEqClosed compM compdd compdm)
  eqSubDerivTmComp (eQtr dL dp dl dcoh) fitsEq =
    eqSubDerivTmCompEQtr dL dp dl dcoh fitsEq
  eqSubDerivTmComp (conv d dAB) fitsEq =
    let
      sigmaFits = fitsEqSubstLeft fitsEq
    in
    compConvTmEqClosed (eqSubDerivTmComp d fitsEq) (substDerivTyEqComp dAB sigmaFits)
  eqSubDerivTmComp {sigma = sigma} {tau = tau}
    (weakenTm {delta = delta} {t = t} {A = A} d wf) fitsEq =
    subst
      (λ J -> Computable J)
      (cong₃ (termEq [])
        (sym (subTmWkBy sigma (length delta) t))
        (sym (subTmWkBy tau (length delta) t))
        (sym (subTyWkBy sigma (length delta) A)))
      (eqSubDerivTmComp d (dropFitsEq delta fitsEq))
  eqSubDerivTmComp {sigma = sigma} {tau = tau}
    (substTmRule {sigma = sigma'} {t = t} {A = A} d fits') fitsEq =
    let
      composedFitsEq = composeEqFits fitsEq fits'
    in
    subst
      (λ J -> Computable J)
      (cong₃ (termEq [])
        (sym (subTmComp sigma sigma' t))
        (sym (subTmComp tau sigma' t))
        (sym (subTyComp sigma sigma' A)))
      (eqSubDerivTmComp d composedFitsEq)
  eqSubDerivTmEqComp (reflTm d) fitsEq =
    eqSubDerivTmComp d fitsEq
  eqSubDerivTmEqComp (symTm d) fitsEq =
    let
      sigmaFits = fitsEqSubstLeft fitsEq
    in
    compTransTmClosed
      (compSymTmClosed (substDerivTmEqComp d sigmaFits))
      (eqSubDerivTmComp (assocTmLeft d) fitsEq)
  eqSubDerivTmEqComp (transTm d₁ d₂) fitsEq =
    let
      sigmaFits = fitsEqSubstLeft fitsEq
    in
    compTransTmClosed
      (substDerivTmEqComp d₁ sigmaFits)
      (eqSubDerivTmEqComp d₂ fitsEq)
  eqSubDerivTmEqComp (convEq d dAB) fitsEq =
    let
      sigmaFits = fitsEqSubstLeft fitsEq
    in
    compConvTmEqClosed (eqSubDerivTmEqComp d fitsEq) (substDerivTyEqComp dAB sigmaFits)
  eqSubDerivTmEqComp (cTop d) fitsEq =
    compCTopClosed (compTmEqLeft (eqSubDerivTmComp d fitsEq))
  eqSubDerivTmEqComp {sigma = sigma} {tau = tau}
    (iSigmaEq {a = a} {b = b} {d = d} {A = A} {B = B} dac dbd dA dB) fitsEq =
    let
      sigmaFits = fitsEqSubstLeft fitsEq
      compac = eqSubDerivTmEqComp dac fitsEq
      compA = substDerivTyComp dA sigmaFits
      dAσ = compToDerivable compA
      compB = openHypTy1 sigmaFits dAσ dB
      compbdRaw = eqSubDerivTmEqComp dbd fitsEq
      compbd =
        subst
          (λ T -> Computable (termEq [] (subTm sigma b) (subTm tau d) T))
          (subTyComp sigma (singleSubst a) B
            ∙ cong (λ rho -> subTy rho B) (sym (singleSubstCompLift sigma a))
            ∙ sym (subTyComp (singleSubst (subTm sigma a)) (liftSubst sigma) B))
          compbdRaw
      compa = compTmEqLeft compac
      compcA = compTmEqRightClosed compac
      compb = compTmEqLeft compbd
      compdA = compTmEqRightClosed compbd
      compd =
        compConvTmClosed compdA (compSingleEqSubstTyClosed compB compac)
      compPairLeft = compISigmaClosed compa compb (compFSigmaClosed compA compB)
      compPairRight = compISigmaClosed compcA compd (compFSigmaClosed compA compB)
    in
    compTmEqClosedSigma
      (iSigmaEq (compToDerivable compac) (compToDerivable compbd) dAσ (hypCompToDerivable compB))
      compPairLeft
      compPairRight
      evalSigma
      evalPair
      evalPair
      compac
      compbd
  eqSubDerivTmEqComp {gamma = gamma} {sigma = sigma} {tau = tau}
    (eSigmaEq {A = A} {B = B} {M = M} {d = d} {d' = d'} {m = m} {m' = m'} dM dd dm) fitsEq =
    let
      sigmaFits = fitsEqSubstLeft fitsEq
      compdd = eqSubDerivTmEqComp dd fitsEq
      compSigma = compTmToCompTy (compTmEqLeft compdd)
      dSigmaσ = compToDerivable compSigma
      compM = openHypTy1 sigmaFits dSigmaσ dM

      tyInv = invertSigmaTy compSigma evalSigma
      compAσ = ClosedSigmaTyInv.sigmaTyCompHead tyInv
      dAσ = compToDerivable compAσ
      compBσ = hypComputableTy (ClosedSigmaTyInv.sigmaTyFamDeriv tyInv)
      dBσ = hypCompToDerivable compBσ

      compdm =
        let
          lifted1Eq :
            FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma)
              (liftSubst sigma)
              (liftSubst tau)
          lifted1Eq =
            subst
              (λ rho -> FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma) rho (liftSubst tau))
              (liftSubstCompKeep sigma)
              (subst
                (λ rho ->
                  FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma)
                    (consSubst (var zero) (compSub (keepSubstBy 1) sigma))
                    rho)
                (liftSubstCompKeep tau)
                (liftFitsEqOne fitsEq dAσ))
          lifted2Eq :
            FitsEqSubst (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) (B ∷ A ∷ gamma)
              (liftSubst (liftSubst sigma))
              (liftSubst (liftSubst tau))
          lifted2Eq =
            subst
              (λ rho ->
                FitsEqSubst (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) (B ∷ A ∷ gamma)
                  rho
                  (liftSubst (liftSubst tau)))
              (liftSubstCompKeep (liftSubst sigma))
              (subst
                (λ rho ->
                  FitsEqSubst (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) (B ∷ A ∷ gamma)
                    (consSubst (var zero) (compSub (keepSubstBy 1) (liftSubst sigma)))
                    rho)
                (liftSubstCompKeep (liftSubst tau))
                (liftFitsEq lifted1Eq dBσ))
        in
        subst
          (λ J -> HypComputable J)
          (cong
            (termEq (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ [])
              (subTm (liftSubst (liftSubst sigma)) m)
              (subTm (liftSubst (liftSubst tau)) m'))
            (sigmaBranchTyLiftComp sigma M))
          (hypTmEqOpen
            nonemptyNeNil
            (eqSubTmEqRule dm lifted2Eq)
            (openHypTm2
              sigmaFits
              dAσ
              dBσ
              (assocTmLeft dm))
            (λ rho fits2 _ ->
              let
                composedFitsEq = composeFitsEq fits2 lifted2Eq
              in
              subst
                (λ J -> Computable J)
                (sym
                  (cong₃ (termEq [])
                    (subTmComp rho (liftSubst (liftSubst sigma)) m)
                    (subTmComp rho (liftSubst (liftSubst tau)) m')
                    (subTyComp rho (liftSubst (liftSubst sigma))
                      (sigmaBranchTy M))))
                (eqSubDerivTmEqComp
                  dm
                  composedFitsEq))
            (λ rho eta fitsEq2 _ ->
              let
                composedFitsEq = composeEqFitsEq fitsEq2 lifted2Eq
              in
              subst
                (λ J -> Computable J)
                (sym
                  (cong₃ (termEq [])
                    (subTmComp rho (liftSubst (liftSubst sigma)) m)
                    (subTmComp eta (liftSubst (liftSubst tau)) m')
                    (subTyComp rho (liftSubst (liftSubst sigma))
                      (sigmaBranchTy M))))
                (eqSubDerivTmEqComp
                  dm
                  composedFitsEq)))

      resultPath :
        termEq []
          (subTm sigma (tmElSigma d m))
          (subTm tau (tmElSigma d' m'))
          (subTy sigma (subTy (singleSubst d) M))
          ≡
        termEq []
          (tmElSigma (subTm sigma d) (subTm (liftSubst (liftSubst sigma)) m))
          (tmElSigma (subTm tau d') (subTm (liftSubst (liftSubst tau)) m'))
          (subTy (singleSubst (subTm sigma d)) (subTy (liftSubst sigma) M))
      resultPath =
        cong₃
          (termEq [])
          refl
          refl
          (subTyComp sigma (singleSubst d) M
            ∙ cong (λ rho -> subTy rho M) (sym (singleSubstCompLift sigma d))
            ∙ sym (subTyComp (singleSubst (subTm sigma d)) (liftSubst sigma) M))
    in
    subst
      (λ J -> Computable J)
      (sym resultPath)
      (compESigmaClosed compTransTmClosed compConvTmEqClosed compM compdd compdm)
  eqSubDerivTmEqComp {gamma = gamma} {sigma = sigma} {tau = tau}
    (cSigma {A = A} {B = B} {M = M} {b = b} {c = c} {m = m} dM db dc dm) fitsEq =
    let
      sigmaFits = fitsEqSubstLeft fitsEq
      compb = eqSubDerivTmComp db fitsEq
      compSigma = substDerivTyComp (ctxSuffixTy {delta = []} {gamma = gamma} {A = tySigma A B} (derivToCtxWF dM)) sigmaFits
      dSigmaσ = compToDerivable compSigma
      tyInv = invertSigmaTy compSigma evalSigma
      compAσ = ClosedSigmaTyInv.sigmaTyCompHead tyInv
      dAσ = compToDerivable compAσ
      compBσ = hypComputableTy (ClosedSigmaTyInv.sigmaTyFamDeriv tyInv)
      dBσ = hypCompToDerivable compBσ
      compM = openHypTy1 sigmaFits dSigmaσ dM

      compcRaw = eqSubDerivTmComp dc fitsEq
      compc =
        subst
          (λ T -> Computable (termEq [] (subTm sigma c) (subTm tau c) T))
          (subTyComp sigma (singleSubst b) B
            ∙ cong (λ rho -> subTy rho B) (sym (singleSubstCompLift sigma b))
            ∙ sym (subTyComp (singleSubst (subTm sigma b)) (liftSubst sigma) B))
          compcRaw

      branchFitsEqData =
        sigmaCompComputableFitsEqHelper compb compc

      branchFitsEq : FitsEqSubst [] (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ [])
        (sigmaCompSub (subTm sigma b) (subTm sigma c))
        (sigmaCompSub (subTm tau b) (subTm tau c))
      branchFitsEq = fst branchFitsEqData

      branchCompFitsEq :
        ComputableFitsEq branchFitsEq
      branchCompFitsEq = snd branchFitsEqData

      compdmOpen =
        let
          lifted1Eq :
            FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma)
              (liftSubst sigma)
              (liftSubst tau)
          lifted1Eq =
            subst
              (λ rho -> FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma) rho (liftSubst tau))
              (liftSubstCompKeep sigma)
              (subst
                (λ rho ->
                  FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma)
                    (consSubst (var zero) (compSub (keepSubstBy 1) sigma))
                    rho)
                (liftSubstCompKeep tau)
                (liftFitsEqOne fitsEq dAσ))
          lifted2Eq :
            FitsEqSubst (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) (B ∷ A ∷ gamma)
              (liftSubst (liftSubst sigma))
              (liftSubst (liftSubst tau))
          lifted2Eq =
            subst
              (λ rho ->
                FitsEqSubst (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) (B ∷ A ∷ gamma)
                  rho
                  (liftSubst (liftSubst tau)))
              (liftSubstCompKeep (liftSubst sigma))
              (subst
                (λ rho ->
                  FitsEqSubst (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) (B ∷ A ∷ gamma)
                    (consSubst (var zero) (compSub (keepSubstBy 1) (liftSubst sigma)))
                    rho)
                (liftSubstCompKeep (liftSubst tau))
                (liftFitsEq lifted1Eq dBσ))
        in
        hypTmEqOpen
          nonemptyNeNil
          (eqSubTmRule dm lifted2Eq)
          (openHypTm2
            sigmaFits
            dAσ
            dBσ
            dm)
          (λ rho fits2 _ ->
            let
              composedFitsEq = composeFitsEq fits2 lifted2Eq
            in
            subst
              (λ J -> Computable J)
              (sym
                (cong₃ (termEq [])
                  (subTmComp rho (liftSubst (liftSubst sigma)) m)
                  (subTmComp rho (liftSubst (liftSubst tau)) m)
                  (subTyComp rho (liftSubst (liftSubst sigma))
                    (sigmaBranchTy M))))
              (eqSubDerivTmComp
                dm
                composedFitsEq))
          (λ rho eta fitsEq2 _ ->
            let
              composedFitsEq = composeEqFitsEq fitsEq2 lifted2Eq
            in
            subst
              (λ J -> Computable J)
              (sym
                (cong₃ (termEq [])
                  (subTmComp rho (liftSubst (liftSubst sigma)) m)
                  (subTmComp eta (liftSubst (liftSubst tau)) m)
                  (subTyComp rho (liftSubst (liftSubst sigma))
                    (sigmaBranchTy M))))
              (eqSubDerivTmComp
                dm
                composedFitsEq))

      compdmEq =
        branchSubEq branchFitsEq branchCompFitsEq compdmOpen

      leftCanPath :
        termEq []
          (subTm sigma (tmElSigma (tmPair b c) m))
          (subTm sigma (subTm (sigmaCompSub b c) m))
          (subTy sigma (subTy (singleSubst (tmPair b c)) M))
          ≡
        termEq []
          (tmElSigma (tmPair (subTm sigma b) (subTm sigma c))
            (subTm (liftSubst (liftSubst sigma)) m))
          (subTm (sigmaCompSub (subTm sigma b) (subTm sigma c))
            (subTm (liftSubst (liftSubst sigma)) m))
          (subTy (singleSubst (tmPair (subTm sigma b) (subTm sigma c)))
            (subTy (liftSubst sigma) M))
      leftCanPath =
        cong₃
          (termEq [])
          refl
          (subTmComp sigma (sigmaCompSub b c) m
            ∙ cong (λ rho -> subTm rho m) (sigmaCompSubLiftComp sigma b c)
            ∙ sym (subTmComp (sigmaCompSub (subTm sigma b) (subTm sigma c))
                (liftSubst (liftSubst sigma)) m))
          (subTyComp sigma (singleSubst (tmPair b c)) M
            ∙ cong (λ rho -> subTy rho M) (sym (singleSubstCompLift sigma (tmPair b c)))
            ∙ sym (subTyComp (singleSubst (tmPair (subTm sigma b) (subTm sigma c)))
                (liftSubst sigma) M))

      leftCan =
        subst
          (λ J -> Computable J)
          leftCanPath
          (substDerivTmEqComp (cSigma dM db dc dm) sigmaFits)

      resultPath :
        termEq []
          (subTm sigma (tmElSigma (tmPair b c) m))
          (subTm tau (subTm (sigmaCompSub b c) m))
          (subTy sigma (subTy (singleSubst (tmPair b c)) M))
          ≡
        termEq []
          (tmElSigma (tmPair (subTm sigma b) (subTm sigma c))
            (subTm (liftSubst (liftSubst sigma)) m))
          (subTm (sigmaCompSub (subTm tau b) (subTm tau c))
            (subTm (liftSubst (liftSubst tau)) m))
          (subTy (singleSubst (tmPair (subTm sigma b) (subTm sigma c)))
            (subTy (liftSubst sigma) M))
      resultPath =
        cong₃
          (termEq [])
          refl
          (subTmComp tau (sigmaCompSub b c) m
            ∙ cong (λ rho -> subTm rho m) (sigmaCompSubLiftComp tau b c)
            ∙ sym (subTmComp (sigmaCompSub (subTm tau b) (subTm tau c))
                (liftSubst (liftSubst tau)) m))
          (subTyComp sigma (singleSubst (tmPair b c)) M
            ∙ cong (λ rho -> subTy rho M) (sym (singleSubstCompLift sigma (tmPair b c)))
            ∙ sym (subTyComp (singleSubst (tmPair (subTm sigma b) (subTm sigma c)))
                (liftSubst sigma) M))
    in
    subst
      (λ J -> Computable J)
      (sym resultPath)
      (compTransTmClosed leftCan compdmEq)
    where
    branchSubEq :
      (branchFitsEq :
        FitsEqSubst [] (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ [])
          (sigmaCompSub (subTm sigma b) (subTm sigma c))
          (sigmaCompSub (subTm tau b) (subTm tau c)))
      -> ComputableFitsEq branchFitsEq
      -> HypComputable
           (termEq (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ [])
             (subTm (liftSubst (liftSubst sigma)) m)
             (subTm (liftSubst (liftSubst tau)) m)
             (subTy (liftSubst (liftSubst sigma)) (sigmaBranchTy M)))
      -> Computable
           (termEq []
             (subTm (sigmaCompSub (subTm sigma b) (subTm sigma c))
               (subTm (liftSubst (liftSubst sigma)) m))
             (subTm (sigmaCompSub (subTm tau b) (subTm tau c))
               (subTm (liftSubst (liftSubst tau)) m))
             (subTy (singleSubst (tmPair (subTm sigma b) (subTm sigma c)))
               (subTy (liftSubst sigma) M)))
    branchSubEq branchFitsEq branchCompFitsEq (hypTmEqOpen _ _ _ _ subEqdm) =
      subst
        (λ J -> Computable J)
        (cong
          (termEq []
            (subTm (sigmaCompSub (subTm sigma b) (subTm sigma c))
              (subTm (liftSubst (liftSubst sigma)) m))
            (subTm (sigmaCompSub (subTm tau b) (subTm tau c))
              (subTm (liftSubst (liftSubst tau)) m)))
          (cong
            (λ T -> subTy (sigmaCompSub (subTm sigma b) (subTm sigma c)) T)
            (sigmaBranchTyLiftComp sigma M)
            ∙ sigmaBranchTyComp (subTm sigma b) (subTm sigma c) (subTy (liftSubst sigma) M)))
        (subEqdm
          (sigmaCompSub (subTm sigma b) (subTm sigma c))
          (sigmaCompSub (subTm tau b) (subTm tau c))
          branchFitsEq
          branchCompFitsEq)
  eqSubDerivTmEqComp (iEqEq d) fitsEq =
    compReflTm (compIEqClosed (compTmEqLeft (eqSubDerivTmEqComp d fitsEq)))
  eqSubDerivTmEqComp (eEqStar dp dA da db) fitsEq =
    let
      compp = eqSubDerivTmComp dp fitsEq
      compab = compEEqClosed (compTmEqLeft compp)
      compbb' = eqSubDerivTmComp db fitsEq
    in
    compTransTmClosed compab compbb'
  eqSubDerivTmEqComp (cEq dp dA da db) fitsEq =
    compCEqClosed (compTmEqLeft (eqSubDerivTmComp dp fitsEq))
  eqSubDerivTmEqComp (iQtrEq da db) fitsEq =
    let
      compab = eqSubDerivTmComp da fitsEq
      compcd = eqSubDerivTmComp db fitsEq
    in
    compIQtrEqClosed (compTmEqLeft compab) (compTmEqRightClosed compcd)
  eqSubDerivTmEqComp (eQtrEq dL dp dl dcoh dcoh') fitsEq =
    eqSubDerivTmEqCompEQtrEq dL dp dl dcoh dcoh' fitsEq
  eqSubDerivTmEqComp (cQtr dL da dl dcoh) fitsEq =
    eqSubDerivTmEqCompCQtr dL da dl dcoh fitsEq
  eqSubDerivTmEqComp {sigma = sigma} {tau = tau}
    (weakenTmEq {delta = delta} {t = t} {u = u} {A = A} d wf) fitsEq =
    subst
      (λ J -> Computable J)
      (cong₃ (termEq [])
        (sym (subTmWkBy sigma (length delta) t))
        (sym (subTmWkBy tau (length delta) u))
        (sym (subTyWkBy sigma (length delta) A)))
      (eqSubDerivTmEqComp d (dropFitsEq delta fitsEq))
  eqSubDerivTmEqComp {sigma = sigma} {tau = tau}
    (substTmEqRule {sigma = sigma'} {t = t} {u = u} {A = A} d fits') fitsEq =
    let
      composedFitsEq = composeEqFits fitsEq fits'
    in
    subst
      (λ J -> Computable J)
      (cong₃ (termEq [])
        (sym (subTmComp sigma sigma' t))
        (sym (subTmComp tau sigma' u))
        (sym (subTyComp sigma sigma' A)))
      (eqSubDerivTmEqComp d composedFitsEq)
  eqSubDerivTmEqComp {sigma = sigma} {tau = tau}
    (eqSubTmRule {sigma = sigma'} {tau = tau'} {t = t} {A = A} d fitsEq') fitsEq =
    let
      composedFitsEq = composeEqFitsEq fitsEq fitsEq'
    in
    subst
      (λ J -> Computable J)
      (cong₃ (termEq [])
        (sym (subTmComp sigma sigma' t))
        (sym (subTmComp tau tau' t))
        (sym (subTyComp sigma sigma' A)))
      (eqSubDerivTmComp d composedFitsEq)
  eqSubDerivTmEqComp {sigma = sigma} {tau = tau}
    (eqSubTmEqRule {sigma = sigma'} {tau = tau'} {t = t} {u = u} {A = A} d fitsEq') fitsEq =
    let
      composedFitsEq = composeEqFitsEq fitsEq fitsEq'
    in
    subst
      (λ J -> Computable J)
      (cong₃ (termEq [])
        (sym (subTmComp sigma sigma' t))
        (sym (subTmComp tau tau' u))
        (sym (subTyComp sigma sigma' A)))
      (eqSubDerivTmEqComp d composedFitsEq)
  substTyClosed d fits = substDerivTyComp d fits

  substTyEqClosed : {delta : Ctx} {A B : RawType} {sigma : Subst}
    -> Derivable (typeEq delta A B)
    -> FitsSubst [] delta sigma
    -> Computable (typeEq [] (subTy sigma A) (subTy sigma B))
  substTyEqClosed d fits = substDerivTyEqComp d fits

  substTmClosed : {delta : Ctx} {t : RawTerm} {A : RawType} {sigma : Subst}
    -> Derivable (hasTy delta t A)
    -> FitsSubst [] delta sigma
    -> Computable (hasTy [] (subTm sigma t) (subTy sigma A))
  substTmClosed d fits = substDerivTmComp d fits

  substTmEqClosed : {delta : Ctx} {t u : RawTerm} {A : RawType} {sigma : Subst}
    -> Derivable (termEq delta t u A)
    -> FitsSubst [] delta sigma
    -> Computable (termEq [] (subTm sigma t) (subTm sigma u) (subTy sigma A))
  substTmEqClosed d fits = substDerivTmEqComp d fits

  eqSubTyClosed d fitsEq = eqSubDerivTyComp d fitsEq

  eqSubTyEqClosed : {delta : Ctx} {A B : RawType} {sigma tau : Subst}
    -> Derivable (typeEq delta A B)
    -> FitsEqSubst [] delta sigma tau
    -> Computable (typeEq [] (subTy sigma A) (subTy tau B))
  eqSubTyEqClosed d fitsEq = eqSubDerivTyEqComp d fitsEq

  eqSubTmClosed : {delta : Ctx} {t : RawTerm} {A : RawType} {sigma tau : Subst}
    -> Derivable (hasTy delta t A)
    -> FitsEqSubst [] delta sigma tau
    -> Computable (termEq [] (subTm sigma t) (subTm tau t) (subTy sigma A))
  eqSubTmClosed d fitsEq = eqSubDerivTmComp d fitsEq

  eqSubTmEqClosed : {delta : Ctx} {t u : RawTerm} {A : RawType} {sigma tau : Subst}
    -> Derivable (termEq delta t u A)
    -> FitsEqSubst [] delta sigma tau
    -> Computable (termEq [] (subTm sigma t) (subTm tau u) (subTy sigma A))
  eqSubTmEqClosed d fitsEq = eqSubDerivTmEqComp d fitsEq

  mkHypComputableTy : {gamma : Ctx} {A : RawType}
    -> ((gamma ≡ []) -> ⊥)
    -> Derivable (isType gamma A)
    -> HypComputable (isType gamma A)
  mkHypComputableTy neq d =
    hypTyOpen
      neq
      d
      (λ sigma fits _ -> substTyClosed d fits)
      (λ sigma tau fitsEq _ -> eqSubTyClosed d fitsEq)

  mkHypComputableTyEq : {gamma : Ctx} {A B : RawType}
    -> ((gamma ≡ []) -> ⊥)
    -> Derivable (typeEq gamma A B)
    -> HypComputable (typeEq gamma A B)
  mkHypComputableTyEq neq d =
    hypTyEqOpen
      neq
      d
      (mkHypComputableTy neq (assocTyLeft d))
      (λ sigma fits _ -> substTyEqClosed d fits)
      (λ sigma tau fitsEq _ -> eqSubTyEqClosed d fitsEq)

  mkHypComputableTm : {gamma : Ctx} {t : RawTerm} {A : RawType}
    -> ((gamma ≡ []) -> ⊥)
    -> Derivable (hasTy gamma t A)
    -> HypComputable (hasTy gamma t A)
  mkHypComputableTm neq d =
    hypTmOpen
      neq
      d
      (mkHypComputableTy neq (assocTy d))
      (λ sigma fits _ -> substTmClosed d fits)
      (λ sigma tau fitsEq _ -> eqSubTmClosed d fitsEq)

  mkHypComputableTmEq : {gamma : Ctx} {t u : RawTerm} {A : RawType}
    -> ((gamma ≡ []) -> ⊥)
    -> Derivable (termEq gamma t u A)
    -> HypComputable (termEq gamma t u A)
  mkHypComputableTmEq neq d =
    hypTmEqOpen
      neq
      d
      (mkHypComputableTm neq (assocTmLeft d))
      (λ sigma fits _ -> substTmEqClosed d fits)
      (λ sigma tau fitsEq _ -> eqSubTmEqClosed d fitsEq)

  hypComputableTy : {A B : RawType} {gamma : Ctx}
    -> Derivable (isType (B ∷ gamma) A)
    -> HypComputable (isType (B ∷ gamma) A)
  hypComputableTy = mkHypComputableTy nonemptyNeNil

  hypComputableTyEq : {A B C : RawType} {gamma : Ctx}
    -> Derivable (typeEq (C ∷ gamma) A B)
    -> HypComputable (typeEq (C ∷ gamma) A B)
  hypComputableTyEq = mkHypComputableTyEq nonemptyNeNil

  hypComputableTm : {t : RawTerm} {A B : RawType} {gamma : Ctx}
    -> Derivable (hasTy (B ∷ gamma) t A)
    -> HypComputable (hasTy (B ∷ gamma) t A)
  hypComputableTm = mkHypComputableTm nonemptyNeNil

  hypComputableTmEq : {t u : RawTerm} {A B : RawType} {gamma : Ctx}
    -> Derivable (termEq (B ∷ gamma) t u A)
    -> HypComputable (termEq (B ∷ gamma) t u A)
  hypComputableTmEq = mkHypComputableTmEq nonemptyNeNil

  hypTyEqLeft : {gamma : Ctx} {A B : RawType}
    -> HypComputable (typeEq gamma A B)
    -> HypComputable (isType gamma A)
  hypTyEqLeft (hypTyEqOpen _ _ compA _ _) = compA

  hypTyEqRight : {gamma : Ctx} {A B : RawType}
    -> HypComputable (typeEq gamma A B)
    -> HypComputable (isType gamma B)
  hypTyEqRight (hypTyEqOpen neq d _ _ _) =
    mkHypComputableTy neq (assocTyRight d)

  hypReflTm : {gamma : Ctx} {t : RawTerm} {A : RawType}
    -> HypComputable (hasTy gamma t A)
    -> HypComputable (termEq gamma t t A)
  hypReflTm comp@(hypTmOpen neq d _ sub subEq) =
    hypTmEqOpen
      neq
      (reflTm d)
      comp
      (λ sigma fits cFits -> compReflTmClosed (sub sigma fits cFits))
      (λ sigma tau fitsEq cFitsEq -> subEq sigma tau fitsEq cFitsEq)

  compTransportFamilyTy : {A C D : RawType}
    -> Computable (typeEq [] A C)
    -> HypComputable (isType (A ∷ []) D)
    -> HypComputable (isType (C ∷ []) D)
  compTransportFamilyTy {A = A} {C = C} compAC compD =
    hypComputableTy (transportFamilyTy dAC dC (hypCompToDerivable compD))
    where
    dAC : Derivable (typeEq [] A C)
    dAC = compToDerivable compAC

    dC : Derivable (isType [] C)
    dC = compToDerivable (compTyEqRightClosed compAC)

  compTransportFamilyTyEq : {A C D F : RawType}
    -> Computable (typeEq [] A C)
    -> HypComputable (typeEq (A ∷ []) D F)
    -> HypComputable (typeEq (C ∷ []) D F)
  compTransportFamilyTyEq {A = A} {C = C} {D = D} {F = F} compAC compDF =
    hypComputableTyEq (transportFamilyTyEq dAC dC (hypCompToDerivable compDF))
    where
    dAC : Derivable (typeEq [] A C)
    dAC = compToDerivable compAC

    dC : Derivable (isType [] C)
    dC = compToDerivable (compTyEqRightClosed compAC)

  compTransTyOpenHelper : {gamma : Ctx} {A B C : RawType}
    -> HypComputable (typeEq gamma A B)
    -> HypComputable (typeEq gamma B C)
    -> HypComputable (typeEq gamma A C)
  compTransTyOpenHelper compAB@(hypTyEqOpen neq _ _ _ _) compBC =
    mkHypComputableTyEq neq
      (transTy (hypCompToDerivable compAB) (hypCompToDerivable compBC))

  compSymTransportFamilyTyEq : {A C D F : RawType}
    -> Computable (typeEq [] A C)
    -> HypComputable (typeEq (A ∷ []) D F)
    -> HypComputable (typeEq (C ∷ []) F D)
  compSymTransportFamilyTyEq {A = A} {C = C} {D = D} {F = F} compAC compDF =
    hypComputableTyEq (symTy transportedEq)
    where
    dAC : Derivable (typeEq [] A C)
    dAC = compToDerivable compAC

    dC : Derivable (isType [] C)
    dC = compToDerivable (compTyEqRightClosed compAC)

    transportedEq : Derivable (typeEq (C ∷ []) D F)
    transportedEq = transportFamilyTyEq dAC dC (hypCompToDerivable compDF)

  compTransTm : {gamma : Ctx} {t u v : RawTerm} {A : RawType}
    -> HypComputable (termEq gamma t u A)
    -> HypComputable (termEq gamma u v A)
    -> HypComputable (termEq gamma t v A)
  compTransTm comp₁@(hypTmEqOpen neq _ _ _ _) comp₂ =
    mkHypComputableTmEq neq
      (transTm (hypCompToDerivable comp₁) (hypCompToDerivable comp₂))

  compSymTm : {gamma : Ctx} {t u : RawTerm} {A : RawType}
    -> HypComputable (termEq gamma t u A)
    -> HypComputable (termEq gamma u t A)
  compSymTm comp@(hypTmEqOpen neq _ _ _ _) =
    mkHypComputableTmEq neq (symTm (hypCompToDerivable comp))

  weakenOneOpenTmEq : {A B C : RawType} {t u : RawTerm}
    -> HypComputable (termEq (A ∷ []) t u B)
    -> CtxWF (C ∷ A ∷ [])
    -> HypComputable (termEq (C ∷ A ∷ []) (wkTmBy 1 t) (wkTmBy 1 u) (wkTyBy 1 B))
  weakenOneOpenTmEq {A = A} {B = B} {C = C} comp wf =
    hypComputableTmEq {A = wkTyBy 1 B} {B = C} {gamma = A ∷ []}
      (weakenTmEq {gamma = A ∷ []} {delta = C ∷ []}
        (hypCompToDerivable comp) wf)

  abstract
    sigmaTyFamHypClosedBuild : {A B : RawType}
      -> Derivable (isType [] A)
      -> Derivable (isType (A ∷ []) B)
      -> HypComputable (isType (A ∷ []) B)
    sigmaTyFamHypClosedBuild _ dB =
      hypTyOpen
        nonemptyNeNil
        dB
        (λ sigma fits _ -> substTyClosed dB fits)
        (λ sigma tau fitsEq _ -> eqSubTyClosed dB fitsEq)

    sigmaTyFamHypClosed : {A B : RawType}
      -> ({A B : RawType}
      -> Derivable (isType [] A)
      -> Derivable (isType (A ∷ []) B)
      -> HypComputable (isType (A ∷ []) B))
      -> Computable (isType [] (tySigma A B))
      -> HypComputable (isType (A ∷ []) B)
    sigmaTyFamHypClosed build
      (compTyClosedSigma {B = A} {C = B} _ evalSigma _ compA dB) =
      build (compToDerivable compA) dB
    sigmaTyFamHypClosed build (compTyClosedTop _ () _)
    sigmaTyFamHypClosed build (compTyClosedEq _ () _ _ _ _)
    sigmaTyFamHypClosed build (compTyClosedQtr _ () _ _)

    sigmaTyFamEqSubClosed : {A B : RawType} {t u : RawTerm}
      -> ({A B : RawType}
      -> Derivable (isType [] A)
      -> Derivable (isType (A ∷ []) B)
      -> HypComputable (isType (A ∷ []) B))
      -> Computable (isType [] (tySigma A B))
      -> Computable (termEq [] t u A)
      -> Computable (typeEq [] (subTy (singleSubst t) B) (subTy (singleSubst u) B))
    sigmaTyFamEqSubClosed build compSigma comptu =
      compSingleEqSubstTyClosed (sigmaTyFamHypClosed build compSigma) comptu

  compConvTmClosedAcc : {t : RawTerm} {A B : RawType}
    -> Computable (hasTy [] t A)
    -> Computable (typeEq [] A B)
    -> Acc _<_ (closedTaskMeasure A)
    -> Computable (hasTy [] t B)
  compConvTmClosedAcc comp (compTyEqClosedTop dAB compA compB evA evB) (acc rs) =
    let
      inv = invertTopTm comp evA
      open ClosedTopTmInv inv
      tyInv = invertTopTy (compTmToCompTy comp) evA
      open ClosedTopTyInv tyInv
      topEqB = transTy (symTy topTyCorr) dAB
    in
    compTmClosedTop
      (conv (compToDerivable comp) dAB)
      compB
      evB
      topTmEvalStar
      (convEq topTmCorrStar topEqB)
  compConvTmClosedAcc
    comp
    (compTyEqClosedSigma {C = C} {D = D} dAB compA compB evA evB compCE dDF)
    (acc rs) =
    let
      inv = invertSigmaTm comp evA
      open ClosedSigmaTmInv inv
      tyInv = invertSigmaTy (compTmToCompTy comp) evA
      open ClosedSigmaTyInv tyInv
      sigmaEqB = transTy (symTy sigmaTyCorr) dAB
      acFst =
        rs _ (rewriteClosedUpper {H = tySigma C D} (evalSigmaPath evA)
          (smallerClosedTask<ClosedTask {A = C} {B = tySigma C D}
            (tyDepth-fst<Sigma C D)))
      acSnd =
        rs _ (rewriteClosedUpper {H = tySigma C D} (evalSigmaPath evA)
          (smallerClosedTask<ClosedTask
            {A = subTy (singleSubst sigmaTmFst) D} {B = tySigma C D}
            (subTySigmaFamilyDepth< (singleSubst sigmaTmFst) C D)))
      compaE = compConvTmClosedAcc sigmaTmCompFst compCE acFst
      compDFa = compSingleSubstTyEqClosed (hypComputableTyEq dDF) sigmaTmCompFst
      compbF = compConvTmClosedAcc sigmaTmCompSnd compDFa acSnd
    in
    compTmClosedSigma
      (conv sigmaTmDeriv sigmaEqB)
      compB
      evB
      sigmaTmEvalPair
      (convEq sigmaTmCorrPair sigmaEqB)
      compaE
      compbF
  compConvTmClosedAcc
    comp
    (compTyEqClosedEq {C = C} {a = a} {b = b} dAB compA compB evA evB compCD compac compbd)
    (acc rs) =
    let
      inv = invertEqTm comp evA
      open ClosedEqTmInv inv
      tyInv = invertEqTy (compTmToCompTy comp) evA
      open ClosedEqTyInv tyInv
      eqEqB = transTy (symTy eqTyCorr) dAB
      acBaseClosed =
        rs _ (rewriteClosedUpper {H = tyEq C a b} (evalEqPath evA)
          (smallerClosedTask<ClosedTask {A = C} {B = tyEq C a b}
            (tyDepth-base<Eq C a b)))
      acBaseOpen =
        rs _ (rewriteClosedUpper {H = tyEq C a b} (evalEqPath evA)
          (smallerOpenTask<ClosedTask {A = C} {B = tyEq C a b}
            (tyDepth-base<Eq C a b)))
      compcdC =
        compTransTmClosedAcc
          (compTransTmClosedAcc (compSymTmClosedAcc compac acBaseClosed) eqTmCompInner acBaseClosed)
          compbd
          acBaseClosed
      compcdD = compConvTmEqClosedAcc compcdC compCD acBaseOpen
    in
    compTmClosedEq
      (conv eqTmDeriv eqEqB)
      compB
      evB
      eqTmEvalRhs
      (convEq eqTmCorrRhs eqEqB)
      compcdD
  compConvTmClosedAcc
    comp
    (compTyEqClosedQtr {C = C} dAB compA compB evA evB compCD)
    (acc rs) =
    let
      inv = invertQtrTm comp evA
      open ClosedQtrTmInv inv
      tyInv = invertQtrTy (compTmToCompTy comp) evA
      open ClosedQtrTyInv tyInv
      qtrEqB = transTy (symTy qtrTyCorr) dAB
      acBase =
        rs _ (rewriteClosedUpper {H = tyQtr C} (evalQtrPath evA)
          (smallerClosedTask<ClosedTask {A = C} {B = tyQtr C}
            (tyDepth-base<Qtr C)))
      compaD = compConvTmClosedAcc qtrTmCompRepr compCD acBase
    in
    compTmClosedQtr
      (conv qtrTmDeriv qtrEqB)
      compB
      evB
      qtrTmEvalClass
      (convEq qtrTmCorrClass qtrEqB)
      compaD

  compConvTmEqClosedAcc : {t u : RawTerm} {A B : RawType}
    -> Computable (termEq [] t u A)
    -> Computable (typeEq [] A B)
    -> Acc _<_ (openTaskMeasure A)
    -> Computable (termEq [] t u B)
  compConvTmEqClosedAcc
    {t = t} {u = u} {A = A} {B = B}
    comp
    compAB@(compTyEqClosedTop dAB compA compB evA evB)
    (acc rs) =
    let
      comp' =
        subst
          (λ X -> Computable (termEq [] t u X))
          (evalTopPath evA)
          comp
      inv = invertTopTmEq0 comp'
      open ClosedTopTmEqInv inv
      compAB' = subst (λ X -> Computable (typeEq [] X B)) (evalTopPath evA) compAB
      acSame = rs _ (rewriteOpenUpper {A = A} {H = tyTop} (evalTopPath evA) (closedTask<openTask tyTop))
    in
    compTmEqClosedTop
      (convEq topTmEqDeriv (compToDerivable compAB'))
      (compConvTmClosedAcc topTmEqCompLeft compAB' acSame)
      (compConvTmClosedAcc topTmEqCompRight compAB' acSame)
      evB
      topTmEqEvalLeftStar
      topTmEqEvalRightStar
  compConvTmEqClosedAcc
    {t = t} {u = u} {A = A} {B = B}
    comp
    compAB@(compTyEqClosedSigma {C = C} {D = D} dAB compA compB evA evB compCE dDF)
    (acc rs) =
    let
      comp' =
        subst
          (λ X -> Computable (termEq [] t u X))
          (evalSigmaPath evA)
          comp
      inv = invertSigmaTmEq0 comp'
      open ClosedSigmaTmEqInv inv
      compA' =
        subst
          (λ X -> Computable (isType [] X))
          (evalSigmaPath evA)
          compA
      tyInv = invertSigmaTy compA' evalSigma
      open ClosedSigmaTyInv tyInv
      compAB' = subst (λ X -> Computable (typeEq [] X B)) (evalSigmaPath evA) compAB
      compLeftA : Computable (hasTy [] t (tySigma C D))
      compLeftA = sigmaTmEqCompLeft
      compRightA : Computable (hasTy [] u (tySigma C D))
      compRightA = sigmaTmEqCompRight
      acSame =
        rs _ (rewriteOpenUpper {A = A} {H = tySigma C D} (evalSigmaPath evA)
          (closedTask<openTask (tySigma C D)))
      acFst =
        rs _ (rewriteOpenUpper {A = A} {H = tySigma C D} (evalSigmaPath evA)
          (smallerOpenTask<OpenTask {A = C} {B = tySigma C D}
            (tyDepth-fst<Sigma C D)))
      acSnd =
        rs _ (rewriteOpenUpper {A = A} {H = tySigma C D} (evalSigmaPath evA)
          (smallerOpenTask<OpenTask
            {A = subTy (singleSubst sigmaTmEqLeftFst) D} {B = tySigma C D}
            (subTySigmaFamilyDepth< (singleSubst sigmaTmEqLeftFst) C D)))
      compLeftB = compConvTmClosedAcc compLeftA compAB' acSame
      compRightB = compConvTmClosedAcc compRightA compAB' acSame
      compFstE = compConvTmEqClosedAcc sigmaTmEqCompFst compCE acFst
      compDFa = compSingleSubstTyEqClosed (hypComputableTyEq dDF) (compTmEqLeft sigmaTmEqCompFst)
      compSndF = compConvTmEqClosedAcc sigmaTmEqCompSnd compDFa acSnd
    in
    compTmEqClosedSigma
      (convEq sigmaTmEqDeriv (compToDerivable compAB'))
      compLeftB
      compRightB
      evB
      sigmaTmEqEvalLeftPair
      sigmaTmEqEvalRightPair
      compFstE
      compSndF
  compConvTmEqClosedAcc
    {t = t} {u = u} {A = A} {B = B}
    comp
    compAB@(compTyEqClosedEq {C = C} {a = a} {b = b} dAB compA compB evA evB compCD compac compbd)
    (acc rs) =
    let
      comp' =
        subst
          (λ X -> Computable (termEq [] t u X))
          (evalEqPath evA)
          comp
      inv = invertEqTmEq0 comp'
      open ClosedEqTmEqInv inv
      compA' =
        subst
          (λ X -> Computable (isType [] X))
          (evalEqPath evA)
          compA
      tyInv = invertEqTy compA' evalEq
      open ClosedEqTyInv tyInv
      compAB' = subst (λ X -> Computable (typeEq [] X B)) (evalEqPath evA) compAB
      compLeftA : Computable (hasTy [] t (tyEq C a b))
      compLeftA = eqTmEqCompLeft
      compRightA : Computable (hasTy [] u (tyEq C a b))
      compRightA = eqTmEqCompRight
      acSame =
        rs _ (rewriteOpenUpper {A = A} {H = tyEq C a b} (evalEqPath evA)
          (closedTask<openTask (tyEq C a b)))
      acBaseClosed =
        rs _ (rewriteOpenUpper {A = A} {H = tyEq C a b} (evalEqPath evA)
          (smallerClosedTask<OpenTask {A = C} {B = tyEq C a b}
            (tyDepth-base<Eq C a b)))
      acBaseOpen =
        rs _ (rewriteOpenUpper {A = A} {H = tyEq C a b} (evalEqPath evA)
          (smallerOpenTask<OpenTask {A = C} {B = tyEq C a b}
            (tyDepth-base<Eq C a b)))
      compLeftB = compConvTmClosedAcc compLeftA compAB' acSame
      compRightB = compConvTmClosedAcc compRightA compAB' acSame
      compcdC =
        compTransTmClosedAcc
          (compTransTmClosedAcc (compSymTmClosedAcc compac acBaseClosed) eqTmEqCompInner acBaseClosed)
          compbd
          acBaseClosed
      compcdD = compConvTmEqClosedAcc compcdC compCD acBaseOpen
    in
    compTmEqClosedEq
      (convEq eqTmEqDeriv (compToDerivable compAB'))
      compLeftB
      compRightB
      evB
      eqTmEqEvalLeftR
      eqTmEqEvalRightR
      compcdD
  compConvTmEqClosedAcc
    {t = t} {u = u} {A = A} {B = B}
    comp
    compAB@(compTyEqClosedQtr {C = C} dAB compA compB evA evB compCD)
    (acc rs) =
    let
      comp' =
        subst
          (λ X -> Computable (termEq [] t u X))
          (evalQtrPath evA)
          comp
      inv = invertQtrTmEq0 comp'
      open ClosedQtrTmEqInv inv
      compA' =
        subst
          (λ X -> Computable (isType [] X))
          (evalQtrPath evA)
          compA
      tyInv = invertQtrTy compA' evalQtr
      open ClosedQtrTyInv tyInv
      compAB' = subst (λ X -> Computable (typeEq [] X B)) (evalQtrPath evA) compAB
      compLeftA : Computable (hasTy [] t (tyQtr C))
      compLeftA = qtrTmEqCompLeft
      compRightA : Computable (hasTy [] u (tyQtr C))
      compRightA = qtrTmEqCompRight
      acSame =
        rs _ (rewriteOpenUpper {A = A} {H = tyQtr C} (evalQtrPath evA)
          (closedTask<openTask (tyQtr C)))
      acBase =
        rs _ (rewriteOpenUpper {A = A} {H = tyQtr C} (evalQtrPath evA)
          (smallerClosedTask<OpenTask {A = C} {B = tyQtr C}
            (tyDepth-base<Qtr C)))
      compLeftB = compConvTmClosedAcc compLeftA compAB' acSame
      compRightB = compConvTmClosedAcc compRightA compAB' acSame
      compaD = compConvTmClosedAcc qtrTmEqCompLeftRepr compCD acBase
      compbD = compConvTmClosedAcc qtrTmEqCompRightRepr compCD acBase
    in
    compTmEqClosedQtr
      (convEq qtrTmEqDeriv (compToDerivable compAB'))
      compLeftB
      compRightB
      evB
      qtrTmEqEvalLeftClass
      qtrTmEqEvalRightClass
      compaD
      compbD

  compSymTmClosedAcc : {t u : RawTerm} {A : RawType}
    -> Computable (termEq [] t u A)
    -> Acc _<_ (closedTaskMeasure A)
    -> Computable (termEq [] u t A)
  compSymTmClosedAcc (compTmEqClosedTop d compt compu evA evt evu) (acc rs) =
    compTmEqClosedTop (symTm d) compu compt evA evu evt
  compSymTmClosedAcc
    comp@(compTmEqClosedSigma {a = a} {A = B} {B = C} d compt compu evA evt evu compac compbd)
    (acc rs) =
    let
      acFst =
        rs _ (rewriteClosedUpper {H = tySigma B C} (evalSigmaPath evA)
          (smallerClosedTask<ClosedTask {A = B} {B = tySigma B C}
            (tyDepth-fst<Sigma B C)))
      acSndClosed =
        rs _ (rewriteClosedUpper {H = tySigma B C} (evalSigmaPath evA)
          (smallerClosedTask<ClosedTask
            {A = subTy (singleSubst a) C} {B = tySigma B C}
            (subTySigmaFamilyDepth< (singleSubst a) B C)))
      acSndOpen =
        rs _ (rewriteClosedUpper {H = tySigma B C} (evalSigmaPath evA)
          (smallerOpenTask<ClosedTask
            {A = subTy (singleSubst a) C} {B = tySigma B C}
            (subTySigmaFamilyDepth< (singleSubst a) B C)))
      compSigma =
        subst
          (λ X -> Computable (isType [] X))
          (evalSigmaPath evA)
          (compTmToCompTy compt)
      compca = compSymTmClosedAcc compac acFst
      compdb = compSymTmClosedAcc compbd acSndClosed
      compBac = sigmaTyFamEqSubClosed sigmaTyFamHypClosedBuild compSigma compac
      compdb' = compConvTmEqClosedAcc compdb compBac acSndOpen
    in
    compTmEqClosedSigma
      (symTm d)
      compu
      compt
      evA
      evu
      evt
      compca
      compdb'
  compSymTmClosedAcc (compTmEqClosedEq d compt compu evA evt evu compab) (acc rs) =
    compTmEqClosedEq
      (symTm d)
      compu
      compt
      evA
      evu
      evt
      compab
  compSymTmClosedAcc (compTmEqClosedQtr d compt compu evA evt evu compa compb) (acc rs) =
    compTmEqClosedQtr
      (symTm d)
      compu
      compt
      evA
      evu
      evt
      compb
      compa

  compTransTmClosedAcc : {t u v : RawTerm} {A : RawType}
    -> Computable (termEq [] t u A)
    -> Computable (termEq [] u v A)
    -> Acc _<_ (closedTaskMeasure A)
    -> Computable (termEq [] t v A)
  compTransTmClosedAcc (compTmEqClosedTop d₁ compt _ evA evt evu) comp₂ (acc rs) =
    let
      inv₂ = invertTopTmEq comp₂ evA
      open ClosedTopTmEqInv inv₂
    in
    compTmEqClosedTop
      (transTm d₁ (compToDerivable comp₂))
      compt
      (compTmEqRightClosed comp₂)
      evA
      evt
      topTmEqEvalRightStar
  compTransTmClosedAcc
    comp₁@(compTmEqClosedSigma {a = a} {b = b} {c = c} {d = d} {A = C} {B = D}
      d₁ compt _ evA evt evu compac compbd)
    comp₂
    (acc rs) =
    let
      inv₂ = invertSigmaTmEq comp₂ evA
      open ClosedSigmaTmEqInv inv₂
      pairEq = evalDetTm evu sigmaTmEqEvalLeftPair
      c≡left = tmPairInj₁ pairEq
      d≡left = tmPairInj₂ pairEq
      compce =
        subst
          (λ x -> Computable (termEq [] x sigmaTmEqRightFst C))
          (sym c≡left)
          sigmaTmEqCompFst
      compdfC =
        subst
          (λ x -> Computable (termEq [] x sigmaTmEqRightSnd (subTy (singleSubst c) D)))
          (sym d≡left)
          (subst
            (λ T -> Computable (termEq [] sigmaTmEqLeftSnd sigmaTmEqRightSnd T))
            (cong (λ x -> subTy (singleSubst x) D) (sym c≡left))
            sigmaTmEqCompSnd)
      acFst =
        rs _ (rewriteClosedUpper {H = tySigma C D} (evalSigmaPath evA)
          (smallerClosedTask<ClosedTask {A = C} {B = tySigma C D}
            (tyDepth-fst<Sigma C D)))
      acSndCOpen =
        rs _ (rewriteClosedUpper {H = tySigma C D} (evalSigmaPath evA)
          (smallerOpenTask<ClosedTask
            {A = subTy (singleSubst c) D} {B = tySigma C D}
            (subTySigmaFamilyDepth< (singleSubst c) C D)))
      acSndAClosed =
        rs _ (rewriteClosedUpper {H = tySigma C D} (evalSigmaPath evA)
          (smallerClosedTask<ClosedTask
            {A = subTy (singleSubst a) D} {B = tySigma C D}
            (subTySigmaFamilyDepth< (singleSubst a) C D)))
      compSigma =
        subst
          (λ X -> Computable (isType [] X))
          (evalSigmaPath evA)
          (compTmToCompTy compt)
      compca = compSymTmClosedAcc compac acFst
      compae = compTransTmClosedAcc compac compce acFst
      compDca = sigmaTyFamEqSubClosed sigmaTyFamHypClosedBuild compSigma compca
      compdfA = compConvTmEqClosedAcc compdfC compDca acSndCOpen
      compbf = compTransTmClosedAcc compbd compdfA acSndAClosed
    in
    compTmEqClosedSigma
      (transTm d₁ (compToDerivable comp₂))
      compt
      (compTmEqRightClosed comp₂)
      evA
      evt
      sigmaTmEqEvalRightPair
      compae
      compbf
  compTransTmClosedAcc comp₁@(compTmEqClosedEq d₁ compt _ evA evt evu compab) comp₂ (acc rs) =
    let
      inv₂ = invertEqTmEq comp₂ evA
      open ClosedEqTmEqInv inv₂
    in
    compTmEqClosedEq
      (transTm d₁ (compToDerivable comp₂))
      compt
      (compTmEqRightClosed comp₂)
      evA
      evt
      eqTmEqEvalRightR
      compab
  compTransTmClosedAcc comp₁@(compTmEqClosedQtr d₁ compt _ evA evt evu compa compb) comp₂ (acc rs) =
    let
      inv₂ = invertQtrTmEq comp₂ evA
      open ClosedQtrTmEqInv inv₂
    in
    compTmEqClosedQtr
      (transTm d₁ (compToDerivable comp₂))
      compt
      (compTmEqRightClosed comp₂)
      evA
      evt
      qtrTmEqEvalRightClass
      compa
      qtrTmEqCompRightRepr

  compConvTmClosed : {t : RawTerm} {A B : RawType}
    -> Computable (hasTy [] t A)
    -> Computable (typeEq [] A B)
    -> Computable (hasTy [] t B)
  compConvTmClosed {A = A} comp compAB =
    compConvTmClosedAcc comp compAB (<-wellfounded (closedTaskMeasure A))

  compConvTmEqClosed : {t u : RawTerm} {A B : RawType}
    -> Computable (termEq [] t u A)
    -> Computable (typeEq [] A B)
    -> Computable (termEq [] t u B)
  compConvTmEqClosed {A = A} comp compAB =
    compConvTmEqClosedAcc comp compAB (<-wellfounded (openTaskMeasure A))

  compSymTmClosed : {t u : RawTerm} {A : RawType}
    -> Computable (termEq [] t u A)
    -> Computable (termEq [] u t A)
  compSymTmClosed {A = A} comp =
    compSymTmClosedAcc comp (<-wellfounded (closedTaskMeasure A))

  compTransTmClosed : {t u v : RawTerm} {A : RawType}
    -> Computable (termEq [] t u A)
    -> Computable (termEq [] u v A)
    -> Computable (termEq [] t v A)
  compTransTmClosed {A = A} comp₁ comp₂ =
    compTransTmClosedAcc comp₁ comp₂ (<-wellfounded (closedTaskMeasure A))

  compSymTyClosedAcc : {A B : RawType}
    -> Computable (typeEq [] A B)
    -> Acc _<_ (closedTaskMeasure A)
    -> Computable (typeEq [] B A)
  compSymTyClosedAcc (compTyEqClosedTop d compA compB evA evB) (acc rs) =
    compTyEqClosedTop (symTy d) compB compA evB evA
  compSymTyClosedAcc
    {A = AΣ}
    (compTyEqClosedSigma {C = C} {D = D} {E = E} {F = F} d compA compB evA evB compCE compDF)
    (acc rs) =
    let
      acHead =
        rs _ (rewriteClosedUpper {H = tySigma C D} (evalSigmaPath evA)
          (smallerClosedTask<ClosedTask {A = C} {B = tySigma C D}
            (tyDepth-fst<Sigma C D)))
    in
      compTyEqClosedSigma
        (symTy d)
        compB
        compA
        evB
        evA
        (compSymTyClosedAcc compCE acHead)
        (hypCompToDerivable
          (compSymTransportFamilyTyEq
            compCE
            (hypComputableTyEq compDF)))
  compSymTyClosedAcc
    (compTyEqClosedEq {C = C} {a = a} {b = b} d compA compB evA evB compCD compac compbd)
    (acc rs) =
    let
      acBase =
        rs _ (rewriteClosedUpper {H = tyEq C a b} (evalEqPath evA)
          (smallerClosedTask<ClosedTask {A = C} {B = tyEq C a b}
            (tyDepth-base<Eq C a b)))
    in
    compTyEqClosedEq
      (symTy d)
      compB
      compA
      evB
      evA
      (compSymTyClosedAcc compCD acBase)
      (compConvTmEqClosed (compSymTmClosed compac) compCD)
      (compConvTmEqClosed (compSymTmClosed compbd) compCD)
  compSymTyClosedAcc
    (compTyEqClosedQtr {C = C} d compA compB evA evB compCD)
    (acc rs) =
    let
      acBase =
        rs _ (rewriteClosedUpper {H = tyQtr C} (evalQtrPath evA)
          (smallerClosedTask<ClosedTask {A = C} {B = tyQtr C}
            (tyDepth-base<Qtr C)))
    in
    compTyEqClosedQtr
      (symTy d)
      compB
      compA
      evB
      evA
      (compSymTyClosedAcc compCD acBase)

  compTransTyClosedAcc : {A B C : RawType}
    -> Computable (typeEq [] A B)
    -> Computable (typeEq [] B C)
    -> Acc _<_ (closedTaskMeasure A)
    -> Computable (typeEq [] A C)
  compTransTyClosedAcc
    (compTyEqClosedTop dAB compA compB evA evB)
    (compTyEqClosedTop dBC _ compC evB' evC)
    (acc rs) =
    compTyEqClosedTop
      (transTy dAB dBC)
      compA
      compC
      evA
      evC
  compTransTyClosedAcc
    (compTyEqClosedTop _ _ _ _ evB)
    (compTyEqClosedSigma _ _ _ evB' _ _ _)
    _ =
    Empty.rec (topNeSigma (sym (evalTopPath evB) ∙ evalSigmaPath evB'))
  compTransTyClosedAcc
    (compTyEqClosedTop _ _ _ _ evB)
    (compTyEqClosedEq _ _ _ evB' _ _ _ _)
    _ =
    Empty.rec (topNeEq (sym (evalTopPath evB) ∙ evalEqPath evB'))
  compTransTyClosedAcc
    (compTyEqClosedTop _ _ _ _ evB)
    (compTyEqClosedQtr _ _ _ evB' _ _)
    _ =
    Empty.rec (topNeQtr (sym (evalTopPath evB) ∙ evalQtrPath evB'))
  compTransTyClosedAcc
    comp₁@(compTyEqClosedSigma {C = C} {D = D} dAB compA compB evA evB compCE compDF)
    comp₂
    (acc rs) =
    let
      inv₂ = invertSigmaTyEq comp₂ evB
      open ClosedSigmaTyEqInv inv₂
      acHead =
        rs _ (rewriteClosedUpper {H = tySigma C D} (evalSigmaPath evA)
          (smallerClosedTask<ClosedTask {A = C} {B = tySigma C D}
            (tyDepth-fst<Sigma C D)))
      compCG = compTransTyClosedAcc compCE sigmaTyEqCompHead acHead
      compGC = compSymTyClosedAcc compCE acHead
      compFH = compTransportFamilyTyEq compGC (hypComputableTyEq sigmaTyEqFamDeriv)
      compDH = compTransTyOpenHelper (hypComputableTyEq compDF) compFH
    in
    compTyEqClosedSigma
      (transTy dAB (compToDerivable comp₂))
      compA
      sigmaTyEqCompRight
      evA
      sigmaTyEqEvalRight
      compCG
      (hypCompToDerivable compDH)
  compTransTyClosedAcc
    (compTyEqClosedEq {C = C} {a = a} {b = b} dAB compA compB evA evB compCD compac compbd)
    comp₂
    (acc rs) =
    let
      inv₂ = invertEqTyEq comp₂ evB
      open ClosedEqTyEqInv inv₂
      acBase =
        rs _ (rewriteClosedUpper {H = tyEq C a b} (evalEqPath evA)
          (smallerClosedTask<ClosedTask {A = C} {B = tyEq C a b}
            (tyDepth-base<Eq C a b)))
      compDG = compTransTyClosedAcc compCD eqTyEqCompBase acBase
      compeRight = compConvTmEqClosed eqTyEqCompLeftTerm (compSymTyClosedAcc compCD acBase)
      compfRight = compConvTmEqClosed eqTyEqCompRightTerm (compSymTyClosedAcc compCD acBase)
      compae = compTransTmClosed compac compeRight
      compbf = compTransTmClosed compbd compfRight
    in
    compTyEqClosedEq
      (transTy dAB (compToDerivable comp₂))
      compA
      eqTyEqCompRight
      evA
      eqTyEqEvalRight
      compDG
      compae
      compbf
  compTransTyClosedAcc
    (compTyEqClosedQtr {C = C} dAB compA compB evA evB compCD)
    comp₂
    (acc rs) =
    let
      inv₂ = invertQtrTyEq comp₂ evB
      open ClosedQtrTyEqInv inv₂
      acBase =
        rs _ (rewriteClosedUpper {H = tyQtr C} (evalQtrPath evA)
          (smallerClosedTask<ClosedTask {A = C} {B = tyQtr C}
            (tyDepth-base<Qtr C)))
    in
    compTyEqClosedQtr
      (transTy dAB (compToDerivable comp₂))
      compA
      qtrTyEqCompRight
      evA
      qtrTyEqEvalRight
      (compTransTyClosedAcc compCD qtrTyEqCompBase acBase)

  compSymTyClosed : {A B : RawType}
    -> Computable (typeEq [] A B)
    -> Computable (typeEq [] B A)
  compSymTyClosed {A = A} comp =
    compSymTyClosedAcc comp (<-wellfounded (closedTaskMeasure A))

  compTransTyClosed : {A B C : RawType}
    -> Computable (typeEq [] A B)
    -> Computable (typeEq [] B C)
    -> Computable (typeEq [] A C)
  compTransTyClosed {A = A} comp₁ comp₂ =
    compTransTyClosedAcc comp₁ comp₂ (<-wellfounded (closedTaskMeasure A))

  computableTyClosed : {A : RawType}
    -> Derivable (isType [] A)
    -> Computable (isType [] A)
  computableTyClosed {A = A} d =
    subst
      (λ T -> Computable (isType [] T))
      (subTyId A)
      (substTyClosed d (fitsNil {gamma = []} {delta = []} {sigma = idSubst} wfNil))

  computableTyEqClosed : {A B : RawType}
    -> Derivable (typeEq [] A B)
    -> Computable (typeEq [] A B)
  computableTyEqClosed {A = A} {B = B} d =
    subst
      (λ J -> Computable J)
      (cong₂ (typeEq []) (subTyId A) (subTyId B))
      (substTyEqClosed d (fitsNil {gamma = []} {delta = []} {sigma = idSubst} wfNil))

  computableTmClosed : {t : RawTerm} {A : RawType}
    -> Derivable (hasTy [] t A)
    -> Computable (hasTy [] t A)
  computableTmClosed {t = t} {A = A} d =
    subst
      (λ J -> Computable J)
      (cong₂ (hasTy []) (subTmId t) (subTyId A))
      (substTmClosed d (fitsNil {gamma = []} {delta = []} {sigma = idSubst} wfNil))

  computableTmEqClosed : {t u : RawTerm} {A : RawType}
    -> Derivable (termEq [] t u A)
    -> Computable (termEq [] t u A)
  computableTmEqClosed {t = t} {u = u} {A = A} d =
    subst
      (λ J -> Computable J)
      (cong₃ (termEq []) (subTmId t) (subTmId u) (subTyId A))
      (substTmEqClosed d (fitsNil {gamma = []} {delta = []} {sigma = idSubst} wfNil))

CanonicalForm : JForm -> Type
CanonicalForm (isType [] A) =
  Σ[ G ∈ RawType ] (A =>t G) × Derivable (typeEq [] A G)
CanonicalForm (typeEq [] A B) =
  Σ[ G ∈ RawType ] Σ[ H ∈ RawType ] (A =>t G) × (B =>t H)
CanonicalForm (hasTy [] t A) =
  Σ[ g ∈ RawTerm ] Σ[ G ∈ RawType ] (t =>e g) × (A =>t G)
CanonicalForm (termEq [] t u A) =
  Σ[ g ∈ RawTerm ] Σ[ h ∈ RawTerm ] Σ[ G ∈ RawType ] (t =>e g) × (u =>e h) × (A =>t G)
CanonicalForm (isType (_ ∷ _) A) = Unit
CanonicalForm (typeEq (_ ∷ _) A B) = Unit
CanonicalForm (hasTy (_ ∷ _) t A) = Unit
CanonicalForm (termEq (_ ∷ _) t u A) = Unit

canonicalFormTheorem : {J : JForm} -> Derivable J -> CanonicalForm J
canonicalFormTheorem {J = isType [] A} d =
  canonicalType (computableTyClosed d)
canonicalFormTheorem {J = typeEq [] A B} d =
  canonicalTypeEq (computableTyEqClosed d)
canonicalFormTheorem {J = hasTy [] t A} d =
  canonicalTerm (computableTmClosed d)
canonicalFormTheorem {J = termEq [] t u A} d =
  canonicalTermEq (computableTmEqClosed d)
canonicalFormTheorem {J = isType (_ ∷ _) A} d = tt
canonicalFormTheorem {J = typeEq (_ ∷ _) A B} d = tt
canonicalFormTheorem {J = hasTy (_ ∷ _) t A} d = tt
canonicalFormTheorem {J = termEq (_ ∷ _) t u A} d = tt
