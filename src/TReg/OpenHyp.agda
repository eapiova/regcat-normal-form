{-# OPTIONS #-}
-- Phase F.5 Stage 2: parameterized openHypTm* helpers.
--
-- These were originally in CompTheorem.agda's main mutual block. They
-- mutually-recurse with substDerivTm[Eq]CompCF and eqSubDerivTm[Eq]CompCF
-- via stored hypTmOpen / hypTmEqOpen closure bodies. To extract them
-- into a separate file, we parameterize the helpers over those recursive
-- callbacks, plus composeCompFits and fitsEqToCompFitsEq (also in the
-- main mutual block).
--
-- Pilot: openHypTm1 only. If this validates, the other 3 helpers
-- (openHypTmEq1, openHypTm2, openHypTmEq2) follow the same pattern.

module TReg.OpenHyp where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Empty.Base as Empty using (⊥ ; rec)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.List.Base using ([] ; _∷_ ; length)
open import Cubical.Induction.WellFounded using (Acc ; acc ; access)

open import TReg.Syntax
open import TReg.Context
open import TReg.Substitution
open import TReg.Measure
open import TReg.Evaluation
open import TReg.Derivability
open import TReg.Computability
open import TReg.StructuralBase using (composeFits)
open import TReg.Presupposition using (fitsSubstCtxWF)
open import TReg.FitsHelpers

-- Type aliases for the callback signatures, to keep the openHypTm* signatures readable.
SubRecTy : Type
SubRecTy = ∀ {n} {gamma : Ctx} {t : RawTerm} {A : RawType} {sigma : Subst}
  -> (d : Derivable (hasTy gamma t A))
  -> (fits : FitsSubst [] gamma sigma)
  -> ComputableFits n fits
  -> Acc LexLt (substTaskLexMeasure d)
  -> Computable n (hasTy [] (subTm sigma t) (subTy sigma A))

EqSubRecTy : Type
EqSubRecTy = ∀ {n} {gamma : Ctx} {t : RawTerm} {A : RawType} {sigma tau : Subst}
  -> (d : Derivable (hasTy gamma t A))
  -> (fitsEq : FitsEqSubst [] gamma sigma tau)
  -> ComputableFitsEq n fitsEq
  -> Acc LexLt (substTaskLexMeasure d)
  -> Computable n (termEq [] (subTm sigma t) (subTm tau t) (subTy sigma A))

ComposeCompFitsTy : Type
ComposeCompFitsTy = ∀ {n} {gamma delta : Ctx} {rho sigma : Subst} {t : RawTerm} {T : RawType}
  -> (outer : FitsSubst [] gamma rho)
  -> ComputableFits n outer
  -> (inner : FitsSubst gamma delta sigma)
  -> (dt : Derivable (hasTy gamma t T))
  -> Acc LexLt (substTaskLexMeasure dt)
  -> ComputableFits n (composeFits outer inner)

FitsEqToCompFitsEqTy : Type
FitsEqToCompFitsEqTy = ∀ {n} {gamma : Ctx} {sigma tau : Subst}
  -> (fitsEq : FitsEqSubst [] gamma sigma tau)
  -> ComputableFitsEq n fitsEq

FitsToCompFitsTy : Type
FitsToCompFitsTy = ∀ {n} {gamma : Ctx} {sigma : Subst}
  -> (fits : FitsSubst [] gamma sigma)
  -> ComputableFits n fits

SubEqRecTy : Type
SubEqRecTy = ∀ {n} {gamma : Ctx} {t u : RawTerm} {A : RawType} {sigma : Subst}
  -> (d : Derivable (termEq gamma t u A))
  -> (fits : FitsSubst [] gamma sigma)
  -> ComputableFits n fits
  -> Acc LexLt (substTaskLexMeasure d)
  -> Computable n (termEq [] (subTm sigma t) (subTm sigma u) (subTy sigma A))

EqSubEqRecTy : Type
EqSubEqRecTy = ∀ {n} {gamma : Ctx} {t u : RawTerm} {A : RawType} {sigma tau : Subst}
  -> (d : Derivable (termEq gamma t u A))
  -> (fitsEq : FitsEqSubst [] gamma sigma tau)
  -> ComputableFitsEq n fitsEq
  -> Acc LexLt (substTaskLexMeasure d)
  -> Computable n (termEq [] (subTm sigma t) (subTm tau u) (subTy sigma A))

-- openHypTm1: parameterized over substRec, eqSubRec, composeCompFitsCb, fitsEqToCompFitsEqCb.
openHypTm1
  : (substRec : SubRecTy)
  -> (eqSubRec : EqSubRecTy)
  -> (composeCompFitsCb : ComposeCompFitsTy)
  -> (fitsEqToCompFitsEqCb : FitsEqToCompFitsEqTy)
  -> {n : ℕ} -> {gamma : Ctx} {A T : RawType} {t : RawTerm} {sigma : Subst}
  -> (fits : FitsSubst [] gamma sigma)
  -> ComputableFits n fits
  -> Derivable (isType [] (subTy sigma A))
  -> HypComputable (suc n) (isType (subTy sigma A ∷ []) (subTy (liftSubst sigma) T))
  -> (dt : Derivable (hasTy (A ∷ gamma) t T))
  -> Acc LexLt (substTaskLexMeasure dt)
  -> HypComputable (suc n)
       (hasTy (subTy sigma A ∷ [])
         (subTm (liftSubst sigma) t)
         (subTy (liftSubst sigma) T))
openHypTm1 substRec eqSubRec composeCompFitsCb fitsEqToCompFitsEqCb
  {n} {gamma = gamma} {A = A} {T = T} {t = t} {sigma = sigma}
  fits cFits dAσ compT dt accDt =
  subst
    (λ J -> HypComputable (suc n) J)
    (cong₂
      (hasTy (subTy sigma A ∷ []))
      (cong (λ rho -> subTm rho t) (liftSubstCompKeep sigma))
      (cong (λ rho -> subTy rho T) (liftSubstCompKeep sigma)))
    (hypTmOpen
      nonemptyNeNil
      (substTmRule dt (liftFitsOne fits dAσ))
      (subst
        (λ J -> HypComputable (suc n) J)
        (sym
          (cong
            (λ rho -> isType (subTy sigma A ∷ []) (subTy rho T))
            (liftSubstCompKeep sigma)))
        compT)
      -- Phase F.3: destructure closure Acc, use accRs _ proof< for recursion on dt
      (λ tau fits2 cFits2 accD ->
        let
          composedFits =
            subst
              (λ rho -> FitsSubst [] (A ∷ gamma) rho)
              (cong (compSub tau) (liftSubstCompKeep sigma))
              (composeFits fits2 (liftFitsOne fits dAσ))
          composedCFits =
            substCompFits
              (cong (compSub tau) (liftSubstCompKeep sigma))
              (composeCompFitsCb
                fits2
                cFits2
                (liftFitsOne fits dAσ)
                (iTop (fitsSubstCtxWF (liftFitsOne fits dAσ)))
                (LexLt-wf _))
        in
        subst
          (λ J -> Computable n J)
          (sym
            (cong₂ (hasTy [])
              (cong (λ rho -> subTm tau (subTm rho t)) (liftSubstCompKeep sigma)
                ∙ subTmComp tau (liftSubst sigma) t)
              (cong (λ rho -> subTy tau (subTy rho T)) (liftSubstCompKeep sigma)
                ∙ subTyComp tau (liftSubst sigma) T)))
          (substRec dt composedFits composedCFits
            (access accD _ (lift-lex-eq {d₁ = dt} {d₂ = substTmRule dt (liftFitsOne fits dAσ)}
              (sym (tyDepth-subTy (consSubst (var zero) (compSub (keepSubstBy 1) sigma)) T))
              (substMeasure-substTmRule< dt (liftFitsOne fits dAσ))))))
      (λ tau₁ tau₂ fitsEq2 _ accD ->
        subst
          (λ J -> Computable n J)
          (sym
            (cong₃ (termEq [])
              (cong (λ rho -> subTm tau₁ (subTm rho t)) (liftSubstCompKeep sigma)
                ∙ subTmComp tau₁ (liftSubst sigma) t)
              (cong (λ rho -> subTm tau₂ (subTm rho t)) (liftSubstCompKeep sigma)
                ∙ subTmComp tau₂ (liftSubst sigma) t)
              (cong (λ rho -> subTy tau₁ (subTy rho T)) (liftSubstCompKeep sigma)
                ∙ subTyComp tau₁ (liftSubst sigma) T)))
          (eqSubRec
            dt
            (composeOneBinderEq fits dAσ fitsEq2)
            (fitsEqToCompFitsEqCb (composeOneBinderEq fits dAσ fitsEq2))
            (access accD _ (lift-lex-eq {d₁ = dt} {d₂ = substTmRule dt (liftFitsOne fits dAσ)}
              (sym (tyDepth-subTy (consSubst (var zero) (compSub (keepSubstBy 1) sigma)) T))
              (substMeasure-substTmRule< dt (liftFitsOne fits dAσ)))))))

-- openHypTmEq1: parameterized over substEqRec, eqSubEqRec, fitsToCompFitsCb, fitsEqToCompFitsEqCb.
openHypTmEq1
  : (substEqRec : SubEqRecTy)
  -> (eqSubEqRec : EqSubEqRecTy)
  -> (fitsToCompFitsCb : FitsToCompFitsTy)
  -> (fitsEqToCompFitsEqCb : FitsEqToCompFitsEqTy)
  -> {n : ℕ} -> {gamma : Ctx} {A T : RawType} {t u : RawTerm} {sigma : Subst}
  -> FitsSubst [] gamma sigma
  -> Derivable (isType [] (subTy sigma A))
  -> HypComputable (suc n)
       (hasTy (subTy sigma A ∷ [])
         (subTm (liftSubst sigma) t)
         (subTy (liftSubst sigma) T))
  -> (dtu : Derivable (termEq (A ∷ gamma) t u T))
  -> Acc LexLt (substTaskLexMeasure dtu)
  -> HypComputable (suc n)
       (termEq (subTy sigma A ∷ [])
         (subTm (liftSubst sigma) t)
         (subTm (liftSubst sigma) u)
         (subTy (liftSubst sigma) T))
openHypTmEq1 substEqRec eqSubEqRec fitsToCompFitsCb fitsEqToCompFitsEqCb
  {n} {A = A} {T = T} {t = t} {u = u} {sigma = sigma}
  fits dAσ compt dtu accDtu =
  subst
    (λ J -> HypComputable (suc n) J)
    (cong₃
      (termEq (subTy sigma A ∷ []))
      (cong (λ rho -> subTm rho t) (liftSubstCompKeep sigma))
      (cong (λ rho -> subTm rho u) (liftSubstCompKeep sigma))
      (cong (λ rho -> subTy rho T) (liftSubstCompKeep sigma)))
    (hypTmEqOpen
      nonemptyNeNil
      (substTmEqRule dtu (liftFitsOne fits dAσ))
      (subst
        (λ J -> HypComputable (suc n) J)
        (sym
          (cong₂
            (hasTy (subTy sigma A ∷ []))
            (cong (λ rho -> subTm rho t) (liftSubstCompKeep sigma))
            (cong (λ rho -> subTy rho T) (liftSubstCompKeep sigma))))
        compt)
      -- Phase F.3: destructure closure Acc, use accRs _ proof< for recursion on dtu
      (λ tau fits2 _ accD ->
        subst
          (λ J -> Computable n J)
          (sym
            (cong₃ (termEq [])
              (cong (λ rho -> subTm tau (subTm rho t)) (liftSubstCompKeep sigma)
                ∙ subTmComp tau (liftSubst sigma) t)
              (cong (λ rho -> subTm tau (subTm rho u)) (liftSubstCompKeep sigma)
                ∙ subTmComp tau (liftSubst sigma) u)
              (cong (λ rho -> subTy tau (subTy rho T)) (liftSubstCompKeep sigma)
                ∙ subTyComp tau (liftSubst sigma) T)))
          (substEqRec
            dtu
            (composeOneBinder fits dAσ fits2)
            (fitsToCompFitsCb (composeOneBinder fits dAσ fits2))
            (access accD _ (lift-lex-eq {d₁ = dtu} {d₂ = substTmEqRule dtu (liftFitsOne fits dAσ)}
              (sym (tyDepth-subTy (consSubst (var zero) (compSub (keepSubstBy 1) sigma)) T))
              (substMeasure-substTmEqRule< dtu (liftFitsOne fits dAσ))))))
      (λ tau₁ tau₂ fitsEq2 _ accD ->
        subst
          (λ J -> Computable n J)
          (sym
            (cong₃ (termEq [])
              (cong (λ rho -> subTm tau₁ (subTm rho t)) (liftSubstCompKeep sigma)
                ∙ subTmComp tau₁ (liftSubst sigma) t)
              (cong (λ rho -> subTm tau₂ (subTm rho u)) (liftSubstCompKeep sigma)
                ∙ subTmComp tau₂ (liftSubst sigma) u)
              (cong (λ rho -> subTy tau₁ (subTy rho T)) (liftSubstCompKeep sigma)
                ∙ subTyComp tau₁ (liftSubst sigma) T)))
          (eqSubEqRec
            dtu
            (composeOneBinderEq fits dAσ fitsEq2)
            (fitsEqToCompFitsEqCb (composeOneBinderEq fits dAσ fitsEq2))
            (access accD _ (lift-lex-eq {d₁ = dtu} {d₂ = substTmEqRule dtu (liftFitsOne fits dAσ)}
              (sym (tyDepth-subTy (consSubst (var zero) (compSub (keepSubstBy 1) sigma)) T))
              (substMeasure-substTmEqRule< dtu (liftFitsOne fits dAσ)))))))

-- openHypTm2: 2-binder version of openHypTm1. Same callbacks.
openHypTm2
  : (substRec : SubRecTy)
  -> (eqSubRec : EqSubRecTy)
  -> (composeCompFitsCb : ComposeCompFitsTy)
  -> (fitsEqToCompFitsEqCb : FitsEqToCompFitsEqTy)
  -> {n : ℕ} -> {gamma : Ctx} {A B T : RawType} {t : RawTerm} {sigma : Subst}
  -> (fits : FitsSubst [] gamma sigma)
  -> ComputableFits n fits
  -> Derivable (isType [] (subTy sigma A))
  -> Derivable (isType (subTy sigma A ∷ []) (subTy (liftSubst sigma) B))
  -> HypComputable (suc n)
       (isType (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ [])
         (subTy (liftSubst (liftSubst sigma)) T))
  -> (dt : Derivable (hasTy (B ∷ A ∷ gamma) t T))
  -> Acc LexLt (substTaskLexMeasure dt)
  -> HypComputable (suc n)
       (hasTy (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ [])
         (subTm (liftSubst (liftSubst sigma)) t)
         (subTy (liftSubst (liftSubst sigma)) T))
openHypTm2 substRec eqSubRec composeCompFitsCb fitsEqToCompFitsEqCb
  {n} {gamma = gamma} {A = A} {B = B} {T = T} {t = t} {sigma = sigma}
  fits cFits dAσ dBσ compT dt accDt =
  let
    lifted1 : FitsSubst (subTy sigma A ∷ []) (A ∷ gamma) (liftSubst sigma)
    lifted1 =
      subst
        (λ rho -> FitsSubst (subTy sigma A ∷ []) (A ∷ gamma) rho)
        (liftSubstCompKeep sigma)
        (liftFitsOne fits dAσ)
  in
  subst
    (λ J -> HypComputable (suc n) J)
    (cong₂
      (hasTy (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []))
      (cong (λ rho -> subTm rho t) (liftSubstCompKeep (liftSubst sigma)))
      (cong (λ rho -> subTy rho T) (liftSubstCompKeep (liftSubst sigma))))
    (hypTmOpen
      nonemptyNeNil
      (substTmRule dt (liftFits lifted1 dBσ))
      (subst
        (λ J -> HypComputable (suc n) J)
        (sym
          (cong
            (λ rho ->
              isType (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ [])
                (subTy rho T))
            (liftSubstCompKeep (liftSubst sigma))))
        compT)
      -- Phase F.3: destructure closure Acc, use accRs _ proof< for recursion on dt
      (λ tau fits2 cFits2 accD ->
        let
          composedFits =
            subst
              (λ rho -> FitsSubst [] (B ∷ A ∷ gamma) rho)
              (cong (compSub tau) (liftSubstCompKeep (liftSubst sigma)))
              (composeFits fits2 (liftFits lifted1 dBσ))
          composedCFits =
            substCompFits
              (cong (compSub tau) (liftSubstCompKeep (liftSubst sigma)))
              (composeCompFitsCb
                fits2
                cFits2
                (liftFits lifted1 dBσ)
                (iTop (fitsSubstCtxWF (liftFits lifted1 dBσ)))
                (LexLt-wf _))
        in
        subst
          (λ J -> Computable n J)
          (sym
            (cong₂ (hasTy [])
              (cong (λ rho -> subTm tau (subTm rho t)) (liftSubstCompKeep (liftSubst sigma))
                ∙ subTmComp tau (liftSubst (liftSubst sigma)) t)
              (cong (λ rho -> subTy tau (subTy rho T)) (liftSubstCompKeep (liftSubst sigma))
                ∙ subTyComp tau (liftSubst (liftSubst sigma)) T)))
          (substRec dt composedFits composedCFits
            (access accD _ (lift-lex-eq {d₁ = dt} {d₂ = substTmRule dt (liftFits lifted1 dBσ)}
              (sym (tyDepth-subTy (consSubst (var zero) (compSub (keepSubstBy 1) (liftSubst sigma))) T))
              (substMeasure-substTmRule< dt (liftFits lifted1 dBσ))))))
      (λ tau₁ tau₂ fitsEq2 _ accD ->
        subst
          (λ J -> Computable n J)
          (sym
            (cong₃ (termEq [])
              (cong (λ rho -> subTm tau₁ (subTm rho t)) (liftSubstCompKeep (liftSubst sigma))
                ∙ subTmComp tau₁ (liftSubst (liftSubst sigma)) t)
              (cong (λ rho -> subTm tau₂ (subTm rho t)) (liftSubstCompKeep (liftSubst sigma))
                ∙ subTmComp tau₂ (liftSubst (liftSubst sigma)) t)
              (cong (λ rho -> subTy tau₁ (subTy rho T)) (liftSubstCompKeep (liftSubst sigma))
                ∙ subTyComp tau₁ (liftSubst (liftSubst sigma)) T)))
          (eqSubRec
            dt
            (composeTwoBindersEq fits dAσ dBσ fitsEq2)
            (fitsEqToCompFitsEqCb (composeTwoBindersEq fits dAσ dBσ fitsEq2))
            (access accD _ (lift-lex-eq {d₁ = dt} {d₂ = substTmRule dt (liftFits lifted1 dBσ)}
              (sym (tyDepth-subTy (consSubst (var zero) (compSub (keepSubstBy 1) (liftSubst sigma))) T))
              (substMeasure-substTmRule< dt (liftFits lifted1 dBσ)))))))
