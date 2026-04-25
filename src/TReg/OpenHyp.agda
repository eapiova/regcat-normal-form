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
