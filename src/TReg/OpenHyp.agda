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
open import TReg.Inversion
open import TReg.StructuralBase using (composeFits)
open import TReg.Structural
open import TReg.Presupposition
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

-- openHypTmEq2: 2-binder version of openHypTmEq1. Same callbacks.
openHypTmEq2
  : (substEqRec : SubEqRecTy)
  -> (eqSubEqRec : EqSubEqRecTy)
  -> (fitsToCompFitsCb : FitsToCompFitsTy)
  -> (fitsEqToCompFitsEqCb : FitsEqToCompFitsEqTy)
  -> {n : ℕ} -> {gamma : Ctx} {A B T : RawType} {t u : RawTerm} {sigma : Subst}
  -> FitsSubst [] gamma sigma
  -> Derivable (isType [] (subTy sigma A))
  -> Derivable (isType (subTy sigma A ∷ []) (subTy (liftSubst sigma) B))
  -> HypComputable (suc n)
       (hasTy (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ [])
         (subTm (liftSubst (liftSubst sigma)) t)
         (subTy (liftSubst (liftSubst sigma)) T))
  -> (dtu : Derivable (termEq (B ∷ A ∷ gamma) t u T))
  -> Acc LexLt (substTaskLexMeasure dtu)
  -> HypComputable (suc n)
       (termEq (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ [])
         (subTm (liftSubst (liftSubst sigma)) t)
         (subTm (liftSubst (liftSubst sigma)) u)
         (subTy (liftSubst (liftSubst sigma)) T))
openHypTmEq2 substEqRec eqSubEqRec fitsToCompFitsCb fitsEqToCompFitsEqCb
  {n} {gamma = gamma} {A = A} {B = B} {T = T} {t = t} {u = u} {sigma = sigma}
  fits dAσ dBσ compt dtu accDtu =
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
    (cong₃
      (termEq (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []))
      (cong (λ rho -> subTm rho t) (liftSubstCompKeep (liftSubst sigma)))
      (cong (λ rho -> subTm rho u) (liftSubstCompKeep (liftSubst sigma)))
      (cong (λ rho -> subTy rho T) (liftSubstCompKeep (liftSubst sigma))))
    (hypTmEqOpen
      nonemptyNeNil
      (substTmEqRule dtu (liftFits lifted1 dBσ))
      (subst
        (λ J -> HypComputable (suc n) J)
        (sym
          (cong₂
            (hasTy (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []))
            (cong (λ rho -> subTm rho t) (liftSubstCompKeep (liftSubst sigma)))
            (cong (λ rho -> subTy rho T) (liftSubstCompKeep (liftSubst sigma)))))
        compt)
      -- Phase F.3: destructure closure Acc, use accRs _ proof< for recursion on dtu
      (λ tau fits2 _ accD ->
        subst
          (λ J -> Computable n J)
          (sym
            (cong₃ (termEq [])
              (cong (λ rho -> subTm tau (subTm rho t)) (liftSubstCompKeep (liftSubst sigma))
                ∙ subTmComp tau (liftSubst (liftSubst sigma)) t)
              (cong (λ rho -> subTm tau (subTm rho u)) (liftSubstCompKeep (liftSubst sigma))
                ∙ subTmComp tau (liftSubst (liftSubst sigma)) u)
              (cong (λ rho -> subTy tau (subTy rho T)) (liftSubstCompKeep (liftSubst sigma))
                ∙ subTyComp tau (liftSubst (liftSubst sigma)) T)))
          (substEqRec
            dtu
            (composeTwoBinders fits dAσ dBσ fits2)
            (fitsToCompFitsCb (composeTwoBinders fits dAσ dBσ fits2))
            (access accD _ (lift-lex-eq {d₁ = dtu} {d₂ = substTmEqRule dtu (liftFits lifted1 dBσ)}
              (sym (tyDepth-subTy (consSubst (var zero) (compSub (keepSubstBy 1) (liftSubst sigma))) T))
              (substMeasure-substTmEqRule< dtu (liftFits lifted1 dBσ))))))
      (λ tau₁ tau₂ fitsEq2 _ accD ->
        subst
          (λ J -> Computable n J)
          (sym
            (cong₃ (termEq [])
              (cong (λ rho -> subTm tau₁ (subTm rho t)) (liftSubstCompKeep (liftSubst sigma))
                ∙ subTmComp tau₁ (liftSubst (liftSubst sigma)) t)
              (cong (λ rho -> subTm tau₂ (subTm rho u)) (liftSubstCompKeep (liftSubst sigma))
                ∙ subTmComp tau₂ (liftSubst (liftSubst sigma)) u)
              (cong (λ rho -> subTy tau₁ (subTy rho T)) (liftSubstCompKeep (liftSubst sigma))
                ∙ subTyComp tau₁ (liftSubst (liftSubst sigma)) T)))
          (eqSubEqRec
            dtu
            (composeTwoBindersEq fits dAσ dBσ fitsEq2)
            (fitsEqToCompFitsEqCb (composeTwoBindersEq fits dAσ dBσ fitsEq2))
            (access accD _ (lift-lex-eq {d₁ = dtu} {d₂ = substTmEqRule dtu (liftFits lifted1 dBσ)}
              (sym (tyDepth-subTy (consSubst (var zero) (compSub (keepSubstBy 1) (liftSubst sigma))) T))
              (substMeasure-substTmEqRule< dtu (liftFits lifted1 dBσ)))))))
compEQtrClosed : (substEqRec : SubEqRecTy)
  -> {n : ℕ} -> {A L : RawType} {l l' p p' : RawTerm}
  -> ({t u v : RawTerm} {T : RawType}
       -> Computable n (termEq [] t u T)
       -> Computable n (termEq [] u v T)
       -> Computable n (termEq [] t v T))
  -> ({t u : RawTerm} {T : RawType}
       -> Computable n (termEq [] t u T)
       -> Computable n (termEq [] u t T))
  -> ({t u : RawTerm} {T U : RawType}
       -> Computable n (termEq [] t u T)
       -> Computable n (typeEq [] T U)
       -> Computable n (termEq [] t u U))
  -> HypComputable (suc n) (isType ((tyQtr A) ∷ []) L)
  -> Computable n (termEq [] p p' (tyQtr A))
  -> (dll' : Derivable (termEq (A ∷ []) l l' (qtrBranchTy L)))
  -> Acc LexLt (substTaskLexMeasure dll')
  -> (dcoh : Derivable
       (termEq (wkTyBy 1 A ∷ A ∷ []) (wkTmBy 1 l) (renTm qtrSecondBranchRen l) (qtrCohTy L)))
  -> (dcoh' : Derivable
       (termEq (wkTyBy 1 A ∷ A ∷ []) (wkTmBy 1 l') (renTm qtrSecondBranchRen l') (qtrCohTy L)))
  -> Acc LexLt (substTaskLexMeasure dcoh')
  -> Computable n
       (termEq [] (tmElQtr l p) (tmElQtr l' p') (subTy (singleSubst p) L))
compEQtrClosed substEqRec {n} {A = A} {L = L} {l = l} {l' = l'} {p = p} {p' = p'}
  transCl symCl convEqCl compL comppp' dll' accDll' dcoh dcoh' accDcoh' =
  transCl leftCan (transCl bodyEqP (symCl rightCan))
  where
  open ClosedQtrTmEqInv (invertQtrTmEq comppp' evalQtr)

  compQtr : Computable n (isType [] (tyQtr A))
  compQtr = compTmToCompTy qtrTmEqCompLeft

  compClassLeft : Computable n (hasTy [] (tmClass qtrTmEqLeftRepr) (tyQtr A))
  compClassLeft = compIQtrClosed qtrTmEqCompLeftRepr

  compClassRight : Computable n (hasTy [] (tmClass qtrTmEqRightRepr) (tyQtr A))
  compClassRight = compIQtrClosed qtrTmEqCompRightRepr

  compLeftCorr : Computable n
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

  compRightCorr : Computable n
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

  dBranch : Derivable (isType (A ∷ []) (qtrBranchTy L))
  dBranch = assocTmTy dll'

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

  compbOnHead : Computable n
    (hasTy [] qtrTmEqRightRepr (subTy (qtrCompSub qtrTmEqLeftRepr) (wkTyBy 1 A)))
  compbOnHead =
    subst
      (λ T -> Computable n (hasTy [] qtrTmEqRightRepr T))
      dHeadTyPath
      qtrTmEqCompRightRepr

  branchFitsLeft : CompFitsBundle n (A ∷ []) (qtrCompSub qtrTmEqLeftRepr)
  branchFitsLeft = qtrCompComputableFitsHelper qtrTmEqCompLeftRepr

  branchEqClassA : Computable n
    (termEq []
      (subTm (qtrCompSub qtrTmEqLeftRepr) l)
      (subTm (qtrCompSub qtrTmEqLeftRepr) l')
      (subTy (singleSubst (tmClass qtrTmEqLeftRepr)) L))
  branchEqClassA =
    subst
      (λ T ->
        Computable n
          (termEq []
            (subTm (qtrCompSub qtrTmEqLeftRepr) l)
            (subTm (qtrCompSub qtrTmEqLeftRepr) l')
            T))
      (qtrBranchTyComp qtrTmEqLeftRepr L)
      (substEqRec dll' (fst branchFitsLeft) (snd branchFitsLeft) accDll')

  cohFitsRight : FitsSubst [] (wkTyBy 1 A ∷ A ∷ [])
    (consSubst qtrTmEqRightRepr (consSubst qtrTmEqLeftRepr idSubst))
  cohFitsRight =
    fitsCons
      (fst (qtrCompComputableFitsHelper qtrTmEqCompLeftRepr))
      dbOnHead

  cohFitsRightComp : ComputableFits n cohFitsRight
  cohFitsRightComp =
    compFitsCons
      (snd (qtrCompComputableFitsHelper qtrTmEqCompLeftRepr))
      compbOnHead

  cohEqClassA : Computable n
    (termEq []
      (subTm (qtrCompSub qtrTmEqLeftRepr) l')
      (subTm (qtrCompSub qtrTmEqRightRepr) l')
      (subTy (singleSubst (tmClass qtrTmEqLeftRepr)) L))
  cohEqClassA =
    subst
      (λ t ->
        Computable n
          (termEq []
            t
            (subTm (qtrCompSub qtrTmEqRightRepr) l')
            (subTy (singleSubst (tmClass qtrTmEqLeftRepr)) L)))
      (qtrCohLeftTmComp qtrTmEqLeftRepr qtrTmEqRightRepr l')
      (subst
        (λ u ->
          Computable n
            (termEq []
              (subTm (consSubst qtrTmEqRightRepr (consSubst qtrTmEqLeftRepr idSubst))
                (wkTmBy 1 l'))
              u
              (subTy (singleSubst (tmClass qtrTmEqLeftRepr)) L)))
        (qtrCohRightTmComp qtrTmEqLeftRepr qtrTmEqRightRepr l')
        (subst
          (λ T ->
            Computable n
              (termEq []
                (subTm (consSubst qtrTmEqRightRepr (consSubst qtrTmEqLeftRepr idSubst))
                  (wkTmBy 1 l'))
                (subTm (consSubst qtrTmEqRightRepr (consSubst qtrTmEqLeftRepr idSubst))
                  (renTm qtrSecondBranchRen l'))
                T))
          (qtrCohTyComp qtrTmEqLeftRepr qtrTmEqRightRepr L)
          (substEqRec dcoh' cohFitsRight cohFitsRightComp accDcoh')))

  bodyEqClassA : Computable n
    (termEq []
      (subTm (qtrCompSub qtrTmEqLeftRepr) l)
      (subTm (qtrCompSub qtrTmEqRightRepr) l')
      (subTy (singleSubst (tmClass qtrTmEqLeftRepr)) L))
  bodyEqClassA = transCl branchEqClassA cohEqClassA

  bodyEqP : Computable n
    (termEq []
      (subTm (qtrCompSub qtrTmEqLeftRepr) l)
      (subTm (qtrCompSub qtrTmEqRightRepr) l')
      (subTy (singleSubst p) L))
  bodyEqP =
    convEqCl
      bodyEqClassA
      (compSingleEqSubstTyClosed compL (symCl compLeftCorr) (LexLt-wf _))

  bodyLeft : Computable n
    (hasTy []
      (subTm (qtrCompSub qtrTmEqLeftRepr) l)
      (subTy (singleSubst p) L))
  bodyLeft = compTmEqLeft bodyEqP

  bodyRight : Computable n
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
      dBranch
      dl
      dl
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
      (cQtr dL da dBranch dl dcoh)
      (symTy
        (singleEqSubstTyHelper dL (compToDerivable compLeftCorr))
        (singleSubstTyHelper dL (compToDerivable (compTmEqRightClosed compLeftCorr))))

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
      (eQtrEq dL (compToDerivable compRightCorr) dBranch dl' dl' (reflTm dl') dcoh' dcoh')
      (convEq
        (cQtr dL db dBranch dl' dcoh')
        (symTy
          (singleEqSubstTyHelper dL (compToDerivable compRightCorr))
          (singleSubstTyHelper dL (compToDerivable (compTmEqRightClosed compRightCorr)))))

  dRightEq : Derivable
    (termEq []
      (tmElQtr l' p')
      (subTm (qtrCompSub qtrTmEqRightRepr) l')
      (subTy (singleSubst p) L))
  dRightEq =
    convEq
      dRightCanon0
      (symTy
        (singleEqSubstTyHelper dL (compToDerivable comppp'))
        (singleSubstTyHelper dL (compToDerivable (compTmEqRightClosed comppp'))))

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
    -> Computable n
         (hasTy []
           (subTm (qtrCompSub qtrTmEqLeftRepr) l)
           (subTy (singleSubst p) L))
    -> Computable n
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
    -> Computable n
         (hasTy []
           (subTm (qtrCompSub qtrTmEqRightRepr) l')
           (subTy (singleSubst p) L))
    -> Computable n
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

  leftCan : Computable n
    (termEq []
      (tmElQtr l p)
      (subTm (qtrCompSub qtrTmEqLeftRepr) l)
      (subTy (singleSubst p) L))
  leftCan = mkLeftCanon dLeftEq dLeftTy qtrTmEqEvalLeftClass bodyLeft

  rightCan : Computable n
    (termEq []
      (tmElQtr l' p')
      (subTm (qtrCompSub qtrTmEqRightRepr) l')
      (subTy (singleSubst p) L))
  rightCan = mkRightCanon dRightEq dRightTy qtrTmEqEvalRightClass bodyRight
