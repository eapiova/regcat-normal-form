{-# OPTIONS --safe #-}
-- Phase F.5 Stage 2: parameterized openHypTm* helpers.
--
-- These were originally in CompTheorem.agda's main mutual block. They
-- mutually-recurse with substDerivTm[Eq]CompCF and eqSubDerivTm[Eq]CompCF
-- via stored hypTmOpen / hypTmEqOpen closure bodies. To extract them
-- into a separate file, we parameterize the helpers over an SCC2Callbacks
-- record that bundles the recursive callbacks from the main mutual block.
--
-- Currently extracted: openHypTm1, openHypTmEq1, openHypTm2, openHypTmEq2,
-- compEQtrClosed, compESigmaClosed. The openHypTm* helpers are parameterized
-- over SCC2Callbacks; the closed eliminator helpers take precomputed
-- branch/coherence Computable values instead of calling callbacks internally.
-- See ~/.claude/plans/sharded-prancing-forest.md.

module TReg.OpenHyp where

open import TReg.Prelude
open import Data.Empty as Empty using (⊥) renaming (⊥-elim to rec)
open import Data.Nat using (ℕ ; zero ; suc)
open import Data.List.Base using ([] ; _∷_ ; length)
open import Induction.WellFounded using (Acc ; acc) renaming (acc-inverse to access)

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
ComposeCompFitsTy = ∀ {n} {gamma delta : Ctx} {rho sigma : Subst}
  -> (outer : FitsSubst [] gamma rho)
  -> ComputableFits n outer
  -> (inner : FitsSubst gamma delta sigma)
  -> Acc LexLt (fitsSubstLexMeasure inner)
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

record SCC2Callbacks : Type where
  constructor mkSCC2Callbacks
  field
    cbSubTm : SubRecTy
    cbEqSubTm : EqSubRecTy
    cbComposeCompFits : ComposeCompFitsTy
    cbFitsEqToCompFitsEq : FitsEqToCompFitsEqTy
    cbFitsToCompFits : FitsToCompFitsTy
    cbSubTmEq : SubEqRecTy
    cbEqSubTmEq : EqSubEqRecTy

open SCC2Callbacks

SigmaClosedBranchEq : {n : ℕ} -> {A B M : RawType} {d d' m m' : RawTerm}
  -> Computable n (termEq [] d d' (tySigma A B))
  -> Type
SigmaClosedBranchEq {n} {M = M} {m = m} {m' = m'} compdd' =
  let
    open ClosedSigmaTmEqInv (invertSigmaTmEq compdd' evalSigma)
  in
  Computable n
    (termEq []
      (subTm (sigmaCompSub sigmaTmEqLeftFst sigmaTmEqLeftSnd) m)
      (subTm (sigmaCompSub sigmaTmEqRightFst sigmaTmEqRightSnd) m')
      (subTy (singleSubst (tmPair sigmaTmEqLeftFst sigmaTmEqLeftSnd)) M))

QtrClosedBranchEq : {n : ℕ} -> {A L : RawType} {l l' p p' : RawTerm}
  -> Computable n (termEq [] p p' (tyQtr A))
  -> Type
QtrClosedBranchEq {n} {L = L} {l = l} {l' = l'} comppp' =
  let
    open ClosedQtrTmEqInv (invertQtrTmEq comppp' evalQtr)
  in
  Computable n
    (termEq []
      (subTm (qtrCompSub qtrTmEqLeftRepr) l)
      (subTm (qtrCompSub qtrTmEqLeftRepr) l')
      (subTy (singleSubst (tmClass qtrTmEqLeftRepr)) L))

QtrClosedCohEq : {n : ℕ} -> {A L : RawType} {l l' p p' : RawTerm}
  -> Computable n (termEq [] p p' (tyQtr A))
  -> Type
QtrClosedCohEq {n} {L = L} {l' = l'} comppp' =
  let
    open ClosedQtrTmEqInv (invertQtrTmEq comppp' evalQtr)
  in
  Computable n
    (termEq []
      (subTm (qtrCompSub qtrTmEqLeftRepr) l')
      (subTm (qtrCompSub qtrTmEqRightRepr) l')
      (subTy (singleSubst (tmClass qtrTmEqLeftRepr)) L))

-- openHypTm1: parameterized over the SCC2 callback record.
openHypTm1
  : SCC2Callbacks
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
openHypTm1 cb
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
              (cbComposeCompFits cb
                fits2
                cFits2
                (liftFitsOne fits dAσ)
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
          (cbSubTm cb dt composedFits composedCFits
            (access accD (lift-lex-eq {d₁ = dt} {d₂ = substTmRule dt (liftFitsOne fits dAσ)}
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
          (cbEqSubTm cb
            dt
            (composeOneBinderEq fits dAσ fitsEq2)
            (cbFitsEqToCompFitsEq cb (composeOneBinderEq fits dAσ fitsEq2))
            (access accD (lift-lex-eq {d₁ = dt} {d₂ = substTmRule dt (liftFitsOne fits dAσ)}
              (sym (tyDepth-subTy (consSubst (var zero) (compSub (keepSubstBy 1) sigma)) T))
              (substMeasure-substTmRule< dt (liftFitsOne fits dAσ)))))))

-- openHypTmEq1: parameterized over the SCC2 callback record.
openHypTmEq1
  : SCC2Callbacks
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
openHypTmEq1 cb
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
          (cbSubTmEq cb
            dtu
            (composeOneBinder fits dAσ fits2)
            (cbFitsToCompFits cb (composeOneBinder fits dAσ fits2))
            (access accD (lift-lex-eq {d₁ = dtu} {d₂ = substTmEqRule dtu (liftFitsOne fits dAσ)}
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
          (cbEqSubTmEq cb
            dtu
            (composeOneBinderEq fits dAσ fitsEq2)
            (cbFitsEqToCompFitsEq cb (composeOneBinderEq fits dAσ fitsEq2))
            (access accD (lift-lex-eq {d₁ = dtu} {d₂ = substTmEqRule dtu (liftFitsOne fits dAσ)}
              (sym (tyDepth-subTy (consSubst (var zero) (compSub (keepSubstBy 1) sigma)) T))
              (substMeasure-substTmEqRule< dtu (liftFitsOne fits dAσ)))))))

-- openHypTm2: 2-binder version of openHypTm1. Same callbacks.
openHypTm2
  : SCC2Callbacks
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
openHypTm2 cb
  {n} {gamma = gamma} {A = A} {B = B} {T = T} {t = t} {sigma = sigma}
  fits cFits dAσ dBσ compT dt accDt =
  let
    lifted1 : FitsSubst (subTy sigma A ∷ []) (A ∷ gamma) (liftSubst sigma)
    lifted1 =
      subst
        (λ rho -> FitsSubst (subTy sigma A ∷ []) (A ∷ gamma) rho)
        (liftSubstCompKeep sigma)
        (liftFitsOne fits dAσ)

    lifted2Keep : FitsSubst
      (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ [])
      (B ∷ A ∷ gamma)
      (consSubst (var zero) (compSub (keepSubstBy 1) (liftSubst sigma)))
    lifted2Keep =
      subst
        (λ rho ->
          FitsSubst
            (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ [])
            (B ∷ A ∷ gamma)
            rho)
        (cong (consSubst (var zero)) (keepSubstCtx1LiftCompFor (subTy sigma A) sigma))
        (liftFits lifted1 dBσ)
  in
  subst
    (λ J -> HypComputable (suc n) J)
    (cong₂
      (hasTy (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []))
      (cong (λ rho -> subTm rho t) (liftSubstCompKeep (liftSubst sigma)))
      (cong (λ rho -> subTy rho T) (liftSubstCompKeep (liftSubst sigma))))
    (hypTmOpen
      nonemptyNeNil
      (substTmRule dt lifted2Keep)
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
              (composeFits fits2 lifted2Keep)
          composedCFits =
            substCompFits
              (cong (compSub tau) (liftSubstCompKeep (liftSubst sigma)))
              (cbComposeCompFits cb
                fits2
                cFits2
                lifted2Keep
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
          (cbSubTm cb dt composedFits composedCFits
            (access accD (lift-lex-eq {d₁ = dt} {d₂ = substTmRule dt lifted2Keep}
              (sym (tyDepth-subTy (consSubst (var zero) (compSub (keepSubstBy 1) (liftSubst sigma))) T))
              (substMeasure-substTmRule< dt lifted2Keep)))))
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
          (cbEqSubTm cb
            dt
            (composeTwoBindersEq fits dAσ dBσ fitsEq2)
            (cbFitsEqToCompFitsEq cb (composeTwoBindersEq fits dAσ dBσ fitsEq2))
            (access accD (lift-lex-eq {d₁ = dt} {d₂ = substTmRule dt lifted2Keep}
              (sym (tyDepth-subTy (consSubst (var zero) (compSub (keepSubstBy 1) (liftSubst sigma))) T))
              (substMeasure-substTmRule< dt lifted2Keep))))))

-- openHypTmEq2: 2-binder version of openHypTmEq1. Same callbacks.
openHypTmEq2
  : SCC2Callbacks
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
openHypTmEq2 cb
  {n} {gamma = gamma} {A = A} {B = B} {T = T} {t = t} {u = u} {sigma = sigma}
  fits dAσ dBσ compt dtu accDtu =
  let
    lifted1 : FitsSubst (subTy sigma A ∷ []) (A ∷ gamma) (liftSubst sigma)
    lifted1 =
      subst
        (λ rho -> FitsSubst (subTy sigma A ∷ []) (A ∷ gamma) rho)
        (liftSubstCompKeep sigma)
        (liftFitsOne fits dAσ)

    lifted2Keep : FitsSubst
      (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ [])
      (B ∷ A ∷ gamma)
      (consSubst (var zero) (compSub (keepSubstBy 1) (liftSubst sigma)))
    lifted2Keep =
      subst
        (λ rho ->
          FitsSubst
            (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ [])
            (B ∷ A ∷ gamma)
            rho)
        (cong (consSubst (var zero)) (keepSubstCtx1LiftCompFor (subTy sigma A) sigma))
        (liftFits lifted1 dBσ)
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
      (substTmEqRule dtu lifted2Keep)
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
          (cbSubTmEq cb
            dtu
            (composeTwoBinders fits dAσ dBσ fits2)
            (cbFitsToCompFits cb (composeTwoBinders fits dAσ dBσ fits2))
            (access accD (lift-lex-eq {d₁ = dtu} {d₂ = substTmEqRule dtu lifted2Keep}
              (sym (tyDepth-subTy (consSubst (var zero) (compSub (keepSubstBy 1) (liftSubst sigma))) T))
              (substMeasure-substTmEqRule< dtu lifted2Keep)))))
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
          (cbEqSubTmEq cb
            dtu
            (composeTwoBindersEq fits dAσ dBσ fitsEq2)
            (cbFitsEqToCompFitsEq cb (composeTwoBindersEq fits dAσ dBσ fitsEq2))
            (access accD (lift-lex-eq {d₁ = dtu} {d₂ = substTmEqRule dtu lifted2Keep}
              (sym (tyDepth-subTy (consSubst (var zero) (compSub (keepSubstBy 1) (liftSubst sigma))) T))
              (substMeasure-substTmEqRule< dtu lifted2Keep))))))
compEQtrClosed
  : {n : ℕ} -> {A L : RawType} {l l' p p' : RawTerm}
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
  -> (comppp' : Computable n (termEq [] p p' (tyQtr A)))
  -> (dll' : Derivable (termEq (A ∷ []) l l' (qtrBranchTy L)))
  -> QtrClosedBranchEq {L = L} {l = l} {l' = l'} {p = p} {p' = p'} comppp'
  -> (dcoh : Derivable
       (termEq (wkTyBy 1 A ∷ A ∷ []) (wkTmBy 1 l) (renTm qtrSecondBranchRen l) (qtrCohTy L)))
  -> (dcoh' : Derivable
       (termEq (wkTyBy 1 A ∷ A ∷ []) (wkTmBy 1 l') (renTm qtrSecondBranchRen l') (qtrCohTy L)))
  -> QtrClosedCohEq {L = L} {l = l} {l' = l'} {p = p} {p' = p'} comppp'
  -> Computable n
       (termEq [] (tmElQtr l p) (tmElQtr l' p') (subTy (singleSubst p) L))
compEQtrClosed {n} {A = A} {L = L} {l = l} {l' = l'} {p = p} {p' = p'}
  transCl symCl convEqCl compL comppp' dll' branchEqClassA dcoh dcoh' cohEqClassA =
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
compESigmaClosed
  : {n : ℕ} -> {A B M : RawType} {d d' m m' : RawTerm}
  -> ({t u v : RawTerm} {T : RawType}
       -> Computable n (termEq [] t u T)
       -> Computable n (termEq [] u v T)
       -> Computable n (termEq [] t v T))
  -> ({t u : RawTerm} {T U : RawType}
       -> Computable n (termEq [] t u T)
       -> Computable n (typeEq [] T U)
       -> Computable n (termEq [] t u U))
  -> HypComputable (suc n) (isType ((tySigma A B) ∷ []) M)
  -> (compdd' : Computable n (termEq [] d d' (tySigma A B)))
  -> (dmm' : Derivable (termEq (B ∷ A ∷ []) m m' (sigmaBranchTy M)))
  -> SigmaClosedBranchEq {M = M} {d = d} {d' = d'} {m = m} {m' = m'} compdd'
  -> Computable n
       (termEq [] (tmElSigma d m) (tmElSigma d' m') (subTy (singleSubst d) M))
compESigmaClosed {n} {A = A} {B = B} {M = M} {d = d} {d' = d'} {m = m} {m' = m'}
  transCl convEqCl compM compdd' dmm' branchEqPair =
  transCl leftCan (transCl bodyEqD rightCanSym)
  where
  open ClosedSigmaTmEqInv (invertSigmaTmEq compdd' evalSigma)

  compSigma : Computable n (isType [] (tySigma A B))
  compSigma = compTmToCompTy sigmaTmEqCompLeft

  compPairLeft : Computable n (hasTy [] (tmPair sigmaTmEqLeftFst sigmaTmEqLeftSnd) (tySigma A B))
  compPairLeft =
    compISigmaClosed sigmaTmEqLeftCompFstTy sigmaTmEqLeftCompSndTy compSigma

  compPairRight : Computable n (hasTy [] (tmPair sigmaTmEqRightFst sigmaTmEqRightSnd) (tySigma A B))
  compPairRight =
    compISigmaClosed sigmaTmEqRightCompFstTy sigmaTmEqRightCompSndTy compSigma

  compLeftCorr : Computable n
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

  compLeftCorrSym : Computable n
    (termEq [] (tmPair sigmaTmEqLeftFst sigmaTmEqLeftSnd) d (tySigma A B))
  compLeftCorrSym =
    compTmEqClosedSigma
      (symTm
        sigmaTmEqLeftCorrPair
        (compToDerivable compPairLeft)
        (compToDerivable (compTmToCompTy compPairLeft)))
      compPairLeft
      sigmaTmEqCompLeft
      evalSigma
      evalPair
      sigmaTmEqEvalLeftPair
      (compReflTmClosed sigmaTmEqLeftCompFstTy)
      (compReflTmClosed sigmaTmEqLeftCompSndTy)

  compRightCorr : Computable n
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

  bodyEqD : Computable n
    (termEq []
      (subTm (sigmaCompSub sigmaTmEqLeftFst sigmaTmEqLeftSnd) m)
      (subTm (sigmaCompSub sigmaTmEqRightFst sigmaTmEqRightSnd) m')
      (subTy (singleSubst d) M))
  bodyEqD =
    convEqCl
      branchEqPair
      (compSingleEqSubstTyClosed compM compLeftCorrSym (LexLt-wf _))

  bodyLeft : Computable n
    (hasTy []
      (subTm (sigmaCompSub sigmaTmEqLeftFst sigmaTmEqLeftSnd) m)
      (subTy (singleSubst d) M))
  bodyLeft = compTmEqLeft bodyEqD

  bodyRight : Computable n
    (hasTy []
      (subTm (sigmaCompSub sigmaTmEqRightFst sigmaTmEqRightSnd) m')
      (subTy (singleSubst d) M))
  bodyRight = compTmEqRightClosed bodyEqD

  dM : Derivable (isType ((tySigma A B) ∷ []) M)
  dM = hypCompToDerivable compM

  dm : Derivable (hasTy (B ∷ A ∷ []) m (sigmaBranchTy M))
  dm = assocTmLeft dmm'

  dm' : Derivable (hasTy (B ∷ A ∷ []) m' (sigmaBranchTy M))
  dm' = assocTmRight dmm'

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
  dLeftStep = eSigmaEq dM sigmaTmEqLeftCorrPair dm (reflTm dm)

  dLeftCanon : Derivable
    (termEq []
      (tmElSigma (tmPair sigmaTmEqLeftFst sigmaTmEqLeftSnd) m)
      (subTm (sigmaCompSub sigmaTmEqLeftFst sigmaTmEqLeftSnd) m)
      (subTy (singleSubst d) M))
  dLeftCanon =
    convEq
      (cSigma dM (compToDerivable compSigma) db dc dm)
      (symTy
        (singleEqSubstTyHelper dM (compToDerivable compLeftCorr))
        (singleSubstTyHelper dM (compToDerivable (compTmEqRightClosed compLeftCorr))))

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
      (eSigmaEq dM sigmaTmEqRightCorrPair dm' (reflTm dm'))
      (convEq
        (cSigma dM (compToDerivable compSigma) de df dm')
        (symTy
          (singleEqSubstTyHelper dM (compToDerivable compRightCorr))
          (singleSubstTyHelper dM (compToDerivable (compTmEqRightClosed compRightCorr)))))

  dRightEq : Derivable
    (termEq []
      (tmElSigma d' m')
      (subTm (sigmaCompSub sigmaTmEqRightFst sigmaTmEqRightSnd) m')
      (subTy (singleSubst d) M))
  dRightEq =
    convEq
      dRightCanon0
      (symTy
        (singleEqSubstTyHelper dM (compToDerivable compdd'))
        (singleSubstTyHelper dM (compToDerivable (compTmEqRightClosed compdd'))))

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
    -> Computable n
         (hasTy []
           (subTm (sigmaCompSub sigmaTmEqLeftFst sigmaTmEqLeftSnd) m)
           (subTy (singleSubst d) M))
    -> Computable n
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
    -> Computable n
         (hasTy []
           (subTm (sigmaCompSub sigmaTmEqRightFst sigmaTmEqRightSnd) m')
           (subTy (singleSubst d) M))
    -> Computable n
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
    -> Computable n
         (hasTy []
           (subTm (sigmaCompSub sigmaTmEqRightFst sigmaTmEqRightSnd) m')
           (subTy (singleSubst d) M))
    -> Computable n
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
      (symTm dEq (compToDerivable body) (compToDerivable compTy))
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
      (symTm dEq (compToDerivable body) (compToDerivable compTy))
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
      (symTm dEq (compToDerivable body) (compToDerivable compTy))
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
      (symTm dEq (compToDerivable body) (compToDerivable compTy))
      body
      lhsComp
      evTy
      evRhs
      (evalElSigma evd evRhs)
      compa
      compa

  leftCan : Computable n
    (termEq []
      (tmElSigma d m)
      (subTm (sigmaCompSub sigmaTmEqLeftFst sigmaTmEqLeftSnd) m)
      (subTy (singleSubst d) M))
  leftCan = mkLeftCanon dLeftEq dLeftTy sigmaTmEqEvalLeftPair bodyLeft

  rightCan : Computable n
    (termEq []
      (tmElSigma d' m')
      (subTm (sigmaCompSub sigmaTmEqRightFst sigmaTmEqRightSnd) m')
      (subTy (singleSubst d) M))
  rightCan = mkRightCanon dRightEq dRightTy sigmaTmEqEvalRightPair bodyRight

  rightCanSym : Computable n
    (termEq []
      (subTm (sigmaCompSub sigmaTmEqRightFst sigmaTmEqRightSnd) m')
      (tmElSigma d' m')
      (subTy (singleSubst d) M))
  rightCanSym = mkRightCanonSym dRightEq dRightTy sigmaTmEqEvalRightPair bodyRight
