{-# OPTIONS #-}
-- TERMINATING is still required on the main mutual block. Remaining
-- termination issues are concentrated in 4 functions:
--   substDerivTyCompCF, substDerivTmCompCF, mkHypComputableTy,
--   sigmaTyFamHypClosed
-- These need Acc-witness propagation through mkHypComputable* closures
-- (currently they use fresh <-wellfounded instead of receiving Acc from caller).

module TReg.CompTheorem where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Empty.Base as Empty using (⊥ ; rec)
open import Cubical.Data.Sigma using (Σ ; Σ-syntax ; _×_ ; _,_ ; fst ; snd)
open import Cubical.Data.List.Base using ([] ; _∷_ ; _++_ ; length)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Nat.Order using (_<_ ; <-wellfounded)
open import Cubical.Data.Nat.Properties using (snotz)
open import Cubical.Data.Unit.Base using (Unit ; tt)
open import Cubical.Induction.WellFounded using (Acc ; acc ; access)

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
open import TReg.FitsHelpers
open import TReg.OpenHyp using (openHypTm1 ; openHypTmEq1)

{-# TERMINATING #-}
mutual
  substDerivTyCompCF : {n : ℕ} -> {gamma : Ctx} {A : RawType} {sigma : Subst}
    -> (d : Derivable (isType gamma A))
    -> (fits : FitsSubst [] gamma sigma)
    -> ComputableFits n fits
    -> Acc LexLt (substTaskLexMeasure d)
    -> Computable n (isType [] (subTy sigma A))

  substDerivTmCompCF : {n : ℕ} -> {gamma : Ctx} {t : RawTerm} {A : RawType} {sigma : Subst}
    -> (d : Derivable (hasTy gamma t A))
    -> (fits : FitsSubst [] gamma sigma)
    -> ComputableFits n fits
    -> Acc LexLt (substTaskLexMeasure d)
    -> Computable n (hasTy [] (subTm sigma t) (subTy sigma A))

  substDerivTmEqCompCF : {n : ℕ} -> {gamma : Ctx} {t u : RawTerm} {A : RawType} {sigma : Subst}
    -> (d : Derivable (termEq gamma t u A))
    -> (fits : FitsSubst [] gamma sigma)
    -> ComputableFits n fits
    -> Acc LexLt (substTaskLexMeasure d)
    -> Computable n (termEq [] (subTm sigma t) (subTm sigma u) (subTy sigma A))

  eqSubDerivTyCompCF : {n : ℕ} -> {gamma : Ctx} {A : RawType} {sigma tau : Subst}
    -> (d : Derivable (isType gamma A))
    -> (fitsEq : FitsEqSubst [] gamma sigma tau)
    -> ComputableFitsEq n fitsEq
    -> Acc LexLt (substTaskLexMeasure d)
    -> Computable n (typeEq [] (subTy sigma A) (subTy tau A))

  eqSubDerivTmCompCF : {n : ℕ} -> {gamma : Ctx} {t : RawTerm} {A : RawType} {sigma tau : Subst}
    -> (d : Derivable (hasTy gamma t A))
    -> (fitsEq : FitsEqSubst [] gamma sigma tau)
    -> ComputableFitsEq n fitsEq
    -> Acc LexLt (substTaskLexMeasure d)
    -> Computable n (termEq [] (subTm sigma t) (subTm tau t) (subTy sigma A))

  eqSubDerivTmEqCompCF : {n : ℕ} -> {gamma : Ctx} {t u : RawTerm} {A : RawType} {sigma tau : Subst}
    -> (d : Derivable (termEq gamma t u A))
    -> (fitsEq : FitsEqSubst [] gamma sigma tau)
    -> ComputableFitsEq n fitsEq
    -> Acc LexLt (substTaskLexMeasure d)
    -> Computable n (termEq [] (subTm sigma t) (subTm tau u) (subTy sigma A))

  substDerivTyEqCompCF : {n : ℕ} -> {gamma : Ctx} {A B : RawType} {sigma : Subst}
    -> (d : Derivable (typeEq gamma A B))
    -> (fits : FitsSubst [] gamma sigma)
    -> ComputableFits n fits
    -> Acc LexLt (substTaskLexMeasure d)
    -> Computable n (typeEq [] (subTy sigma A) (subTy sigma B))

  eqSubDerivTyEqCompCF : {n : ℕ} -> {gamma : Ctx} {A B : RawType} {sigma tau : Subst}
    -> (d : Derivable (typeEq gamma A B))
    -> (fitsEq : FitsEqSubst [] gamma sigma tau)
    -> ComputableFitsEq n fitsEq
    -> Acc LexLt (substTaskLexMeasure d)
    -> Computable n (typeEq [] (subTy sigma A) (subTy tau B))
  
  substDerivTmCompClosed : {n : ℕ} -> {t : RawTerm} {A : RawType}
    -> Derivable (hasTy [] t A)
    -> Computable n (hasTy [] t A)

  openHypTm2 : {n : ℕ} -> {gamma : Ctx} {A B T : RawType} {t : RawTerm} {sigma : Subst}
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
  openHypTm2 {n} {gamma = gamma} {A = A} {B = B} {T = T} {t = t} {sigma = sigma}
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
                (composeCompFits
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
            (substDerivTmCompCF dt composedFits composedCFits
              (access accD _ (lift-lex-eq (sym (tyDepth-subTy _ T))
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
            (eqSubDerivTmCompCF
              dt
              (composeTwoBindersEq fits dAσ dBσ fitsEq2)
              (fitsEqToCompFitsEq (composeTwoBindersEq fits dAσ dBσ fitsEq2))
              (access accD _ (lift-lex-eq (sym (tyDepth-subTy _ T))
                (substMeasure-substTmRule< dt (liftFits lifted1 dBσ)))))))
  
  openHypTmEq2 : {n : ℕ} -> {gamma : Ctx} {A B T : RawType} {t u : RawTerm} {sigma : Subst}
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
  openHypTmEq2 {n} {gamma = gamma} {A = A} {B = B} {T = T} {t = t} {u = u} {sigma = sigma}
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
            (substDerivTmEqCompCF
              dtu
              (composeTwoBinders fits dAσ dBσ fits2)
              (fitsToCompFits (composeTwoBinders fits dAσ dBσ fits2))
              (access accD _ (lift-lex-eq (sym (tyDepth-subTy _ T))
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
            (eqSubDerivTmEqCompCF
              dtu
              (composeTwoBindersEq fits dAσ dBσ fitsEq2)
              (fitsEqToCompFitsEq (composeTwoBindersEq fits dAσ dBσ fitsEq2))
              (access accD _ (lift-lex-eq (sym (tyDepth-subTy _ T))
                (substMeasure-substTmEqRule< dtu (liftFits lifted1 dBσ)))))))
  singleBinderComputableFits : {n : ℕ} ->    {A : RawType} {sigma : Subst}
    -> (fits : FitsSubst [] (A ∷ []) sigma)
    -> ComputableFits n fits
  singleBinderComputableFits {n} (fitsCons {sigma = sigma} {A = A} {t = t} tail dt) =
    compFitsCons
      (nilComputableFits tail)
      (computableTmClosed dt)

  singleBinderComputableFitsEq : {n : ℕ} ->    {A : RawType} {sigma tau : Subst}
    -> (fitsEq : FitsEqSubst [] (A ∷ []) sigma tau)
    -> ComputableFitsEq n fitsEq
  singleBinderComputableFitsEq {n} (fitsEqCons {sigma = sigma} {A = A} {t = t} {u = u} tail dtu) =
    compFitsEqCons
      (nilComputableFitsEq tail)
      (computableTmEqClosed dtu)

  fitsToCompFits : {n : ℕ} -> {gamma : Ctx} {sigma : Subst}
    -> (fits : FitsSubst [] gamma sigma)
    -> ComputableFits n fits
  fitsToCompFits {n} (fitsNil wf) = compFitsNil
  fitsToCompFits {n} (fitsCons fits dt) =
    compFitsCons
      (fitsToCompFits fits)
      (computableTmClosed dt)

  fitsEqToCompFitsEq : {n : ℕ} -> {gamma : Ctx} {sigma tau : Subst}
    -> (fitsEq : FitsEqSubst [] gamma sigma tau)
    -> ComputableFitsEq n fitsEq
  fitsEqToCompFitsEq {n} (fitsEqNil wf) = compFitsEqNil
  fitsEqToCompFitsEq {n} (fitsEqCons {sigma = sigma} {A = A} {t = t} {u = u} fitsEq dtu) =
    compFitsEqCons
      (fitsEqToCompFitsEq fitsEq)
      (computableTmEqClosed dtu)

  compESigmaClosed : {n : ℕ} -> {A B M : RawType} {d d' m m' : RawTerm}
    -> ({t u v : RawTerm} {T : RawType}
         -> Computable n (termEq [] t u T)
         -> Computable n (termEq [] u v T)
         -> Computable n (termEq [] t v T))
    -> ({t u : RawTerm} {T U : RawType}
         -> Computable n (termEq [] t u T)
         -> Computable n (typeEq [] T U)
         -> Computable n (termEq [] t u U))
    -> HypComputable (suc n) (isType ((tySigma A B) ∷ []) M)
    -> Computable n (termEq [] d d' (tySigma A B))
    -> (dmm' : Derivable (termEq (B ∷ A ∷ []) m m' (sigmaBranchTy M)))
    -> Acc LexLt (substTaskLexMeasure dmm')
    -> Computable n
         (termEq [] (tmElSigma d m) (tmElSigma d' m') (subTy (singleSubst d) M))
  compESigmaClosed {n} {A = A} {B = B} {M = M} {d = d} {d' = d'} {m = m} {m' = m'}
    transCl convEqCl compM compdd' dmm' accDmm' =
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
  
    branchFitsEq : Σ
      (FitsEqSubst [] (B ∷ A ∷ [])
        (sigmaCompSub sigmaTmEqLeftFst sigmaTmEqLeftSnd)
        (sigmaCompSub sigmaTmEqRightFst sigmaTmEqRightSnd))
      (ComputableFitsEq n)
    branchFitsEq = sigmaCompComputableFitsEqHelper sigmaTmEqCompFst sigmaTmEqCompSnd
  
    branchEqPair : Computable n
      (termEq []
        (subTm (sigmaCompSub sigmaTmEqLeftFst sigmaTmEqLeftSnd) m)
        (subTm (sigmaCompSub sigmaTmEqRightFst sigmaTmEqRightSnd) m')
        (subTy (singleSubst (tmPair sigmaTmEqLeftFst sigmaTmEqLeftSnd)) M))
    branchEqPair =
      subst
        (λ T ->
          Computable n
            (termEq []
              (subTm (sigmaCompSub sigmaTmEqLeftFst sigmaTmEqLeftSnd) m)
              (subTm (sigmaCompSub sigmaTmEqRightFst sigmaTmEqRightSnd) m')
              T))
        (sigmaBranchTyComp sigmaTmEqLeftFst sigmaTmEqLeftSnd M)
        (eqSubDerivTmEqCompCF dmm' (fst branchFitsEq) (snd branchFitsEq) accDmm')
  
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
  
  compEQtrClosed : {n : ℕ} -> {A L : RawType} {l l' p p' : RawTerm}
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
  compEQtrClosed {n} {A = A} {L = L} {l = l} {l' = l'} {p = p} {p' = p'}
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
        (substDerivTmEqCompCF dll' (fst branchFitsLeft) (snd branchFitsLeft) accDll')
  
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
            (substDerivTmEqCompCF dcoh' cohFitsRight cohFitsRightComp accDcoh')))
  
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
  
  composeCompFits : {n : ℕ} -> {gamma delta : Ctx} {rho sigma : Subst} {t : RawTerm} {T : RawType}
    -> (outer : FitsSubst [] gamma rho)
    -> ComputableFits n outer
    -> (inner : FitsSubst gamma delta sigma)
    -> (dt : Derivable (hasTy gamma t T))
    -> Acc LexLt (substTaskLexMeasure dt)
    -> ComputableFits n (composeFits outer inner)
  composeCompFits {n} outer cOuter (fitsNil wf) dt accDt = compFitsNil
  composeCompFits {n} {rho = rho} outer cOuter
    (fitsCons {sigma = sigmaTail} {A = A} {t = t} inner dtInner) dt accDt =
    substCompFits
      (sym (compSubCons rho t sigmaTail))
      (compFitsCons
        {dt =
          subst
            (λ T -> Derivable (hasTy [] (subTm rho t) T))
            (subTyComp rho sigmaTail A)
            (substTmRule dtInner outer)}
        (composeCompFits outer cOuter inner dt accDt)
        (subst
          (λ T -> Computable n (hasTy [] (subTm rho t) T))
          (subTyComp rho sigmaTail A)
          (substDerivTmCompCF dtInner outer cOuter (LexLt-wf _))))

  composeCompEqFits : {n : ℕ} -> {gamma delta : Ctx} {rho eta sigma : Subst} {t : RawTerm} {T : RawType}
    -> (outer : FitsEqSubst [] gamma rho eta)
    -> ComputableFitsEq n outer
    -> (inner : FitsSubst gamma delta sigma)
    -> (dt : Derivable (hasTy gamma t T))
    -> Acc LexLt (substTaskLexMeasure dt)
    -> ComputableFitsEq n (composeEqFits outer inner)
  composeCompEqFits {n} outer cOuter (fitsNil wf) dt accDt = compFitsEqNil
  composeCompEqFits {n} {rho = rho} {eta = eta} outer cOuter
    (fitsCons {sigma = sigmaTail} {A = A} {t = t} inner dtInner) dt accDt =
    substCompFitsEqLeft
      (sym (compSubCons rho t sigmaTail))
      (substCompFitsEqRight
        (sym (compSubCons eta t sigmaTail))
        (compFitsEqCons
          {dtu =
            subst
              (λ T -> Derivable (termEq [] (subTm rho t) (subTm eta t) T))
              (subTyComp rho sigmaTail A)
              (eqSubTmRule dtInner outer)}
          (composeCompEqFits outer cOuter inner dt accDt)
          (subst
            (λ T -> Computable n (termEq [] (subTm rho t) (subTm eta t) T))
            (subTyComp rho sigmaTail A)
            (eqSubDerivTmCompCF dtInner outer (fitsEqToCompFitsEq outer) (LexLt-wf _)))))

  composeCompFitsEq : {n : ℕ} -> {gamma delta : Ctx} {rho sigma tau : Subst} {t u : RawTerm} {T : RawType}
    -> (outer : FitsSubst [] gamma rho)
    -> ComputableFits n outer
    -> (inner : FitsEqSubst gamma delta sigma tau)
    -> (dtu : Derivable (termEq gamma t u T))
    -> Acc LexLt (substTaskLexMeasure dtu)
    -> ComputableFitsEq n (composeFitsEq outer inner)
  composeCompFitsEq {n} outer cOuter (fitsEqNil wf) dtu accDtu = compFitsEqNil
  composeCompFitsEq {n} {rho = rho} outer cOuter
    (fitsEqCons {sigma = sigmaTail} {tau = tauTail} {A = A} {t = t} {u = u} inner dtuInner) dtu accDtu =
    substCompFitsEqLeft
      (sym (compSubCons rho t sigmaTail))
      (substCompFitsEqRight
        (sym (compSubCons rho u tauTail))
        (compFitsEqCons
          {dtu =
            subst
              (λ T -> Derivable (termEq [] (subTm rho t) (subTm rho u) T))
              (subTyComp rho sigmaTail A)
              (substTmEqRule dtuInner outer)}
          (composeCompFitsEq outer cOuter inner dtu accDtu)
          (subst
            (λ T -> Computable n (termEq [] (subTm rho t) (subTm rho u) T))
            (subTyComp rho sigmaTail A)
            (substDerivTmEqCompCF dtuInner outer (fitsToCompFits outer) (LexLt-wf _)))))

  composeCompEqFitsEq : {n : ℕ} -> {gamma delta : Ctx} {rho eta sigma tau : Subst} {t u : RawTerm} {T : RawType}
    -> (outer : FitsEqSubst [] gamma rho eta)
    -> ComputableFitsEq n outer
    -> (inner : FitsEqSubst gamma delta sigma tau)
    -> (dtu : Derivable (termEq gamma t u T))
    -> Acc LexLt (substTaskLexMeasure dtu)
    -> ComputableFitsEq n (composeEqFitsEq outer inner)
  composeCompEqFitsEq {n} outer cOuter (fitsEqNil wf) dtu accDtu = compFitsEqNil
  composeCompEqFitsEq {n} {rho = rho} {eta = eta} outer cOuter
    (fitsEqCons {sigma = sigmaTail} {tau = tauTail} {A = A} {t = t} {u = u} inner dtuInner) dtu accDtu =
    substCompFitsEqLeft
      (sym (compSubCons rho t sigmaTail))
      (substCompFitsEqRight
        (sym (compSubCons eta u tauTail))
        (compFitsEqCons
          {dtu =
            subst
              (λ T -> Derivable (termEq [] (subTm rho t) (subTm eta u) T))
              (subTyComp rho sigmaTail A)
              (eqSubTmEqRule dtuInner outer)}
          (composeCompEqFitsEq outer cOuter inner dtu accDtu)
          (subst
            (λ T -> Computable n (termEq [] (subTm rho t) (subTm eta u) T))
            (subTyComp rho sigmaTail A)
            (eqSubDerivTmEqCompCF dtuInner outer (fitsEqToCompFitsEq outer) (LexLt-wf _)))))

  substDerivTyCompCF {n} (fTop wf) fits cFits _ = compFTopClosed
  substDerivTyCompCF {n} {gamma = gamma} {sigma = sigma} (fSigma {A = A} {B = B} dA dB) fits cFits (acc rs) =
    let
      compA = substDerivTyCompCF dA fits cFits
        (LexLt-wf _)
      dAσ = substTyRule dA fits
      dB' : Derivable (isType (subTy sigma A ∷ []) (subTy (liftSubst sigma) B))
      dB' =
        subst
          (λ T -> Derivable (isType (subTy sigma A ∷ []) T))
          (cong (λ rho -> subTy rho B) (liftSubstCompKeep sigma))
          (substTyRule dB (liftFitsOne fits dAσ))
    in
    compTyClosedSigma
      (fSigma (compToDerivable compA) dB')
      evalSigma
      (reflTy (fSigma (compToDerivable compA) dB'))
      compA
      dB'
  substDerivTyCompCF {n} (fEq {A = A} {a = a} {b = b} dA da db) fits cFits (acc rs) =
    compFEqClosed
      (substDerivTyCompCF dA fits cFits (LexLt-wf _))
      (substDerivTmCompCF da fits cFits (LexLt-wf _))
      (substDerivTmCompCF db fits cFits (LexLt-wf _))
  substDerivTyCompCF {n} (fQtr {A = A} dA) fits cFits (acc rs) =
    compFQtrClosed (substDerivTyCompCF dA fits cFits (LexLt-wf _))
  substDerivTyCompCF {n} {sigma = sigma} (weakenTy {delta = delta} {A = A} d wf) fits cFits (acc rs) =
    subst
      (λ T -> Computable n (isType [] T))
      (sym (subTyWkBy sigma (length delta) A))
      (substDerivTyCompCF d (dropFits delta fits) (dropCompFits delta cFits) (LexLt-wf _))
  substDerivTyCompCF {n} {sigma = sigma} (substTyRule {sigma = sigma'} {A = A} d fits') fits cFits (acc rs) =
    let
      composedFits = composeFits fits fits'
      composedCFits = composeCompFits fits cFits fits' (iTop (fitsSubstCtxWF fits')) (LexLt-wf _)
    in
    subst
      (λ T -> Computable n (isType [] T))
      (sym (subTyComp sigma sigma' A))
      (substDerivTyCompCF d composedFits composedCFits (LexLt-wf _))

  substDerivTyEqCompCF {n} (reflTy d) fits cFits (acc rs) =
    compReflTy (substDerivTyCompCF d fits cFits (LexLt-wf _))
  substDerivTyEqCompCF {n} (symTy d dB) fits cFits (acc rs) =
    compSymTyClosed (substDerivTyEqCompCF d fits cFits (LexLt-wf _))
  substDerivTyEqCompCF {n} (transTy d₁ d₂) fits cFits (acc rs) =
    compTransTyClosed
      (substDerivTyEqCompCF d₁ fits cFits (LexLt-wf _))
      (substDerivTyEqCompCF d₂ fits cFits (LexLt-wf _))
  substDerivTyEqCompCF {n} {sigma = sigma} (fSigmaEq {A = A} {B = B} {D = D} dAC dB dBD) fits cFits (acc rs) =
    let
      compAC = substDerivTyEqCompCF dAC fits cFits (LexLt-wf _)
      compA = compTyEqLeft compAC
      compC = compTyEqRightClosed compAC
      dAσ = compToDerivable compA
      compB =
        subst
          (λ T -> HypComputable (suc n) (isType (subTy sigma A ∷ []) T))
          (cong (λ rho -> subTy rho B) (liftSubstCompKeep sigma))
          (hypTyOpen
            nonemptyNeNil
            (substTyRule dB (liftFitsOne fits dAσ))
            (λ tau fits2 _ accD ->
              subst
                (λ T -> Computable n (isType [] T))
                (sym
                  (cong (λ rho -> subTy tau (subTy rho B)) (liftSubstCompKeep sigma)
                    ∙ subTyComp tau (liftSubst sigma) B))
                (compTyEqLeft
                  (substDerivTyEqCompCF
                    dBD
                    (composeOneBinder fits dAσ fits2) (fitsToCompFits (composeOneBinder fits dAσ fits2)) (LexLt-wf _))))
            (λ tau₁ tau₂ fitsEq2 _ accD ->
              subst
                (λ J -> Computable n J)
                (sym
                  (cong₂ (typeEq [])
                    (cong (λ rho -> subTy tau₁ (subTy rho B)) (liftSubstCompKeep sigma)
                      ∙ subTyComp tau₁ (liftSubst sigma) B)
                    (cong (λ rho -> subTy tau₂ (subTy rho B)) (liftSubstCompKeep sigma)
                      ∙ subTyComp tau₂ (liftSubst sigma) B)))
                (compTransTyClosed
                  (eqSubDerivTyEqCompCF
                    dBD
                    (composeOneBinderEq fits dAσ fitsEq2) (fitsEqToCompFitsEq (composeOneBinderEq fits dAσ fitsEq2)) (LexLt-wf _))
                  (compSymTyClosed
                    (substDerivTyEqCompCF
                      dBD
                      (composeOneBinder
                        fits
                        dAσ
                        (fitsEqSubstRight (wfCons wfNil dAσ) fitsEq2)) (fitsToCompFits (composeOneBinder
                        fits
                        dAσ
                        (fitsEqSubstRight (wfCons wfNil dAσ) fitsEq2))) (LexLt-wf _))))))
      compBD =
        subst
          (λ J -> HypComputable (suc n) J)
          (cong₂
            (typeEq (subTy sigma A ∷ []))
            (cong (λ rho -> subTy rho B) (liftSubstCompKeep sigma))
            (cong (λ rho -> subTy rho D) (liftSubstCompKeep sigma)))
          (hypTyEqOpen
            nonemptyNeNil
            (substTyEqRule dBD (liftFitsOne fits dAσ))
            (subst
              (λ T -> HypComputable (suc n) (isType (subTy sigma A ∷ []) T))
              (sym (cong (λ rho -> subTy rho B) (liftSubstCompKeep sigma)))
              compB)
            (λ tau fits2 _ accD ->
              subst
                (λ J -> Computable n J)
                (sym
                  (cong₂ (typeEq [])
                    (cong (λ rho -> subTy tau (subTy rho B)) (liftSubstCompKeep sigma)
                      ∙ subTyComp tau (liftSubst sigma) B)
                    (cong (λ rho -> subTy tau (subTy rho D)) (liftSubstCompKeep sigma)
                      ∙ subTyComp tau (liftSubst sigma) D)))
                (substDerivTyEqCompCF
                  dBD
                  (composeOneBinder fits dAσ fits2) (fitsToCompFits (composeOneBinder fits dAσ fits2)) (LexLt-wf _)))
            (λ tau₁ tau₂ fitsEq2 _ accD ->
              subst
                (λ J -> Computable n J)
                (sym
                  (cong₂ (typeEq [])
                    (cong (λ rho -> subTy tau₁ (subTy rho B)) (liftSubstCompKeep sigma)
                      ∙ subTyComp tau₁ (liftSubst sigma) B)
                    (cong (λ rho -> subTy tau₂ (subTy rho D)) (liftSubstCompKeep sigma)
                      ∙ subTyComp tau₂ (liftSubst sigma) D)))
                (eqSubDerivTyEqCompCF
                  dBD
                  (composeOneBinderEq fits dAσ fitsEq2) (fitsEqToCompFitsEq (composeOneBinderEq fits dAσ fitsEq2)) (LexLt-wf _))))
      compSigmaA = compFSigmaClosed compA (hypCompToDerivable (hypTyEqLeft compBD))
      compSigmaC = compFSigmaClosed compC (hypCompToDerivable (compTransportFamilyTy compAC (hypTyEqRight compBD)))
    in
    compTyEqClosedSigma
      (fSigmaEq (compToDerivable compAC) (hypCompToDerivable compB) (hypCompToDerivable compBD))
      compSigmaA
      compSigmaC
      evalSigma
      evalSigma
      compAC
      (hypCompToDerivable compBD)
  substDerivTyEqCompCF {n} (fEqEq dAC dac dbd) fits cFits (acc rs) =
    let
      compAC = substDerivTyEqCompCF dAC fits cFits (LexLt-wf _)
      compac = substDerivTmEqCompCF dac fits cFits (LexLt-wf _)
      compbd = substDerivTmEqCompCF dbd fits cFits (LexLt-wf _)
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
  substDerivTyEqCompCF {n} (fQtrEq dAB) fits cFits (acc rs) =
    let
      compAB = substDerivTyEqCompCF dAB fits cFits (LexLt-wf _)
    in
    compTyEqClosedQtr
      (fQtrEq (compToDerivable compAB))
      (compFQtrClosed (compTyEqLeft compAB))
      (compFQtrClosed (compTyEqRightClosed compAB))
      evalQtr
      evalQtr
      compAB
  substDerivTyEqCompCF {n} {sigma = sigma} (weakenTyEq {delta = delta} {A = A} {B = B} d wf) fits cFits (acc rs) =
    subst
      (λ J -> Computable n J)
      (cong₂ (typeEq [])
        (sym (subTyWkBy sigma (length delta) A))
        (sym (subTyWkBy sigma (length delta) B)))
      (substDerivTyEqCompCF d (dropFits delta fits) (fitsToCompFits (dropFits delta fits)) (LexLt-wf _))
  substDerivTyEqCompCF {n} {sigma = sigma} (substTyEqRule {sigma = sigma'} {A = A} {B = B} d fits') fits cFits (acc rs) =
    let
      composedFits = composeFits fits fits'
    in
    subst
      (λ J -> Computable n J)
      (cong₂ (typeEq [])
        (sym (subTyComp sigma sigma' A))
        (sym (subTyComp sigma sigma' B)))
      (substDerivTyEqCompCF d composedFits (fitsToCompFits composedFits) (LexLt-wf _))
  substDerivTyEqCompCF {n} {sigma = sigma} (eqSubTyRule {sigma = sigma'} {tau = tau'} {A = A} d fitsEq') fits cFits (acc rs) =
    let
      composedFitsEq = composeFitsEq fits fitsEq'
    in
    subst
      (λ J -> Computable n J)
      (cong₂ (typeEq [])
        (sym (subTyComp sigma sigma' A))
        (sym (subTyComp sigma tau' A)))
      (eqSubDerivTyCompCF d composedFitsEq (fitsEqToCompFitsEq composedFitsEq) (LexLt-wf _))
  substDerivTyEqCompCF {n} {sigma = sigma} (eqSubTyEqRule {sigma = sigma'} {tau = tau'} {A = A} {B = B} d fitsEq') fits cFits (acc rs) =
    let
      composedFitsEq = composeFitsEq fits fitsEq'
    in
    subst
      (λ J -> Computable n J)
      (cong₂ (typeEq [])
        (sym (subTyComp sigma sigma' A))
        (sym (subTyComp sigma tau' B)))
      (eqSubDerivTyEqCompCF d composedFitsEq (fitsEqToCompFitsEq composedFitsEq) (LexLt-wf _))
  
  substDerivTmCompCF {n} (varStar {delta = delta} {A = A} wf dA) fits cFits _ =
    lookupCompFits {delta = delta} {A = A} cFits
  substDerivTmCompCF {n} (iTop wf) fits cFits _ = compITopClosed
  substDerivTmCompCF {n} {sigma = sigma}
    (iSigma {a = a} {b = b} {A = A} {B = B} da db dSigma) fits cFits (acc rs) =
    let
      compa = substDerivTmCompCF da fits cFits (LexLt-wf _)
      compb =
        subst
          (λ T -> Computable n (hasTy [] (subTm sigma b) T))
          (subTyComp sigma (singleSubst a) B
            ∙ cong (λ rho -> subTy rho B) (sym (singleSubstCompLift sigma a))
            ∙ sym (subTyComp (singleSubst (subTm sigma a)) (liftSubst sigma) B))
          (substDerivTmCompCF db fits cFits (LexLt-wf _))
    in
    compISigmaClosed compa compb (substDerivTyCompCF dSigma fits cFits (LexLt-wf _))
  substDerivTmCompCF {n} (iEq da) fits cFits (acc rs) =
    compIEqClosed (substDerivTmCompCF da fits cFits (LexLt-wf _))
  substDerivTmCompCF {n} (iQtr da) fits cFits (acc rs) =
    compIQtrClosed (substDerivTmCompCF da fits cFits (LexLt-wf _))
  substDerivTmCompCF {n} {gamma = gamma} {sigma = sigma}
    (eSigma {A = A} {B = B} {M = M} {d = d} {m = m} dM dd dm) fits cFits (acc rs) =
    let
      compdd = substDerivTmCompCF dd fits cFits (LexLt-wf _)
      compSigma = compTmToCompTy compdd
      dSigmaσ = compToDerivable compSigma
      tyInv = invertSigmaTy compSigma evalSigma
      compAσ = ClosedSigmaTyInv.sigmaTyCompHead tyInv
      dAσ = compToDerivable compAσ
      dBσ = ClosedSigmaTyInv.sigmaTyFamDeriv tyInv
      compM =
        subst
          (λ T -> HypComputable (suc n) (isType (subTy sigma (tySigma A B) ∷ []) T))
          (cong (λ rho -> subTy rho M) (liftSubstCompKeep sigma))
          (hypTyOpen
            nonemptyNeNil
            (substTyRule dM (liftFitsOne fits dSigmaσ))
            (λ rho fits2 cFits2 accD ->
              let
                composedCFits =
                  substCompFits
                    (cong (compSub rho) (liftSubstCompKeep sigma))
                    (composeCompFits
                      fits2
                      cFits2
                      (liftFitsOne fits dSigmaσ)
                      (iTop (fitsSubstCtxWF (liftFitsOne fits dSigmaσ)))
                      (LexLt-wf _))
              in
              subst
                (λ T -> Computable n (isType [] T))
                (sym
                  (cong (λ theta -> subTy rho (subTy theta M)) (liftSubstCompKeep sigma)
                    ∙ subTyComp rho (liftSubst sigma) M))
                (substDerivTyCompCF
                  dM
                  (composeOneBinder fits dSigmaσ fits2) (fitsToCompFits (composeOneBinder fits dSigmaσ fits2)) (LexLt-wf _)))
            (λ rho eta fitsEq2 _ accD ->
              subst
                (λ J -> Computable n J)
                (sym
                  (cong₂ (typeEq [])
                    (cong (λ theta -> subTy rho (subTy theta M)) (liftSubstCompKeep sigma)
                      ∙ subTyComp rho (liftSubst sigma) M)
                    (cong (λ theta -> subTy eta (subTy theta M)) (liftSubstCompKeep sigma)
                      ∙ subTyComp eta (liftSubst sigma) M)))
                (eqSubDerivTyCompCF
                  dM
                  (composeOneBinderEq fits dSigmaσ fitsEq2) (fitsEqToCompFitsEq (composeOneBinderEq fits dSigmaσ fitsEq2)) (LexLt-wf _))))
  
      -- Stage 3 v29: build raw dmm' : Derivable (termEq (B_sub ∷ A_sub ∷ []) m_sub m_sub ...).
      -- Wraps dm with substTmRule (2-binder lift) and reflTm.
      lifted1 : FitsSubst (subTy sigma A ∷ []) (A ∷ gamma) (liftSubst sigma)
      lifted1 =
        subst
          (λ rho -> FitsSubst (subTy sigma A ∷ []) (A ∷ gamma) rho)
          (liftSubstCompKeep sigma)
          (liftFitsOne fits dAσ)
      lifted2 : FitsSubst
        (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) (B ∷ A ∷ gamma)
        (liftSubst (liftSubst sigma))
      lifted2 =
        subst
          (λ rho -> FitsSubst (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) (B ∷ A ∷ gamma) rho)
          (liftSubstCompKeep (liftSubst sigma))
          (liftFits lifted1 dBσ)
      dmSub : Derivable
        (hasTy (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ [])
          (subTm (liftSubst (liftSubst sigma)) m)
          (sigmaBranchTy (subTy (liftSubst sigma) M)))
      dmSub =
        subst
          (λ T ->
            Derivable (hasTy (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ [])
              (subTm (liftSubst (liftSubst sigma)) m) T))
          (sigmaBranchTyLiftComp sigma M)
          (substTmRule dm lifted2)
      dmm' : Derivable
        (termEq (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ [])
          (subTm (liftSubst (liftSubst sigma)) m)
          (subTm (liftSubst (liftSubst sigma)) m)
          (sigmaBranchTy (subTy (liftSubst sigma) M)))
      dmm' = reflTm dmSub

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
      (λ J -> Computable n J)
      (sym resultPath)
      (compTmEqLeft
        (compESigmaClosed compTransTmClosed compConvTmEqClosed
          compM (compReflTm compdd) dmm' (LexLt-wf _)))
  substDerivTmCompCF
    {n} {gamma = gamma} {sigma = sigma}
    (eQtr {A = A} {L = L} {l = l} {p = p} dL dp dBranch dl dcoh) fits cFits (acc rs) =
    let
      compdp = substDerivTmCompCF dp fits cFits (LexLt-wf _)
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
      wkCtxWF : CtxWF (subTy (liftSubst sigma) (wkTyBy 1 A) ∷ subTy sigma A ∷ [])
      wkCtxWF = wfCons (wfCons wfNil dAσ) dWkAσ
      compL =
        subst
          (λ T -> HypComputable (suc n) (isType (subTy sigma (tyQtr A) ∷ []) T))
          (cong (λ rho -> subTy rho L) (liftSubstCompKeep sigma))
          (hypTyOpen
            nonemptyNeNil
            (substTyRule dL (liftFitsOne fits dQtrσ))
            (λ rho fits2 cFits2 accDL ->
              let
                composedFits = composeOneBinder fits dQtrσ fits2
              in
              subst
                (λ T -> Computable n (isType [] T))
                (sym
                  (cong (λ theta -> subTy rho (subTy theta L)) (liftSubstCompKeep sigma)
                    ∙ subTyComp rho (liftSubst sigma) L))
                (substDerivTyCompCF
                  dL
                  composedFits
                  (fitsToCompFits composedFits)
                  (LexLt-wf _)))
            (λ rho eta fitsEq2 _ accDL ->
              let
                composedFitsEq = composeOneBinderEq fits dQtrσ fitsEq2
              in
              subst
                (λ J -> Computable n J)
                (sym
                  (cong₂ (typeEq [])
                    (cong (λ theta -> subTy rho (subTy theta L)) (liftSubstCompKeep sigma)
                      ∙ subTyComp rho (liftSubst sigma) L)
                    (cong (λ theta -> subTy eta (subTy theta L)) (liftSubstCompKeep sigma)
                      ∙ subTyComp eta (liftSubst sigma) L)))
                (eqSubDerivTyCompCF
                  dL
                  composedFitsEq
                  (fitsEqToCompFitsEq composedFitsEq)
                  (LexLt-wf _))))
      compBranchTy =
        subst
          (λ T -> HypComputable (suc n) (isType (subTy sigma A ∷ []) T))
          (cong (λ rho -> subTy rho (qtrBranchTy L)) (liftSubstCompKeep sigma))
          (hypTyOpen
            nonemptyNeNil
            (substTyRule dBranch (liftFitsOne fits dAσ))
            (λ rho fits2 cFits2 accDBranch ->
              let
                composedFits = composeOneBinder fits dAσ fits2
              in
              subst
                (λ T -> Computable n (isType [] T))
                (sym
                  (cong (λ theta -> subTy rho (subTy theta (qtrBranchTy L)))
                    (liftSubstCompKeep sigma)
                    ∙ subTyComp rho (liftSubst sigma) (qtrBranchTy L)))
                (substDerivTyCompCF
                  dBranch
                  composedFits
                  (fitsToCompFits composedFits)
                  (LexLt-wf _)))
            (λ rho eta fitsEq2 _ accDBranch ->
              let
                composedFitsEq = composeOneBinderEq fits dAσ fitsEq2
              in
              subst
                (λ J -> Computable n J)
                (sym
                  (cong₂ (typeEq [])
                    (cong (λ theta -> subTy rho (subTy theta (qtrBranchTy L)))
                      (liftSubstCompKeep sigma)
                      ∙ subTyComp rho (liftSubst sigma) (qtrBranchTy L))
                    (cong (λ theta -> subTy eta (subTy theta (qtrBranchTy L)))
                      (liftSubstCompKeep sigma)
                      ∙ subTyComp eta (liftSubst sigma) (qtrBranchTy L))))
                (eqSubDerivTyCompCF
                  dBranch
                  composedFitsEq
                  (fitsEqToCompFitsEq composedFitsEq)
                  (LexLt-wf _))))
  
      compl =
        subst
          (λ T ->
            HypComputable (suc n)
              (hasTy (subTy sigma A ∷ [])
                (subTm (liftSubst sigma) l)
                T))
          (qtrBranchTyLiftComp sigma L)
          (subst
            (λ J -> HypComputable (suc n) J)
            (cong₂
              (hasTy (subTy sigma A ∷ []))
              (cong (λ rho -> subTm rho l) (liftSubstCompKeep sigma))
              (cong (λ rho -> subTy rho (qtrBranchTy L)) (liftSubstCompKeep sigma)))
            (hypTmOpen
              nonemptyNeNil
              (substTmRule dl (liftFitsOne fits dAσ))
              (subst
                (λ J -> HypComputable (suc n) J)
                (sym
                  (cong (λ rho -> isType (subTy sigma A ∷ []) (subTy rho (qtrBranchTy L)))
                    (liftSubstCompKeep sigma)))
                compBranchTy)
              (λ tau fits2 cFits2 accDl ->
                let
                  composedFits =
                    subst
                      (λ rho -> FitsSubst [] (A ∷ gamma) rho)
                      (cong (compSub tau) (liftSubstCompKeep sigma))
                      (composeFits fits2 (liftFitsOne fits dAσ))
                  composedCFits =
                    substCompFits
                      (cong (compSub tau) (liftSubstCompKeep sigma))
                      (composeCompFits
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
                      (cong (λ rho -> subTm tau (subTm rho l)) (liftSubstCompKeep sigma)
                        ∙ subTmComp tau (liftSubst sigma) l)
                      (cong (λ rho -> subTy tau (subTy rho (qtrBranchTy L))) (liftSubstCompKeep sigma)
                        ∙ subTyComp tau (liftSubst sigma) (qtrBranchTy L))))
                  (substDerivTmCompCF dl composedFits composedCFits (LexLt-wf _)))
              (λ tau₁ tau₂ fitsEq2 _ accDl ->
                subst
                  (λ J -> Computable n J)
                  (sym
                    (cong₃ (termEq [])
                      (cong (λ rho -> subTm tau₁ (subTm rho l)) (liftSubstCompKeep sigma)
                        ∙ subTmComp tau₁ (liftSubst sigma) l)
                      (cong (λ rho -> subTm tau₂ (subTm rho l)) (liftSubstCompKeep sigma)
                        ∙ subTmComp tau₂ (liftSubst sigma) l)
                      (cong (λ rho -> subTy tau₁ (subTy rho (qtrBranchTy L))) (liftSubstCompKeep sigma)
                        ∙ subTyComp tau₁ (liftSubst sigma) (qtrBranchTy L))))
                  (eqSubDerivTmCompCF
                    dl
                    (composeOneBinderEq fits dAσ fitsEq2)
                    (fitsEqToCompFitsEq (composeOneBinderEq fits dAσ fitsEq2))
                    (LexLt-wf _)))))
  
      compcohAssoc =
        subst
          (λ J -> HypComputable (suc n) J)
          (cong₂
            (hasTy (subTy (liftSubst sigma) (wkTyBy 1 A) ∷ subTy sigma A ∷ []))
            (sym (wkTmLiftSubst (liftSubst sigma) l))
            (qtrBranchTyWk (subTy (liftSubst sigma) L)
              ∙ sym (qtrCohTyLiftComp sigma L)))
          (weakenOneOpenTm compl wkCtxWF)
  
      compcoh =
        subst
          (λ J -> HypComputable (suc n) J)
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
          (let
             lifted1-coh : FitsSubst (subTy sigma A ∷ []) (A ∷ gamma) (liftSubst sigma)
             lifted1-coh =
               subst
                 (λ rho -> FitsSubst (subTy sigma A ∷ []) (A ∷ gamma) rho)
                 (liftSubstCompKeep sigma)
                 (liftFitsOne fits dAσ)
           in
           subst
             (λ J -> HypComputable (suc n) J)
             (cong₃
               (termEq (subTy (liftSubst sigma) (wkTyBy 1 A) ∷ subTy sigma A ∷ []))
               (cong (λ rho -> subTm rho (wkTmBy 1 l)) (liftSubstCompKeep (liftSubst sigma)))
               (cong (λ rho -> subTm rho (renTm qtrSecondBranchRen l)) (liftSubstCompKeep (liftSubst sigma)))
               (cong (λ rho -> subTy rho (qtrCohTy L)) (liftSubstCompKeep (liftSubst sigma))))
             (hypTmEqOpen
               nonemptyNeNil
               (substTmEqRule dcoh (liftFits lifted1-coh dWkAσ))
               (subst
                 (λ J -> HypComputable (suc n) J)
                 (sym
                   (cong₂
                     (hasTy (subTy (liftSubst sigma) (wkTyBy 1 A) ∷ subTy sigma A ∷ []))
                     (cong (λ rho -> subTm rho (wkTmBy 1 l)) (liftSubstCompKeep (liftSubst sigma)))
                     (cong (λ rho -> subTy rho (qtrCohTy L)) (liftSubstCompKeep (liftSubst sigma)))))
                 compcohAssoc)
               (λ tau fits2 _ accDcoh ->
                 subst
                   (λ J -> Computable n J)
                   (sym
                     (cong₃ (termEq [])
                       (cong (λ rho -> subTm tau (subTm rho (wkTmBy 1 l))) (liftSubstCompKeep (liftSubst sigma))
                         ∙ subTmComp tau (liftSubst (liftSubst sigma)) (wkTmBy 1 l))
                       (cong (λ rho -> subTm tau (subTm rho (renTm qtrSecondBranchRen l))) (liftSubstCompKeep (liftSubst sigma))
                         ∙ subTmComp tau (liftSubst (liftSubst sigma)) (renTm qtrSecondBranchRen l))
                       (cong (λ rho -> subTy tau (subTy rho (qtrCohTy L))) (liftSubstCompKeep (liftSubst sigma))
                         ∙ subTyComp tau (liftSubst (liftSubst sigma)) (qtrCohTy L))))
                   (substDerivTmEqCompCF
                     dcoh
                     (composeTwoBinders fits dAσ dWkAσ fits2)
                     (fitsToCompFits (composeTwoBinders fits dAσ dWkAσ fits2))
                     (LexLt-wf _)))
               (λ tau₁ tau₂ fitsEq2 _ accDcoh ->
                 subst
                   (λ J -> Computable n J)
                   (sym
                     (cong₃ (termEq [])
                       (cong (λ rho -> subTm tau₁ (subTm rho (wkTmBy 1 l))) (liftSubstCompKeep (liftSubst sigma))
                         ∙ subTmComp tau₁ (liftSubst (liftSubst sigma)) (wkTmBy 1 l))
                       (cong (λ rho -> subTm tau₂ (subTm rho (renTm qtrSecondBranchRen l))) (liftSubstCompKeep (liftSubst sigma))
                         ∙ subTmComp tau₂ (liftSubst (liftSubst sigma)) (renTm qtrSecondBranchRen l))
                       (cong (λ rho -> subTy tau₁ (subTy rho (qtrCohTy L))) (liftSubstCompKeep (liftSubst sigma))
                         ∙ subTyComp tau₁ (liftSubst (liftSubst sigma)) (qtrCohTy L))))
                   (eqSubDerivTmEqCompCF
                     dcoh
                     (composeTwoBindersEq fits dAσ dWkAσ fitsEq2)
                     (fitsEqToCompFitsEq (composeTwoBindersEq fits dAσ dWkAσ fitsEq2))
                     (LexLt-wf _)))))

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
      -- Stage 3 v29: extract raw Derivables + <-wellfounded for compEQtrClosed.
      dll'OpenEQtr = reflTm (hypCompToDerivable compl)
      dcohOpenEQtr = hypCompToDerivable compcoh
    in
    subst
      (λ J -> Computable n J)
      (sym resultPath)
      (compTmEqLeft
        (compEQtrClosed
          compTransTmClosed
          compSymTmClosed
          compConvTmEqClosed
          compL
          (compReflTm compdp)
          dll'OpenEQtr (LexLt-wf _)
          dcohOpenEQtr
          dcohOpenEQtr (LexLt-wf _)))
  substDerivTmCompCF {n} (conv d dAB) fits cFits (acc rs) =
    compConvTmClosed
      (substDerivTmCompCF d fits cFits (LexLt-wf _))
      (substDerivTyEqCompCF dAB fits cFits (LexLt-wf _))
  substDerivTmCompCF {n} {sigma = sigma} (weakenTm {delta = delta} {t = t} {A = A} d wf) fits cFits (acc rs) =
    subst
      (λ J -> Computable n J)
      (cong₂ (hasTy [])
        (sym (subTmWkBy sigma (length delta) t))
        (sym (subTyWkBy sigma (length delta) A)))
      (substDerivTmCompCF d (dropFits delta fits) (dropCompFits delta cFits) (LexLt-wf _))
  substDerivTmCompCF {n} {sigma = sigma} (substTmRule {sigma = sigma'} {t = t} {A = A} d fits') fits cFits (acc rs) =
    let
      composedFits = composeFits fits fits'
      composedCFits = composeCompFits fits cFits fits' (iTop (fitsSubstCtxWF fits')) (LexLt-wf _)
    in
    subst
      (λ J -> Computable n J)
      (cong₂ (hasTy [])
        (sym (subTmComp sigma sigma' t))
        (sym (subTyComp sigma sigma' A)))
      (substDerivTmCompCF d composedFits composedCFits (LexLt-wf _))

  -- Closed-context (gamma=[]) variant of substDerivTmComp.
  -- Single catch-all clause to avoid Agda's split-completeness check on varStar
  -- (which can't be auto-discharged because delta ++ A ∷ gamma can't be matched
  -- against [] by simple unification).
  -- The substTmRule sub-term decrease that we need for the SCT trace is provided
  -- by a separate helper substDerivTmCompClosed-Helper below — but that helper
  -- has the same problem. Workaround: keep this as a single-clause function and
  -- accept that the trace will need to come from elsewhere.
  substDerivTmCompClosed {n} {t = t} {A = A} d =
    subst
      (λ J -> Computable n J)
      (cong₂ (hasTy []) (subTmId t) (subTyId A))
      (substDerivTmCompCF d (fitsNil {gamma = []} {delta = []} {sigma = idSubst} wfNil) (fitsToCompFits (fitsNil {gamma = []} {delta = []} {sigma = idSubst} wfNil)) (LexLt-wf _))

  
  substDerivTmEqCompCF {n} (reflTm d) fits cFits (acc rs) =
    compReflTmClosed (substDerivTmCompCF d fits cFits (LexLt-wf _))
  substDerivTmEqCompCF {n} (symTm d du dA) fits cFits (acc rs) =
    compSymTmClosed (substDerivTmEqCompCF d fits cFits (LexLt-wf _))
  substDerivTmEqCompCF {n} (transTm d₁ d₂) fits cFits (acc rs) =
    compTransTmClosed
      (substDerivTmEqCompCF d₁ fits cFits (LexLt-wf _))
      (substDerivTmEqCompCF d₂ fits cFits (LexLt-wf _))
  substDerivTmEqCompCF {n} (convEq d dAB) fits cFits (acc rs) =
    compConvTmEqClosed
      (substDerivTmEqCompCF d fits cFits (LexLt-wf _))
      (substDerivTyEqCompCF dAB fits cFits (LexLt-wf _))
  substDerivTmEqCompCF {n} (cTop d) fits cFits (acc rs) =
    compCTopClosed (substDerivTmCompCF d fits cFits (LexLt-wf _))
  substDerivTmEqCompCF {n} {sigma = sigma}
    (iSigmaEq {a = a} {b = b} {d = d} {A = A} {B = B} dac dbd dA dB) fits cFits (acc rs) =
    let
      compac = substDerivTmEqCompCF dac fits cFits (LexLt-wf _)
      compbdRaw = substDerivTmEqCompCF dbd fits cFits (LexLt-wf _)
      compA = substDerivTyCompCF dA fits cFits (LexLt-wf _)
      dAσ = compToDerivable compA
      compB =
        subst
          (λ T -> HypComputable (suc n) (isType (subTy sigma A ∷ []) T))
          (cong (λ rho -> subTy rho B) (liftSubstCompKeep sigma))
          (hypTyOpen
            nonemptyNeNil
            (substTyRule dB (liftFitsOne fits dAσ))
            (λ rho fits2 _ accD ->
              subst
                (λ T -> Computable n (isType [] T))
                (sym
                  (cong (λ theta -> subTy rho (subTy theta B)) (liftSubstCompKeep sigma)
                    ∙ subTyComp rho (liftSubst sigma) B))
                (substDerivTyCompCF
                  dB
                  (composeOneBinder fits dAσ fits2) (fitsToCompFits (composeOneBinder fits dAσ fits2)) (LexLt-wf _)))
            (λ rho eta fitsEq2 _ accD ->
              subst
                (λ J -> Computable n J)
                (sym
                  (cong₂ (typeEq [])
                    (cong (λ theta -> subTy rho (subTy theta B)) (liftSubstCompKeep sigma)
                      ∙ subTyComp rho (liftSubst sigma) B)
                    (cong (λ theta -> subTy eta (subTy theta B)) (liftSubstCompKeep sigma)
                      ∙ subTyComp eta (liftSubst sigma) B)))
                (eqSubDerivTyCompCF
                  dB
                  (composeOneBinderEq fits dAσ fitsEq2) (fitsEqToCompFitsEq (composeOneBinderEq fits dAσ fitsEq2)) (LexLt-wf _))))
      compa = compTmEqLeft compac
      compcA = compTmEqRightClosed compac
      compbd =
        subst
          (λ T -> Computable n (termEq [] (subTm sigma b) (subTm sigma d) T))
          (subTyComp sigma (singleSubst a) B
            ∙ cong (λ rho -> subTy rho B) (sym (singleSubstCompLift sigma a))
            ∙ sym (subTyComp (singleSubst (subTm sigma a)) (liftSubst sigma) B))
          compbdRaw
      compb = compTmEqLeft compbd
      compdA = compTmEqRightClosed compbd
      compd =
        compConvTmClosed compdA (compSingleEqSubstTyClosed compB compac (LexLt-wf _))
      compPairLeft = compISigmaClosed compa compb (compFSigmaClosed compA (hypCompToDerivable compB))
      compPairRight = compISigmaClosed compcA compd (compFSigmaClosed compA (hypCompToDerivable compB))
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
  substDerivTmEqCompCF {n} {gamma = gamma} {sigma = sigma}
    (eSigmaEq {A = A} {B = B} {M = M} {d = d} {d' = d'} {m = m} {m' = m'}
      dM dd dmL dm) fits cFits (acc rs) =
    -- Phase F.2 (eSigmaEq): inlined body of substDerivTmEqCompESigmaEq.
    let
      compdd = substDerivTmEqCompCF dd fits cFits
        (rs _ (lift-lex-eq refl (substMeasure-eSigmaEq-dd< dM dd dmL dm)))
      compSigma = compTmToCompTy (compTmEqLeft compdd)
      dSigmaσ = compToDerivable compSigma
      tyInv = invertSigmaTy compSigma evalSigma
      compAσ = ClosedSigmaTyInv.sigmaTyCompHead tyInv
      dAσ = compToDerivable compAσ
      dBσ = ClosedSigmaTyInv.sigmaTyFamDeriv tyInv
      compM =
        subst
          (λ T -> HypComputable (suc n) (isType (subTy sigma (tySigma A B) ∷ []) T))
          (cong (λ rho -> subTy rho M) (liftSubstCompKeep sigma))
          (hypTyOpen
            nonemptyNeNil
            (substTyRule dM (liftFitsOne fits dSigmaσ))
            -- Phase F.2 (Scope B): destructure closure Acc, use accRs _ proof<
            (λ rho fits2 _ accD ->
              subst
                (λ T -> Computable n (isType [] T))
                (sym
                  (cong (λ theta -> subTy rho (subTy theta M)) (liftSubstCompKeep sigma)
                    ∙ subTyComp rho (liftSubst sigma) M))
                (substDerivTyCompCF
                  dM
                  (composeOneBinder fits dSigmaσ fits2) (fitsToCompFits (composeOneBinder fits dSigmaσ fits2)) (access accD _ (lift-lex-eq (sym (tyDepth-subTy _ M)) (substMeasure-substTyRule< dM (liftFitsOne fits dSigmaσ))))))
            -- Phase F.2 (Scope B): destructure closure Acc, use accRs _ proof<
            (λ rho eta fitsEq2 _ accD ->
              subst
                (λ J -> Computable n J)
                (sym
                  (cong₂ (typeEq [])
                    (cong (λ theta -> subTy rho (subTy theta M)) (liftSubstCompKeep sigma)
                      ∙ subTyComp rho (liftSubst sigma) M)
                    (cong (λ theta -> subTy eta (subTy theta M)) (liftSubstCompKeep sigma)
                      ∙ subTyComp eta (liftSubst sigma) M)))
                (eqSubDerivTyCompCF
                  dM
                  (composeOneBinderEq fits dSigmaσ fitsEq2) (fitsEqToCompFitsEq (composeOneBinderEq fits dSigmaσ fitsEq2)) (access accD _ (lift-lex-eq (sym (tyDepth-subTy _ M)) (substMeasure-substTyRule< dM (liftFitsOne fits dSigmaσ)))))))
  
      -- Stage 3 v29: raw dmm' from substTmEqRule on the outer dm (gamma-level termEq).
      lifted1dmm' : FitsSubst (subTy sigma A ∷ []) (A ∷ gamma) (liftSubst sigma)
      lifted1dmm' =
        subst
          (λ rho -> FitsSubst (subTy sigma A ∷ []) (A ∷ gamma) rho)
          (liftSubstCompKeep sigma)
          (liftFitsOne fits dAσ)
      lifted2dmm' : FitsSubst
        (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) (B ∷ A ∷ gamma)
        (liftSubst (liftSubst sigma))
      lifted2dmm' =
        subst
          (λ rho -> FitsSubst (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) (B ∷ A ∷ gamma) rho)
          (liftSubstCompKeep (liftSubst sigma))
          (liftFits lifted1dmm' dBσ)
      dmm' : Derivable
        (termEq (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ [])
          (subTm (liftSubst (liftSubst sigma)) m)
          (subTm (liftSubst (liftSubst sigma)) m')
          (sigmaBranchTy (subTy (liftSubst sigma) M)))
      dmm' =
        subst
          (λ T ->
            Derivable (termEq (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ [])
              (subTm (liftSubst (liftSubst sigma)) m)
              (subTm (liftSubst (liftSubst sigma)) m') T))
          (sigmaBranchTyLiftComp sigma M)
          (substTmEqRule dm lifted2dmm')

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
      (λ J -> Computable n J)
      (sym resultPath)
      (compESigmaClosed compTransTmClosed compConvTmEqClosed compM compdd dmm' (LexLt-wf _))

  substDerivTmEqCompCF {n} {gamma = gamma} {sigma = sigma}
    (eQtrEq {A = A} {L = L} {l = l} {l' = l'} {p = p} {p' = p'}
      dL dp dBranch dlL dlR dl dcoh dcoh') fits cFits (acc rs) =
    -- Phase F.1e-step1: inlined body of substDerivTmEqCompEQtrEqCF.
    -- F.1b's Acc sub-witness for dp is realized inline at the compdp site below.
    let
      compdp = substDerivTmEqCompCF dp fits cFits
        (rs _ (lift-lex-eq refl (substMeasure-eQtrEq-p< dL dp dBranch dlL dlR dl dcoh dcoh')))
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
      wkCtxWF : CtxWF (subTy (liftSubst sigma) (wkTyBy 1 A) ∷ subTy sigma A ∷ [])
      wkCtxWF = wfCons (wfCons wfNil dAσ) dWkAσ
      compL =
        subst
          (λ T -> HypComputable (suc n) (isType (subTy sigma (tyQtr A) ∷ []) T))
          (cong (λ rho -> subTy rho L) (liftSubstCompKeep sigma))
          (hypTyOpen
            nonemptyNeNil
            (substTyRule dL (liftFitsOne fits dQtrσ))
            -- Phase F.1e-step3 (Scope B): destructure closure Acc, use accRs _ proof<
            (λ rho fits2 cFits2 accD ->
              let
                composedFits = composeOneBinder fits dQtrσ fits2
              in
              subst
                (λ T -> Computable n (isType [] T))
                (sym
                  (cong (λ theta -> subTy rho (subTy theta L)) (liftSubstCompKeep sigma)
                    ∙ subTyComp rho (liftSubst sigma) L))
                (substDerivTyCompCF
                  dL
                  composedFits
                  (fitsToCompFits composedFits)
                  (access accD _ (lift-lex-eq (sym (tyDepth-subTy _ L))
                    (substMeasure-substTyRule< dL (liftFitsOne fits dQtrσ))))))
            (λ rho eta fitsEq2 cFitsEq2 accD ->
              let
                composedFitsEq = composeOneBinderEq fits dQtrσ fitsEq2
              in
              subst
                (λ J -> Computable n J)
                (sym
                  (cong₂ (typeEq [])
                    (cong (λ theta -> subTy rho (subTy theta L)) (liftSubstCompKeep sigma)
                      ∙ subTyComp rho (liftSubst sigma) L)
                    (cong (λ theta -> subTy eta (subTy theta L)) (liftSubstCompKeep sigma)
                      ∙ subTyComp eta (liftSubst sigma) L)))
                (eqSubDerivTyCompCF
                  dL
                  composedFitsEq
                  (fitsEqToCompFitsEq composedFitsEq)
                  (access accD _ (lift-lex-eq (sym (tyDepth-subTy _ L))
                    (substMeasure-substTyRule< dL (liftFitsOne fits dQtrσ)))))))
      compBranchTy =
        subst
          (λ T -> HypComputable (suc n) (isType (subTy sigma A ∷ []) T))
          (cong (λ rho -> subTy rho (qtrBranchTy L)) (liftSubstCompKeep sigma))
          (hypTyOpen
            nonemptyNeNil
            (substTyRule dBranch (liftFitsOne fits dAσ))
            -- Phase F.1e-step3 (Scope B): destructure closure Acc, use accRs _ proof<
            (λ rho fits2 cFits2 accD ->
              let
                composedFits = composeOneBinder fits dAσ fits2
              in
              subst
                (λ T -> Computable n (isType [] T))
                (sym
                  (cong (λ theta -> subTy rho (subTy theta (qtrBranchTy L)))
                    (liftSubstCompKeep sigma)
                    ∙ subTyComp rho (liftSubst sigma) (qtrBranchTy L)))
                (substDerivTyCompCF
                  dBranch
                  composedFits
                  (fitsToCompFits composedFits)
                  (access accD _ (lift-lex-eq (sym (tyDepth-subTy _ (qtrBranchTy L)))
                    (substMeasure-substTyRule< dBranch (liftFitsOne fits dAσ))))))
            (λ rho eta fitsEq2 cFitsEq2 accD ->
              let
                composedFitsEq = composeOneBinderEq fits dAσ fitsEq2
              in
              subst
                (λ J -> Computable n J)
                (sym
                  (cong₂ (typeEq [])
                    (cong (λ theta -> subTy rho (subTy theta (qtrBranchTy L)))
                      (liftSubstCompKeep sigma)
                      ∙ subTyComp rho (liftSubst sigma) (qtrBranchTy L))
                    (cong (λ theta -> subTy eta (subTy theta (qtrBranchTy L)))
                      (liftSubstCompKeep sigma)
                      ∙ subTyComp eta (liftSubst sigma) (qtrBranchTy L))))
                (eqSubDerivTyCompCF
                  dBranch
                  composedFitsEq
                  (fitsEqToCompFitsEq composedFitsEq)
                  (access accD _ (lift-lex-eq (sym (tyDepth-subTy _ (qtrBranchTy L)))
                    (substMeasure-substTyRule< dBranch (liftFitsOne fits dAσ)))))))
      -- Phase F.1e-step2 (Scope A): use rs _ proof< for dlL recursion
      complAssoc = openHypTm1 substDerivTmCompCF eqSubDerivTmCompCF composeCompFits fitsEqToCompFitsEq fits cFits dAσ compBranchTy dlL
        (rs _ (lift-lex-eq refl (substMeasure-eQtrEq-dlL< dL dp dBranch dlL dlR dl dcoh dcoh')))
  
      compl =
        subst
          (λ T ->
            HypComputable (suc n)
              (termEq (subTy sigma A ∷ [])
                (subTm (liftSubst sigma) l)
                (subTm (liftSubst sigma) l')
                T))
          (qtrBranchTyLiftComp sigma L)
          -- Phase F.1e-step2 (Scope A): use rs _ proof< for dl (=dll') recursion
          (openHypTmEq1 substDerivTmEqCompCF eqSubDerivTmEqCompCF fitsToCompFits fitsEqToCompFitsEq
            fits
            dAσ
            complAssoc
            dl
            (rs _ (lift-lex-eq refl (substMeasure-eQtrEq-dll< dL dp dBranch dlL dlR dl dcoh dcoh'))))
  
      compcohAssoc =
        subst
          (λ J -> HypComputable (suc n) J)
          (cong₂
            (hasTy (subTy (liftSubst sigma) (wkTyBy 1 A) ∷ subTy sigma A ∷ []))
            (sym (wkTmLiftSubst (liftSubst sigma) l))
            (qtrBranchTyWk (subTy (liftSubst sigma) L)
              ∙ sym (qtrCohTyLiftComp sigma L)))
          (weakenOneOpenTm (hypTmEqLeft compl) wkCtxWF)

      compcoh =
        subst
          (λ J -> HypComputable (suc n) J)
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
          -- Phase F.1e-step2 (Scope A): use rs _ proof< for dcoh recursion
          (openHypTmEq2
            fits
            dAσ
            dWkAσ
            compcohAssoc
            dcoh
            (rs _ (lift-lex-eq refl (substMeasure-eQtrEq-dcoh< dL dp dBranch dlL dlR dl dcoh dcoh'))))
  
      compcohAssoc' =
        subst
          (λ J -> HypComputable (suc n) J)
          (cong₂
            (hasTy (subTy (liftSubst sigma) (wkTyBy 1 A) ∷ subTy sigma A ∷ []))
            (sym (wkTmLiftSubst (liftSubst sigma) l'))
            (qtrBranchTyWk (subTy (liftSubst sigma) L)
              ∙ sym (qtrCohTyLiftComp sigma L)))
          (weakenOneOpenTm (hypTmEqLeft (compSymTm compl)) wkCtxWF)
  
      compcoh' =
        subst
          (λ J -> HypComputable (suc n) J)
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
          -- Phase F.1e-step2 (Scope A): use rs _ proof< for dcoh' recursion
          (openHypTmEq2
            fits
            dAσ
            dWkAσ
            compcohAssoc'
            dcoh'
            (rs _ (lift-lex-eq refl (substMeasure-eQtrEq-dcoh'< dL dp dBranch dlL dlR dl dcoh dcoh'))))
  
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
      -- Stage 3 v29: extract raw Derivables + <-wellfounded for compEQtrClosed (eQtrEq case).
      dll'Arg = hypCompToDerivable compl
      dcohArg = hypCompToDerivable compcoh
      dcoh'Arg = hypCompToDerivable compcoh'
    in
    subst
      (λ J -> Computable n J)
      (sym resultPath)
      (compEQtrClosed compTransTmClosed compSymTmClosed compConvTmEqClosed
        compL compdp dll'Arg (LexLt-wf _) dcohArg dcoh'Arg (LexLt-wf _))

  substDerivTmEqCompCF {n} {gamma = gamma} {sigma = sigma}
    (cSigma {A = A} {B = B} {M = M} {b = b} {c = c} {m = m} dM dSigma db dc dm) fits cFits (acc rs) =
    let
      compb = substDerivTmCompCF db fits cFits (LexLt-wf _)
      compSigma = substDerivTyCompCF dSigma fits cFits (LexLt-wf _)
      dSigmaσ = compToDerivable compSigma
      tyInv = invertSigmaTy compSigma evalSigma
      compAσ = ClosedSigmaTyInv.sigmaTyCompHead tyInv
      dAσ = compToDerivable compAσ
      dBσ = ClosedSigmaTyInv.sigmaTyFamDeriv tyInv
      compM =
        subst
          (λ T -> HypComputable (suc n) (isType (subTy sigma (tySigma A B) ∷ []) T))
          (cong (λ rho -> subTy rho M) (liftSubstCompKeep sigma))
          (hypTyOpen
            nonemptyNeNil
            (substTyRule dM (liftFitsOne fits dSigmaσ))
            (λ rho fits2 _ accD ->
              subst
                (λ T -> Computable n (isType [] T))
                (sym
                  (cong (λ theta -> subTy rho (subTy theta M)) (liftSubstCompKeep sigma)
                    ∙ subTyComp rho (liftSubst sigma) M))
                (substDerivTyCompCF
                  dM
                  (composeOneBinder fits dSigmaσ fits2) (fitsToCompFits (composeOneBinder fits dSigmaσ fits2)) (LexLt-wf _)))
            (λ rho eta fitsEq2 _ accD ->
              subst
                (λ J -> Computable n J)
                (sym
                  (cong₂ (typeEq [])
                    (cong (λ theta -> subTy rho (subTy theta M)) (liftSubstCompKeep sigma)
                      ∙ subTyComp rho (liftSubst sigma) M)
                    (cong (λ theta -> subTy eta (subTy theta M)) (liftSubstCompKeep sigma)
                      ∙ subTyComp eta (liftSubst sigma) M)))
                (eqSubDerivTyCompCF
                  dM
                  (composeOneBinderEq fits dSigmaσ fitsEq2) (fitsEqToCompFitsEq (composeOneBinderEq fits dSigmaσ fitsEq2)) (LexLt-wf _))))
  
      compcRaw = substDerivTmCompCF dc fits cFits (LexLt-wf _)
      compc =
        subst
          (λ T -> Computable n (hasTy [] (subTm sigma c) T))
          (subTyComp sigma (singleSubst b) B
            ∙ cong (λ rho -> subTy rho B) (sym (singleSubstCompLift sigma b))
            ∙ sym (subTyComp (singleSubst (subTm sigma b)) (liftSubst sigma) B))
          compcRaw

      -- v28 Stage 2: build the body Computable directly via SCC 2 recursion
      -- on the ORIGINAL dm, using sub-Acc via substMeasure-cSigma-m<.
      -- The composition path sigmaCompSubLiftComp gives us:
      --   compSub sigma (sigmaCompSub b c) ≡ compSub (sigmaCompSub b' c') (liftSubst (liftSubst sigma))
      -- Step 1: build the 2-element fits for sigmaCompSub at substituted (B ∷ A ∷ [])
      bodyFits2 : CompFitsBundle n
        (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ [])
        (sigmaCompSub (subTm sigma b) (subTm sigma c))
      bodyFits2 = sigmaCompComputableFitsHelper {A = subTy sigma A} {B = subTy (liftSubst sigma) B} compb compc
      -- Step 2: compose with outer fits to get fits for (B ∷ A ∷ gamma)
      composedFitsTwoBinder :
        FitsSubst [] (B ∷ A ∷ gamma)
          (compSub (sigmaCompSub (subTm sigma b) (subTm sigma c))
                   (liftSubst (liftSubst sigma)))
      composedFitsTwoBinder =
        composeTwoBinders fits dAσ dBσ (fst bodyFits2)
      -- Step 3: transport fits along sigmaCompSubLiftComp
      composedFitsFinal :
        FitsSubst [] (B ∷ A ∷ gamma) (compSub sigma (sigmaCompSub b c))
      composedFitsFinal =
        subst
          (λ rho -> FitsSubst [] (B ∷ A ∷ gamma) rho)
          (sym (sigmaCompSubLiftComp sigma b c))
          composedFitsTwoBinder
      -- Step 4: build CompFits for composedFitsFinal
      composedCFitsFinal : ComputableFits n composedFitsFinal
      composedCFitsFinal = fitsToCompFits composedFitsFinal
      -- Step 5: recursive call on original dm with sub-Acc. The result lives at
      -- context (compSub sigma (sigmaCompSub b c)).
      rawBodyRaw : Computable n
        (hasTy [] (subTm (compSub sigma (sigmaCompSub b c)) m)
          (subTy (compSub sigma (sigmaCompSub b c)) (sigmaBranchTy M)))
      rawBodyRaw =
        substDerivTmCompCF dm composedFitsFinal composedCFitsFinal
          (LexLt-wf _)
      -- Step 6: transport to the (sigmaCompSub b' c') (liftSubst (liftSubst sigma)) form.
      rawBody : Computable n
        (hasTy [] (subTm (sigmaCompSub (subTm sigma b) (subTm sigma c))
                    (subTm (liftSubst (liftSubst sigma)) m))
          (subTy (sigmaCompSub (subTm sigma b) (subTm sigma c))
            (sigmaBranchTy (subTy (liftSubst sigma) M))))
      rawBody =
        subst
          (λ J -> Computable n J)
          (cong₂ (hasTy [])
            (sym (subTmComp sigma (sigmaCompSub b c) m)
              ∙ subTmComp sigma (sigmaCompSub b c) m  -- identity: just to start the chain
              -- Actually: we want compSub sigma (sigmaCompSub b c) → sigmaCompSub b' c' composed with liftSubst (liftSubst sigma)
              -- Use cong directly on the substitution equality
              ∙ cong (λ rho -> subTm rho m) (sigmaCompSubLiftComp sigma b c)
              ∙ sym (subTmComp (sigmaCompSub (subTm sigma b) (subTm sigma c))
                  (liftSubst (liftSubst sigma)) m))
            (cong (λ rho -> subTy rho (sigmaBranchTy M)) (sigmaCompSubLiftComp sigma b c)
              ∙ sym (subTyComp (sigmaCompSub (subTm sigma b) (subTm sigma c))
                  (liftSubst (liftSubst sigma)) (sigmaBranchTy M))
              ∙ cong (subTy (sigmaCompSub (subTm sigma b) (subTm sigma c)))
                  (sigmaBranchTyLiftComp sigma M)))
          rawBodyRaw

      -- Substituted dm for dEq construction (not used recursively, so derivSize bound not needed)
      liftedOne : FitsSubst (subTy sigma A ∷ []) (A ∷ gamma) (liftSubst sigma)
      liftedOne =
        subst
          (λ rho -> FitsSubst (subTy sigma A ∷ []) (A ∷ gamma) rho)
          (liftSubstCompKeep sigma)
          (liftFitsOne fits dAσ)
      liftedTwo : FitsSubst
        (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) (B ∷ A ∷ gamma)
        (liftSubst (liftSubst sigma))
      liftedTwo =
        subst
          (λ rho -> FitsSubst (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) (B ∷ A ∷ gamma) rho)
          (liftSubstCompKeep (liftSubst sigma))
          (liftFits liftedOne dBσ)
      dmSub : Derivable
        (hasTy (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ [])
          (subTm (liftSubst (liftSubst sigma)) m)
          (sigmaBranchTy (subTy (liftSubst sigma) M)))
      dmSub =
        subst
          (λ T ->
            Derivable (hasTy (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ [])
              (subTm (liftSubst (liftSubst sigma)) m) T))
          (sigmaBranchTyLiftComp sigma M)
          (substTmRule dm liftedTwo)

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
      (λ J -> Computable n J)
      (sym resultPath)
      (compCSigmaClosed compM compb compc dmSub rawBody)
  substDerivTmEqCompCF {n} (iEqEq d) fits cFits (acc rs) =
    compReflTm (compIEqClosed (compTmEqLeft (substDerivTmEqCompCF d fits cFits (LexLt-wf _))))
  substDerivTmEqCompCF {n} (eEqStar dp dA da db) fits cFits (acc rs) =
    compEEqClosed (substDerivTmCompCF dp fits cFits (LexLt-wf _))
  substDerivTmEqCompCF {n} (cEq dp dA da db) fits cFits (acc rs) =
    compCEqClosed (substDerivTmCompCF dp fits cFits (LexLt-wf _))
  substDerivTmEqCompCF {n} (iQtrEq da db) fits cFits (acc rs) =
    compIQtrEqClosed
      (substDerivTmCompCF da fits cFits (LexLt-wf _))
      (substDerivTmCompCF db fits cFits (LexLt-wf _))
  substDerivTmEqCompCF {n} {gamma = gamma} {sigma = sigma}
    (cQtr {A = A} {L = L} {a = a} {l = l}
      dL da dBranch dl dcoh) fits cFits (acc rs) =
    -- Phase F.2 (cQtr): inlined body of substDerivTmEqCompCQtr.
    let
      compa = substDerivTmCompCF da fits cFits
        (rs _ (lift-lex-eq refl (substMeasure-cQtr-a< dL da dBranch dl dcoh)))
      compAσ = compTmToCompTy compa
      dAσ = compToDerivable compAσ
      dQtrσ = compToDerivable (compFQtrClosed compAσ)
      dWkAσ =
        subst
          (λ T -> Derivable (isType (subTy sigma A ∷ []) T))
          (sym (wkTyLiftSubst sigma A))
          (weakenTy dAσ (wfCons wfNil dAσ))
      wkCtxWF : CtxWF (subTy (liftSubst sigma) (wkTyBy 1 A) ∷ subTy sigma A ∷ [])
      wkCtxWF = wfCons (wfCons wfNil dAσ) dWkAσ
      compL =
        subst
          (λ T -> HypComputable (suc n) (isType (subTy sigma (tyQtr A) ∷ []) T))
          (cong (λ rho -> subTy rho L) (liftSubstCompKeep sigma))
          (hypTyOpen
            nonemptyNeNil
            (substTyRule dL (liftFitsOne fits dQtrσ))
            -- Phase F.2 (Scope B): destructure closure Acc, use accRs _ proof<
            (λ rho fits2 _ accD ->
              subst
                (λ T -> Computable n (isType [] T))
                (sym
                  (cong (λ theta -> subTy rho (subTy theta L)) (liftSubstCompKeep sigma)
                    ∙ subTyComp rho (liftSubst sigma) L))
                (substDerivTyCompCF
                  dL
                  (composeOneBinder fits dQtrσ fits2) (fitsToCompFits (composeOneBinder fits dQtrσ fits2))
                  (access accD _ (lift-lex-eq (sym (tyDepth-subTy _ L))
                    (substMeasure-substTyRule< dL (liftFitsOne fits dQtrσ))))))
            (λ rho eta fitsEq2 _ accD ->
              subst
                (λ J -> Computable n J)
                (sym
                  (cong₂ (typeEq [])
                    (cong (λ theta -> subTy rho (subTy theta L)) (liftSubstCompKeep sigma)
                      ∙ subTyComp rho (liftSubst sigma) L)
                    (cong (λ theta -> subTy eta (subTy theta L)) (liftSubstCompKeep sigma)
                      ∙ subTyComp eta (liftSubst sigma) L)))
                (eqSubDerivTyCompCF
                  dL
                  (composeOneBinderEq fits dQtrσ fitsEq2) (fitsEqToCompFitsEq (composeOneBinderEq fits dQtrσ fitsEq2))
                  (access accD _ (lift-lex-eq (sym (tyDepth-subTy _ L))
                    (substMeasure-substTyRule< dL (liftFitsOne fits dQtrσ)))))))
      compBranchTy =
        subst
          (λ T -> HypComputable (suc n) (isType (subTy sigma A ∷ []) T))
          (cong (λ rho -> subTy rho (qtrBranchTy L)) (liftSubstCompKeep sigma))
          (hypTyOpen
            nonemptyNeNil
            (substTyRule dBranch (liftFitsOne fits dAσ))
            -- Phase F.2 (Scope B): destructure closure Acc, use accRs _ proof<
            (λ rho fits2 _ accD ->
              subst
                (λ T -> Computable n (isType [] T))
                (sym
                  (cong (λ theta -> subTy rho (subTy theta (qtrBranchTy L)))
                    (liftSubstCompKeep sigma)
                    ∙ subTyComp rho (liftSubst sigma) (qtrBranchTy L)))
                (substDerivTyCompCF
                  dBranch
                  (composeOneBinder fits dAσ fits2) (fitsToCompFits (composeOneBinder fits dAσ fits2))
                  (access accD _ (lift-lex-eq (sym (tyDepth-subTy _ (qtrBranchTy L)))
                    (substMeasure-substTyRule< dBranch (liftFitsOne fits dAσ))))))
            (λ rho eta fitsEq2 _ accD ->
              subst
                (λ J -> Computable n J)
                (sym
                  (cong₂ (typeEq [])
                    (cong (λ theta -> subTy rho (subTy theta (qtrBranchTy L)))
                      (liftSubstCompKeep sigma)
                      ∙ subTyComp rho (liftSubst sigma) (qtrBranchTy L))
                    (cong (λ theta -> subTy eta (subTy theta (qtrBranchTy L)))
                      (liftSubstCompKeep sigma)
                      ∙ subTyComp eta (liftSubst sigma) (qtrBranchTy L))))
                (eqSubDerivTyCompCF
                  dBranch
                  (composeOneBinderEq fits dAσ fitsEq2) (fitsEqToCompFitsEq (composeOneBinderEq fits dAσ fitsEq2))
                  (access accD _ (lift-lex-eq (sym (tyDepth-subTy _ (qtrBranchTy L)))
                    (substMeasure-substTyRule< dBranch (liftFitsOne fits dAσ)))))))
  
      -- Build dBranchSub and dlSub for the new compCQtrClosed signature.
      -- liftFitsOne gives consSubst form; transport the result of substTyRule directly.
      liftedOneARaw : FitsSubst (subTy sigma A ∷ []) (A ∷ gamma)
        (consSubst (var zero) (compSub (keepSubstBy 1) sigma))
      liftedOneARaw = liftFitsOne fits dAσ
      dBranchSub : Derivable
        (isType (subTy sigma A ∷ []) (qtrBranchTy (subTy (liftSubst sigma) L)))
      dBranchSub =
        subst
          (λ T -> Derivable (isType (subTy sigma A ∷ []) T))
          (cong (λ rho -> subTy rho (qtrBranchTy L)) (liftSubstCompKeep sigma)
            ∙ qtrBranchTyLiftComp sigma L)
          (substTyRule dBranch liftedOneARaw)
      dlSub : Derivable
        (hasTy (subTy sigma A ∷ []) (subTm (liftSubst sigma) l)
          (qtrBranchTy (subTy (liftSubst sigma) L)))
      dlSub =
        subst
          (λ J -> Derivable J)
          (cong₂
            (hasTy (subTy sigma A ∷ []))
            (cong (λ rho -> subTm rho l) (liftSubstCompKeep sigma))
            (cong (λ rho -> subTy rho (qtrBranchTy L)) (liftSubstCompKeep sigma)
              ∙ qtrBranchTyLiftComp sigma L))
          (substTmRule dl liftedOneARaw)
      -- v28 Stage 2: build rawBody via SCC 2 recursion on original dl with sub-Acc
      -- We need: Computable n (hasTy [] (subTm (qtrCompSub a') (subTm (liftSubst sigma) l))
      --                           (subTy (qtrCompSub a') (qtrBranchTy (subTy (liftSubst sigma) L))))
      -- where a' = subTm sigma a. By qtrCompSubLiftComp: compSub sigma (qtrCompSub a) ≡ compSub (qtrCompSub a') (liftSubst sigma)
      lBodyFits : CompFitsBundle n (subTy sigma A ∷ []) (qtrCompSub (subTm sigma a))
      lBodyFits = qtrCompComputableFitsHelper {A = subTy sigma A} compa
      composedFitsL :
        FitsSubst [] (A ∷ gamma)
          (compSub (qtrCompSub (subTm sigma a)) (liftSubst sigma))
      composedFitsL = composeOneBinder fits dAσ (fst lBodyFits)
      composedFitsLFinal :
        FitsSubst [] (A ∷ gamma) (compSub sigma (qtrCompSub a))
      composedFitsLFinal =
        subst
          (λ rho -> FitsSubst [] (A ∷ gamma) rho)
          (sym (qtrCompSubLiftComp sigma a))
          composedFitsL
      composedCFitsLFinal : ComputableFits n composedFitsLFinal
      composedCFitsLFinal = fitsToCompFits composedFitsLFinal
      rawBodyRaw : Computable n
        (hasTy [] (subTm (compSub sigma (qtrCompSub a)) l)
          (subTy (compSub sigma (qtrCompSub a)) (qtrBranchTy L)))
      rawBodyRaw =
        -- Phase F.2 (Scope A): use rs _ proof< for dl recursion
        substDerivTmCompCF dl composedFitsLFinal composedCFitsLFinal
          (rs _ (lift-lex-eq refl (substMeasure-cQtr-l< dL da dBranch dl dcoh)))
      rawBody : Computable n
        (hasTy [] (subTm (qtrCompSub (subTm sigma a)) (subTm (liftSubst sigma) l))
          (subTy (qtrCompSub (subTm sigma a)) (qtrBranchTy (subTy (liftSubst sigma) L))))
      rawBody =
        subst
          (λ J -> Computable n J)
          (cong₂ (hasTy [])
            (cong (λ rho -> subTm rho l) (qtrCompSubLiftComp sigma a)
              ∙ sym (subTmComp (qtrCompSub (subTm sigma a)) (liftSubst sigma) l))
            (cong (λ rho -> subTy rho (qtrBranchTy L)) (qtrCompSubLiftComp sigma a)
              ∙ sym (subTyComp (qtrCompSub (subTm sigma a)) (liftSubst sigma) (qtrBranchTy L))
              ∙ cong (subTy (qtrCompSub (subTm sigma a))) (qtrBranchTyLiftComp sigma L)))
          rawBodyRaw

      -- compcoh (coherence) computation unchanged — still uses openHypTmEq2 + weakenOneOpenTm
      -- This is unchanged because we're not rewriting the coh HypComputable in Stage 2
      -- (that's for Stage 3 when we rewrite compEQtrClosed/compCQtrClosed coh path).
      complForCoh =
        subst
          (λ T ->
            HypComputable (suc n)
              (hasTy (subTy sigma A ∷ [])
                (subTm (liftSubst sigma) l)
                T))
          (qtrBranchTyLiftComp sigma L)
          -- Phase F.2 (Scope A): use rs _ proof< for dl recursion
          (openHypTm1 substDerivTmCompCF eqSubDerivTmCompCF composeCompFits fitsEqToCompFitsEq
            fits
            (fitsToCompFits fits)
            dAσ
            compBranchTy
            dl
            (rs _ (lift-lex-eq refl (substMeasure-cQtr-l< dL da dBranch dl dcoh))))

      compcohAssoc =
        subst
          (λ J -> HypComputable (suc n) J)
          (cong₂
            (hasTy (subTy (liftSubst sigma) (wkTyBy 1 A) ∷ subTy sigma A ∷ []))
            (sym (wkTmLiftSubst (liftSubst sigma) l))
            (qtrBranchTyWk (subTy (liftSubst sigma) L)
              ∙ sym (qtrCohTyLiftComp sigma L)))
          (weakenOneOpenTm complForCoh wkCtxWF)

      compcoh =
        subst
          (λ J -> HypComputable (suc n) J)
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
          -- Phase F.2 (Scope A): use rs _ proof< for dcoh recursion
          (openHypTmEq2
            fits
            dAσ
            dWkAσ
            compcohAssoc
            dcoh
            (rs _ (lift-lex-eq refl (substMeasure-cQtr-dcoh< dL da dBranch dl dcoh))))

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
      (λ J -> Computable n J)
      (sym resultPath)
      (compCQtrClosed compL compa dBranchSub dlSub rawBody compcoh)


  substDerivTmEqCompCF {n} {sigma = sigma} (weakenTmEq {delta = delta} {t = t} {u = u} {A = A} d wf) fits cFits (acc rs) =
    subst
      (λ J -> Computable n J)
      (cong₃ (termEq [])
        (sym (subTmWkBy sigma (length delta) t))
        (sym (subTmWkBy sigma (length delta) u))
        (sym (subTyWkBy sigma (length delta) A)))
      (substDerivTmEqCompCF d (dropFits delta fits) (dropCompFits delta cFits) (LexLt-wf _))
  substDerivTmEqCompCF {n} {sigma = sigma} (substTmEqRule {sigma = sigma'} {t = t} {u = u} {A = A} d fits') fits cFits (acc rs) =
    let
      composedFits = composeFits fits fits'
      composedCFits = composeCompFits fits cFits fits' (iTop (fitsSubstCtxWF fits')) (LexLt-wf _)
    in
    subst
      (λ J -> Computable n J)
      (cong₃ (termEq [])
        (sym (subTmComp sigma sigma' t))
        (sym (subTmComp sigma sigma' u))
        (sym (subTyComp sigma sigma' A)))
      (substDerivTmEqCompCF d composedFits composedCFits (LexLt-wf _))
  substDerivTmEqCompCF {n} {sigma = sigma}
    (eqSubTmRule {sigma = sigma'} {tau = tau'} {t = t} {A = A} d fitsEq') fits cFits _ =
    let
      composedFitsEq = composeFitsEq fits fitsEq'
      composedCFitsEq =
        composeCompFitsEq fits cFits fitsEq'
          (reflTm (iTop (fitsEqSubstCtxWF fitsEq')))
          (LexLt-wf _)
    in
    subst
      (λ J -> Computable n J)
      (cong₃ (termEq [])
        (sym (subTmComp sigma sigma' t))
        (sym (subTmComp sigma tau' t))
        (sym (subTyComp sigma sigma' A)))
      (eqSubDerivTmCompCF d composedFitsEq composedCFitsEq (LexLt-wf _))
  substDerivTmEqCompCF {n} {sigma = sigma}
    (eqSubTmEqRule {sigma = sigma'} {tau = tau'} {t = t} {u = u} {A = A} d fitsEq') fits cFits _ =
    let
      composedFitsEq = composeFitsEq fits fitsEq'
      composedCFitsEq =
        composeCompFitsEq fits cFits fitsEq'
          (reflTm (iTop (fitsEqSubstCtxWF fitsEq')))
          (LexLt-wf _)
    in
    subst
      (λ J -> Computable n J)
      (cong₃ (termEq [])
        (sym (subTmComp sigma sigma' t))
        (sym (subTmComp sigma tau' u))
        (sym (subTyComp sigma sigma' A)))
      (eqSubDerivTmEqCompCF d composedFitsEq composedCFitsEq (LexLt-wf _))

  -- Closed-context (gamma=[]) variant of substDerivTmEqComp.
  -- Single catch-all clause (see substDerivTmCompClosed for explanation).
  eqSubDerivTyCompCF {n} (fTop wf) fitsEq cFitsEq _ = compReflTy compFTopClosed
  eqSubDerivTyCompCF {n} {gamma = gamma} {sigma = sigma} {tau = tau}
    (fSigma {A = A} {B = B} dA dB) fitsEq cFitsEq (acc rs) =
    let
      sigmaFits = fitsEqSubstLeft fitsEq
      compAA' = eqSubDerivTyCompCF dA fitsEq cFitsEq (LexLt-wf _)
      compA = compTyEqLeft compAA'
      compA' = compTyEqRightClosed compAA'
      dAσ = substTyRule dA sigmaFits
      compB =
        subst
          (λ T -> HypComputable (suc n) (isType (subTy sigma A ∷ []) T))
          (cong (λ rho -> subTy rho B) (liftSubstCompKeepNR sigma))
          (hypTyOpen
            nonemptyNeNil
            (substTyRule dB (liftFitsOneNR sigmaFits dAσ))
            (λ rho fits2 cFits2 accD ->
              let
                composedFits = composeOneBinderNR sigmaFits dAσ fits2
              in
              subst
                (λ T -> Computable n (isType [] T))
                (sym
                  (cong (λ theta -> subTy rho (subTy theta B)) (liftSubstCompKeepNR sigma)
                    ∙ subTyComp rho (liftSubst sigma) B))
                (substDerivTyCompCF
                  dB
                  composedFits
                  (fitsToCompFits composedFits) (LexLt-wf _)))
            (λ rho eta fitsEq2 cFitsEq2 accD ->
              let
                composedFitsEq = composeOneBinderEqNR sigmaFits dAσ fitsEq2
              in
              subst
                (λ J -> Computable n J)
                (sym
                  (cong₂ (typeEq [])
                    (cong (λ theta -> subTy rho (subTy theta B)) (liftSubstCompKeepNR sigma)
                      ∙ subTyComp rho (liftSubst sigma) B)
                    (cong (λ theta -> subTy eta (subTy theta B)) (liftSubstCompKeepNR sigma)
                      ∙ subTyComp eta (liftSubst sigma) B)))
                (eqSubDerivTyCompCF
                  dB
                  composedFitsEq
                  (fitsEqToCompFitsEq composedFitsEq) (LexLt-wf _))))
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
          (λ rho fits2 _ accD ->
            let
              composedFitsEq = composeFitsEq fits2 liftedEq
            in
            subst
              (λ J -> Computable n J)
              (sym
                (cong₂ (typeEq [])
                  (subTyComp rho (liftSubst sigma) B)
                  (subTyComp rho (liftSubst tau) B)))
              (eqSubDerivTyCompCF
                dB
                composedFitsEq
                (fitsEqToCompFitsEq composedFitsEq) (LexLt-wf _)))
          (λ rho eta fitsEq2 _ accD ->
            let
              composedFitsEq = composeEqFitsEq fitsEq2 liftedEq
            in
            subst
              (λ J -> Computable n J)
              (sym
                (cong₂ (typeEq [])
                  (subTyComp rho (liftSubst sigma) B)
                  (subTyComp eta (liftSubst tau) B)))
              (eqSubDerivTyCompCF
                dB
                composedFitsEq
                (fitsEqToCompFitsEq composedFitsEq) (LexLt-wf _)))
      compSigmaA = compFSigmaClosed compA (hypCompToDerivable (hypTyEqLeft compBD))
      compSigmaA' = compFSigmaClosed compA' (hypCompToDerivable (compTransportFamilyTy compAA' (hypTyEqRight compBD)))
    in
    compTyEqClosedSigma
      (fSigmaEq
        (compToDerivable compAA')
        (hypCompToDerivable (hypTyEqLeft compBD))
        (hypCompToDerivable compBD))
      compSigmaA
      compSigmaA'
      evalSigma
      evalSigma
      compAA'
      (hypCompToDerivable compBD)
  eqSubDerivTyCompCF {n} (fEq dA da db) fitsEq cFitsEq (acc rs) =
    let
      compAA' = eqSubDerivTyCompCF dA fitsEq cFitsEq (LexLt-wf _)
      compac = eqSubDerivTmCompCF da fitsEq cFitsEq (LexLt-wf _)
      compbd = eqSubDerivTmCompCF db fitsEq cFitsEq (LexLt-wf _)
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
  eqSubDerivTyCompCF {n} (fQtr dA) fitsEq cFitsEq (acc rs) =
    let
      compAA' = eqSubDerivTyCompCF dA fitsEq cFitsEq (LexLt-wf _)
    in
    compTyEqClosedQtr
      (fQtrEq (compToDerivable compAA'))
      (compFQtrClosed (compTyEqLeft compAA'))
      (compFQtrClosed (compTyEqRightClosed compAA'))
      evalQtr
      evalQtr
      compAA'
  eqSubDerivTyCompCF {n} {sigma = sigma} {tau = tau}
    (weakenTy {delta = delta} {A = A} d wf) fitsEq cFitsEq (acc rs) =
    subst
      (λ J -> Computable n J)
      (cong₂ (typeEq [])
        (sym (subTyWkBy sigma (length delta) A))
        (sym (subTyWkBy tau (length delta) A)))
      (eqSubDerivTyCompCF d (dropFitsEq delta fitsEq) (dropCompFitsEq delta cFitsEq) (LexLt-wf _))
  eqSubDerivTyCompCF {n} {sigma = sigma} {tau = tau}
    (substTyRule {sigma = sigma'} {A = A} d fits') fitsEq cFitsEq (acc rs) =
    let
      composedFitsEq = composeEqFits fitsEq fits'
      composedCFitsEq = composeCompEqFits fitsEq cFitsEq fits' (iTop (fitsSubstCtxWF fits')) (LexLt-wf _)
    in
    subst
      (λ J -> Computable n J)
      (cong₂ (typeEq [])
        (sym (subTyComp sigma sigma' A))
        (sym (subTyComp tau sigma' A)))
      (eqSubDerivTyCompCF d composedFitsEq composedCFitsEq (LexLt-wf _))
  
  eqSubDerivTyEqCompCF {n} (reflTy d) fitsEq cFitsEq (acc rs) =
    eqSubDerivTyCompCF d fitsEq (fitsEqToCompFitsEq fitsEq) (LexLt-wf _)
  eqSubDerivTyEqCompCF {n} (symTy d dA) fitsEq cFitsEq (acc rs) =
    let
      tauFits = fitsEqSubstRight (derivToCtxWF dA) fitsEq
    in
    compTransTyClosed
      (eqSubDerivTyCompCF dA fitsEq (fitsEqToCompFitsEq fitsEq) (LexLt-wf _))
      (compSymTyClosed (substDerivTyEqCompCF d tauFits (fitsToCompFits tauFits) (LexLt-wf _)))
  eqSubDerivTyEqCompCF {n} (transTy d₁ d₂) fitsEq cFitsEq (acc rs) =
    let
      sigmaFits = fitsEqSubstLeft fitsEq
    in
    compTransTyClosed
      (substDerivTyEqCompCF d₁ sigmaFits (fitsToCompFits sigmaFits) (LexLt-wf _))
      (eqSubDerivTyEqCompCF d₂ fitsEq (fitsEqToCompFitsEq fitsEq) (LexLt-wf _))
  eqSubDerivTyEqCompCF {n} {gamma = gamma} {sigma = sigma} {tau = tau}
    (fSigmaEq {A = A} {B = B} {D = D} dAC dB dBD) fitsEq cFitsEq (acc rs) =
    let
      sigmaFits = fitsEqSubstLeft fitsEq
      compAC = eqSubDerivTyEqCompCF dAC fitsEq (fitsEqToCompFitsEq fitsEq) (LexLt-wf _)
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
          (subst
            (λ T -> HypComputable (suc n) (isType (subTy sigma A ∷ []) T))
            (cong (λ rho -> subTy rho B) (liftSubstCompKeep sigma))
            (hypTyOpen
              nonemptyNeNil
              (substTyRule dB (liftFitsOne sigmaFits dAσ))
              (λ rho fits2 _ accD ->
                subst
                  (λ T -> Computable n (isType [] T))
                  (sym
                    (cong (λ theta -> subTy rho (subTy theta B)) (liftSubstCompKeep sigma)
                      ∙ subTyComp rho (liftSubst sigma) B))
                  (substDerivTyCompCF
                    dB
                    (composeOneBinder sigmaFits dAσ fits2) (fitsToCompFits (composeOneBinder sigmaFits dAσ fits2)) (LexLt-wf _)))
              (λ rho eta fitsEq2 _ accD ->
                subst
                  (λ J -> Computable n J)
                  (sym
                    (cong₂ (typeEq [])
                      (cong (λ theta -> subTy rho (subTy theta B)) (liftSubstCompKeep sigma)
                        ∙ subTyComp rho (liftSubst sigma) B)
                      (cong (λ theta -> subTy eta (subTy theta B)) (liftSubstCompKeep sigma)
                        ∙ subTyComp eta (liftSubst sigma) B)))
                  (eqSubDerivTyCompCF
                    dB
                    (composeOneBinderEq sigmaFits dAσ fitsEq2) (fitsEqToCompFitsEq (composeOneBinderEq sigmaFits dAσ fitsEq2)) (LexLt-wf _)))))
          (λ rho fits2 _ accD ->
            let
              composedFitsEq = composeFitsEq fits2 liftedEq
            in
            subst
              (λ J -> Computable n J)
              (sym
                (cong₂ (typeEq [])
                  (subTyComp rho (liftSubst sigma) B)
                  (subTyComp rho (liftSubst tau) D)))
              (eqSubDerivTyEqCompCF
                dBD
                composedFitsEq (fitsEqToCompFitsEq composedFitsEq) (LexLt-wf _)))
          (λ rho eta fitsEq2 _ accD ->
            let
              composedFitsEq = composeEqFitsEq fitsEq2 liftedEq
            in
            subst
              (λ J -> Computable n J)
              (sym
                (cong₂ (typeEq [])
                  (subTyComp rho (liftSubst sigma) B)
                  (subTyComp eta (liftSubst tau) D)))
              (eqSubDerivTyEqCompCF
                dBD
                composedFitsEq (fitsEqToCompFitsEq composedFitsEq) (LexLt-wf _)))
      compSigmaA = compFSigmaClosed compA (hypCompToDerivable (hypTyEqLeft compBD))
      compSigmaC = compFSigmaClosed compC (hypCompToDerivable (compTransportFamilyTy compAC (hypTyEqRight compBD)))
    in
    compTyEqClosedSigma
      (fSigmaEq (compToDerivable compAC) (hypCompToDerivable (hypTyEqLeft compBD)) (hypCompToDerivable compBD))
      compSigmaA
      compSigmaC
      evalSigma
      evalSigma
      compAC
      (hypCompToDerivable compBD)
  eqSubDerivTyEqCompCF {n} {sigma = sigma} {tau = tau}
    (weakenTyEq {delta = delta} {A = A} {B = B} d wf) fitsEq cFitsEq (acc rs) =
    subst
      (λ J -> Computable n J)
      (cong₂ (typeEq [])
        (sym (subTyWkBy sigma (length delta) A))
        (sym (subTyWkBy tau (length delta) B)))
      (eqSubDerivTyEqCompCF d (dropFitsEq delta fitsEq) (fitsEqToCompFitsEq (dropFitsEq delta fitsEq)) (LexLt-wf _))
  eqSubDerivTyEqCompCF {n} {sigma = sigma} {tau = tau}
    (substTyEqRule {sigma = sigma'} {A = A} {B = B} d fits') fitsEq cFitsEq (acc rs) =
    let
      composedFitsEq = composeEqFits fitsEq fits'
    in
    subst
      (λ J -> Computable n J)
      (cong₂ (typeEq [])
        (sym (subTyComp sigma sigma' A))
        (sym (subTyComp tau sigma' B)))
      (eqSubDerivTyEqCompCF d composedFitsEq (fitsEqToCompFitsEq composedFitsEq) (LexLt-wf _))
  eqSubDerivTyEqCompCF {n} {sigma = sigma} {tau = tau}
    (eqSubTyRule {sigma = sigma'} {tau = tau'} {A = A} d fitsEq') fitsEq cFitsEq (acc rs) =
    let
      composedFitsEq = composeEqFitsEq fitsEq fitsEq'
    in
    subst
      (λ J -> Computable n J)
      (cong₂ (typeEq [])
        (sym (subTyComp sigma sigma' A))
        (sym (subTyComp tau tau' A)))
      (eqSubDerivTyCompCF d composedFitsEq (fitsEqToCompFitsEq composedFitsEq) (LexLt-wf _))
  eqSubDerivTyEqCompCF {n} {sigma = sigma} {tau = tau}
    (eqSubTyEqRule {sigma = sigma'} {tau = tau'} {A = A} {B = B} d fitsEq') fitsEq cFitsEq (acc rs) =
    let
      composedFitsEq = composeEqFitsEq fitsEq fitsEq'
    in
    subst
      (λ J -> Computable n J)
      (cong₂ (typeEq [])
        (sym (subTyComp sigma sigma' A))
        (sym (subTyComp tau tau' B)))
      (eqSubDerivTyEqCompCF d composedFitsEq (fitsEqToCompFitsEq composedFitsEq) (LexLt-wf _))
  eqSubDerivTyEqCompCF {n} (fEqEq dAC dac dbd) fitsEq cFitsEq (acc rs) =
    let
      compAC = eqSubDerivTyEqCompCF dAC fitsEq (fitsEqToCompFitsEq fitsEq) (LexLt-wf _)
      compac = eqSubDerivTmEqCompCF dac fitsEq (fitsEqToCompFitsEq fitsEq) (LexLt-wf _)
      compbd = eqSubDerivTmEqCompCF dbd fitsEq (fitsEqToCompFitsEq fitsEq) (LexLt-wf _)
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
  eqSubDerivTyEqCompCF {n} (fQtrEq dAB) fitsEq cFitsEq (acc rs) =
    let
      compAB = eqSubDerivTyEqCompCF dAB fitsEq (fitsEqToCompFitsEq fitsEq) (LexLt-wf _)
    in
    compTyEqClosedQtr
      (fQtrEq (compToDerivable compAB))
      (compFQtrClosed (compTyEqLeft compAB))
      (compFQtrClosed (compTyEqRightClosed compAB))
      evalQtr
      evalQtr
      compAB
  

  eqSubDerivTmCompCF {n} (varStar {delta = delta} {A = A} wf dA) fitsEq cFitsEq _ =
    lookupCompFitsEq {delta = delta} {A = A} cFitsEq
  eqSubDerivTmCompCF {n} (iTop wf) fitsEq cFitsEq _ =
    compReflTm compITopClosed
  eqSubDerivTmCompCF {n} {sigma = sigma} {tau = tau}
    (iSigma {a = a} {b = b} {A = A} {B = B} da db dSigma) fitsEq cFitsEq (acc rs) =
    let
      sigmaFits = fitsEqSubstLeft fitsEq
      compac = eqSubDerivTmCompCF da fitsEq cFitsEq (LexLt-wf _)
      compSigma = substDerivTyCompCF dSigma sigmaFits (fitsToCompFits sigmaFits) (LexLt-wf _)
      tyInv = invertSigmaTy compSigma evalSigma
      compAσ = ClosedSigmaTyInv.sigmaTyCompHead tyInv
      compBσ = sigmaTyFamHypClosed compSigma
      compbdRaw = eqSubDerivTmCompCF db fitsEq cFitsEq (LexLt-wf _)
      compbd =
        subst
          (λ T -> Computable n (termEq [] (subTm sigma b) (subTm tau b) T))
          (subTyComp sigma (singleSubst a) B
            ∙ cong (λ rho -> subTy rho B) (sym (singleSubstCompLift sigma a))
            ∙ sym (subTyComp (singleSubst (subTm sigma a)) (liftSubst sigma) B))
          compbdRaw
      compa = compTmEqLeft compac
      compcA = compTmEqRightClosed compac
      compb = compTmEqLeft compbd
      compdA = compTmEqRightClosed compbd
      compd =
        compConvTmClosed compdA
          (compSingleEqSubstTyClosed compBσ compac
            (rs _ (lex-fst
              (subst (λ m → m < tyDepth (tySigma A B))
                (sym (tyDepth-subTy (liftSubst sigma) B))
                (tyDepth-snd<Sigma A B)))))
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
  eqSubDerivTmCompCF {n} (iEq da) fitsEq cFitsEq (acc rs) =
    compReflTm (compIEqClosed (compTmEqLeft (eqSubDerivTmCompCF da fitsEq cFitsEq (LexLt-wf _))))
  eqSubDerivTmCompCF {n} (iQtr da) fitsEq cFitsEq (acc rs) =
    let
      compab = eqSubDerivTmCompCF da fitsEq cFitsEq (LexLt-wf _)
    in
    compIQtrEqClosed (compTmEqLeft compab) (compTmEqRightClosed compab)
  eqSubDerivTmCompCF {n} {gamma = gamma} {sigma = sigma} {tau = tau}
    (eSigma {A = A} {B = B} {M = M} {d = d} {m = m} dM dd dm) fitsEq cFitsEq (acc rs) =
    let
      sigmaFits = fitsEqSubstLeft fitsEq
      compdd = eqSubDerivTmCompCF dd fitsEq cFitsEq (LexLt-wf _)
      compSigma = compTmToCompTy (compTmEqLeft compdd)
      dSigmaσ = compToDerivable compSigma
      compM =
        subst
          (λ T -> HypComputable (suc n) (isType (subTy sigma (tySigma A B) ∷ []) T))
          (cong (λ rho -> subTy rho M) (liftSubstCompKeep sigma))
          (hypTyOpen
            nonemptyNeNil
            (substTyRule dM (liftFitsOne sigmaFits dSigmaσ))
            (λ rho fits2 _ accD ->
              subst
                (λ T -> Computable n (isType [] T))
                (sym
                  (cong (λ theta -> subTy rho (subTy theta M)) (liftSubstCompKeep sigma)
                    ∙ subTyComp rho (liftSubst sigma) M))
                (substDerivTyCompCF
                  dM
                  (composeOneBinder sigmaFits dSigmaσ fits2) (fitsToCompFits (composeOneBinder sigmaFits dSigmaσ fits2)) (LexLt-wf _)))
            (λ rho eta fitsEq2 _ accD ->
              subst
                (λ J -> Computable n J)
                (sym
                  (cong₂ (typeEq [])
                    (cong (λ theta -> subTy rho (subTy theta M)) (liftSubstCompKeep sigma)
                      ∙ subTyComp rho (liftSubst sigma) M)
                    (cong (λ theta -> subTy eta (subTy theta M)) (liftSubstCompKeep sigma)
                      ∙ subTyComp eta (liftSubst sigma) M)))
                (eqSubDerivTyCompCF
                  dM
                  (composeOneBinderEq sigmaFits dSigmaσ fitsEq2) (fitsEqToCompFitsEq (composeOneBinderEq sigmaFits dSigmaσ fitsEq2)) (LexLt-wf _))))
  
      tyInv = invertSigmaTy compSigma evalSigma
      compAσ = ClosedSigmaTyInv.sigmaTyCompHead tyInv
      dAσ = compToDerivable compAσ
      dBσ = ClosedSigmaTyInv.sigmaTyFamDeriv tyInv
  
      -- Stage 3 v29: raw dmm' for eqSub-eSigma. Uses eqSubTmRule dm lifted2Eq + transport.
      -- Reconstruct lifted2Eq locally (it was inside compdm's let block).
      dmm' : Derivable
        (termEq (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ [])
          (subTm (liftSubst (liftSubst sigma)) m)
          (subTm (liftSubst (liftSubst tau)) m)
          (sigmaBranchTy (subTy (liftSubst sigma) M)))
      dmm' =
        let
          lifted1EqOuter :
            FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma)
              (liftSubst sigma)
              (liftSubst tau)
          lifted1EqOuter =
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
          lifted2EqOuter :
            FitsEqSubst (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) (B ∷ A ∷ gamma)
              (liftSubst (liftSubst sigma))
              (liftSubst (liftSubst tau))
          lifted2EqOuter =
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
                (liftFitsEq lifted1EqOuter dBσ))
        in
        subst
          (λ T ->
            Derivable (termEq (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ [])
              (subTm (liftSubst (liftSubst sigma)) m)
              (subTm (liftSubst (liftSubst tau)) m) T))
          (sigmaBranchTyLiftComp sigma M)
          (eqSubTmRule dm lifted2EqOuter)

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
      (λ J -> Computable n J)
      (sym resultPath)
      (compESigmaClosed compTransTmClosed compConvTmEqClosed compM compdd dmm' (LexLt-wf _))
  eqSubDerivTmCompCF
    {n} {gamma = gamma} {sigma = sigma} {tau = tau}
    (eQtr {A = A} {L = L} {l = l} {p = p} dL dp dBranch dl dcoh) fitsEq cFitsEq (acc rs) =
    let
      sigmaFits = fitsEqSubstLeft fitsEq
      compp = eqSubDerivTmCompCF dp fitsEq cFitsEq (LexLt-wf _)
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
      wkCtxWFAssoc : CtxWF (subTy (liftSubst sigma) (wkTyBy 1 A) ∷ subTy sigma A ∷ [])
      wkCtxWFAssoc = wfCons (wfCons wfNil dAσ) dWkAσ
      wkCtxWF : CtxWF (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
      wkCtxWF = wfCons (wfCons wfNil dAσ) dWkBaseσ
      compL =
        subst
          (λ T -> HypComputable (suc n) (isType (subTy sigma (tyQtr A) ∷ []) T))
          (cong (λ rho -> subTy rho L) (liftSubstCompKeep sigma))
          (hypTyOpen
            nonemptyNeNil
            (substTyRule dL (liftFitsOne sigmaFits dQtrσ))
            (λ rho fits2 _ accD ->
              subst
                (λ T -> Computable n (isType [] T))
                (sym
                  (cong (λ theta -> subTy rho (subTy theta L)) (liftSubstCompKeep sigma)
                    ∙ subTyComp rho (liftSubst sigma) L))
                (substDerivTyCompCF
                  dL
                  (composeOneBinder sigmaFits dQtrσ fits2) (fitsToCompFits (composeOneBinder sigmaFits dQtrσ fits2)) (LexLt-wf _)))
            (λ rho eta fitsEq2 _ accD ->
              subst
                (λ J -> Computable n J)
                (sym
                  (cong₂ (typeEq [])
                    (cong (λ theta -> subTy rho (subTy theta L)) (liftSubstCompKeep sigma)
                      ∙ subTyComp rho (liftSubst sigma) L)
                    (cong (λ theta -> subTy eta (subTy theta L)) (liftSubstCompKeep sigma)
                      ∙ subTyComp eta (liftSubst sigma) L)))
                (eqSubDerivTyCompCF
                  dL
                  (composeOneBinderEq sigmaFits dQtrσ fitsEq2) (fitsEqToCompFitsEq (composeOneBinderEq sigmaFits dQtrσ fitsEq2)) (LexLt-wf _))))
      compBranchTy =
        subst
          (λ T -> HypComputable (suc n) (isType (subTy sigma A ∷ []) T))
          (cong (λ rho -> subTy rho (qtrBranchTy L)) (liftSubstCompKeep sigma))
          (hypTyOpen
            nonemptyNeNil
            (substTyRule dBranch (liftFitsOne sigmaFits dAσ))
            (λ rho fits2 _ accD ->
              subst
                (λ T -> Computable n (isType [] T))
                (sym
                  (cong (λ theta -> subTy rho (subTy theta (qtrBranchTy L)))
                    (liftSubstCompKeep sigma)
                    ∙ subTyComp rho (liftSubst sigma) (qtrBranchTy L)))
                (substDerivTyCompCF
                  dBranch
                  (composeOneBinder sigmaFits dAσ fits2) (fitsToCompFits (composeOneBinder sigmaFits dAσ fits2)) (LexLt-wf _)))
            (λ rho eta fitsEq2 _ accD ->
              subst
                (λ J -> Computable n J)
                (sym
                  (cong₂ (typeEq [])
                    (cong (λ theta -> subTy rho (subTy theta (qtrBranchTy L)))
                      (liftSubstCompKeep sigma)
                      ∙ subTyComp rho (liftSubst sigma) (qtrBranchTy L))
                    (cong (λ theta -> subTy eta (subTy theta (qtrBranchTy L)))
                      (liftSubstCompKeep sigma)
                      ∙ subTyComp eta (liftSubst sigma) (qtrBranchTy L))))
                (eqSubDerivTyCompCF
                  dBranch
                  (composeOneBinderEq sigmaFits dAσ fitsEq2) (fitsEqToCompFitsEq (composeOneBinderEq sigmaFits dAσ fitsEq2)) (LexLt-wf _))))
      complAssoc = openHypTm1 substDerivTmCompCF eqSubDerivTmCompCF composeCompFits fitsEqToCompFitsEq sigmaFits (fitsToCompFits sigmaFits) dAσ compBranchTy dl (LexLt-wf _)
  
      branchEq =
        subst
          (λ T ->
            HypComputable (suc n)
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
             complAssoc
             (λ rho fits2 _ accD ->
               let
                 composedFitsEq = composeFitsEq fits2 liftedEq
               in
               subst
                 (λ J -> Computable n J)
                 (sym
                   (cong₃ (termEq [])
                     (subTmComp rho (liftSubst sigma) l)
                     (subTmComp rho (liftSubst tau) l)
                     (subTyComp rho (liftSubst sigma) (qtrBranchTy L))))
                 (eqSubDerivTmCompCF
                   dl
                   composedFitsEq
                   (fitsEqToCompFitsEq composedFitsEq) (LexLt-wf _)))
             (λ rho eta fitsEq2 _ accD ->
               let
                 composedFitsEq = composeEqFitsEq fitsEq2 liftedEq
               in
               subst
                 (λ J -> Computable n J)
                 (sym
                   (cong₃ (termEq [])
                     (subTmComp rho (liftSubst sigma) l)
                     (subTmComp eta (liftSubst tau) l)
                     (subTyComp rho (liftSubst sigma) (qtrBranchTy L))))
                 (eqSubDerivTmCompCF
                   dl
                   composedFitsEq
                   (fitsEqToCompFitsEq composedFitsEq) (LexLt-wf _))))
  
      branchEqWk =
        subst
          (λ J -> HypComputable (suc n) J)
          (cong
            (λ T ->
              termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                (wkTmBy 1 (subTm (liftSubst sigma) l))
                (wkTmBy 1 (subTm (liftSubst tau) l))
                T)
            (qtrBranchTyWk (subTy (liftSubst sigma) L)))
          (weakenOneOpenTmEq branchEq wkCtxWF)
      compcohAssoc =
        subst
          (λ J -> HypComputable (suc n) J)
          (cong₂
            (hasTy (subTy (liftSubst sigma) (wkTyBy 1 A) ∷ subTy sigma A ∷ []))
            (sym (wkTmLiftSubst (liftSubst sigma) l))
            (qtrBranchTyWk (subTy (liftSubst sigma) L)
              ∙ sym (qtrCohTyLiftComp sigma L)))
          (weakenOneOpenTm (hypTmEqLeft branchEq) wkCtxWFAssoc)
  
      cohσ =
        subst
          (λ J -> HypComputable (suc n) J)
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
            compcohAssoc
            dcoh
            (LexLt-wf _))
  
      cohστ =
        subst
          (λ J -> HypComputable (suc n) J)
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
             compcohAssoc
             (λ rho fits2 _ accD ->
               let
                 composedFitsEq = composeFitsEq fits2 lifted2Eq
               in
               subst
                 (λ J -> Computable n J)
                 (sym
                   (cong₃ (termEq [])
                     (subTmComp rho (liftSubst (liftSubst sigma)) (wkTmBy 1 l))
                     (subTmComp rho (liftSubst (liftSubst tau)) (renTm qtrSecondBranchRen l))
                     (subTyComp rho (liftSubst (liftSubst sigma)) (qtrCohTy L))))
                 (eqSubDerivTmEqCompCF
                   dcoh
                   composedFitsEq
                   (fitsEqToCompFitsEq composedFitsEq) (LexLt-wf _)))
             (λ rho eta fitsEq2 _ accD ->
               let
                 composedFitsEq = composeEqFitsEq fitsEq2 lifted2Eq
               in
               subst
                 (λ J -> Computable n J)
                 (sym
                   (cong₃ (termEq [])
                     (subTmComp rho (liftSubst (liftSubst sigma)) (wkTmBy 1 l))
                     (subTmComp eta (liftSubst (liftSubst tau)) (renTm qtrSecondBranchRen l))
                     (subTyComp rho (liftSubst (liftSubst sigma)) (qtrCohTy L))))
                 (eqSubDerivTmEqCompCF
                   dcoh
                   composedFitsEq
                   (fitsEqToCompFitsEq composedFitsEq) (LexLt-wf _))))
  
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
      -- Stage 3 v29: extract raw Derivables + <-wellfounded for compEQtrClosed (eqSub-eQtrEq case).
      dll'Arg4 = hypCompToDerivable branchEq
      dcohArg4 = hypCompToDerivable cohσ
      dcoh'Arg4 = hypCompToDerivable cohτ
    in
    subst
      (λ J -> Computable n J)
      (sym resultPath)
      (compEQtrClosed compTransTmClosed compSymTmClosed compConvTmEqClosed
        compL compp dll'Arg4 (LexLt-wf _) dcohArg4 dcoh'Arg4 (LexLt-wf _))
  eqSubDerivTmCompCF {n} (conv d dAB) fitsEq cFitsEq (acc rs) =
    let
      sigmaFits = fitsEqSubstLeft fitsEq
    in
    compConvTmEqClosed (eqSubDerivTmCompCF d fitsEq cFitsEq (LexLt-wf _)) (substDerivTyEqCompCF dAB sigmaFits (fitsToCompFits sigmaFits) (LexLt-wf _))
  eqSubDerivTmCompCF {n} {sigma = sigma} {tau = tau}
    (weakenTm {delta = delta} {t = t} {A = A} d wf) fitsEq cFitsEq (acc rs) =
    subst
      (λ J -> Computable n J)
      (cong₃ (termEq [])
        (sym (subTmWkBy sigma (length delta) t))
        (sym (subTmWkBy tau (length delta) t))
        (sym (subTyWkBy sigma (length delta) A)))
      (eqSubDerivTmCompCF d (dropFitsEq delta fitsEq) (dropCompFitsEq delta cFitsEq) (LexLt-wf _))
  eqSubDerivTmCompCF {n} {sigma = sigma} {tau = tau}
    (substTmRule {sigma = sigma'} {t = t} {A = A} d fits') fitsEq cFitsEq (acc rs) =
    let
      composedFitsEq = composeEqFits fitsEq fits'
      composedCFitsEq = composeCompEqFits fitsEq cFitsEq fits' (iTop (fitsSubstCtxWF fits')) (LexLt-wf _)
    in
    subst
      (λ J -> Computable n J)
      (cong₃ (termEq [])
        (sym (subTmComp sigma sigma' t))
        (sym (subTmComp tau sigma' t))
        (sym (subTyComp sigma sigma' A)))
      (eqSubDerivTmCompCF d composedFitsEq composedCFitsEq (LexLt-wf _))
  eqSubDerivTmEqCompCF {n} (reflTm d) fitsEq cFitsEq (acc rs) =
    eqSubDerivTmCompCF d fitsEq cFitsEq (LexLt-wf _)
  eqSubDerivTmEqCompCF {n} (symTm d du dA) fitsEq cFitsEq (acc rs) =
    let
      tauFits = fitsEqSubstRight (derivToCtxWF du) fitsEq
    in
    compTransTmClosed
      (eqSubDerivTmCompCF du fitsEq cFitsEq (LexLt-wf _))
      (compConvTmEqClosed
        (compSymTmClosed (substDerivTmEqCompCF d tauFits (fitsToCompFits tauFits) (LexLt-wf _)))
        (compSymTyClosed (eqSubDerivTyCompCF dA fitsEq (fitsEqToCompFitsEq fitsEq) (LexLt-wf _))))
  eqSubDerivTmEqCompCF {n} (transTm d₁ d₂) fitsEq cFitsEq (acc rs) =
    let
      sigmaFits = fitsEqSubstLeft fitsEq
    in
    compTransTmClosed
      (substDerivTmEqCompCF d₁ sigmaFits (fitsToCompFits sigmaFits) (LexLt-wf _))
      (eqSubDerivTmEqCompCF d₂ fitsEq cFitsEq (LexLt-wf _))
  eqSubDerivTmEqCompCF {n} (convEq d dAB) fitsEq cFitsEq (acc rs) =
    let
      sigmaFits = fitsEqSubstLeft fitsEq
    in
    compConvTmEqClosed (eqSubDerivTmEqCompCF d fitsEq cFitsEq (LexLt-wf _)) (substDerivTyEqCompCF dAB sigmaFits (fitsToCompFits sigmaFits) (LexLt-wf _))
  eqSubDerivTmEqCompCF {n} (cTop d) fitsEq cFitsEq (acc rs) =
    compCTopClosed (compTmEqLeft (eqSubDerivTmCompCF d fitsEq cFitsEq (LexLt-wf _)))
  eqSubDerivTmEqCompCF {n} {sigma = sigma} {tau = tau}
    (iSigmaEq {a = a} {b = b} {d = d} {A = A} {B = B} dac dbd dA dB) fitsEq cFitsEq (acc rs) =
    let
      sigmaFits = fitsEqSubstLeft fitsEq
      compac = eqSubDerivTmEqCompCF dac fitsEq cFitsEq (LexLt-wf _)
      compA = substDerivTyCompCF dA sigmaFits (fitsToCompFits sigmaFits) (LexLt-wf _)
      dAσ = compToDerivable compA
      compB =
        subst
          (λ T -> HypComputable (suc n) (isType (subTy sigma A ∷ []) T))
          (cong (λ rho -> subTy rho B) (liftSubstCompKeep sigma))
          (hypTyOpen
            nonemptyNeNil
            (substTyRule dB (liftFitsOne sigmaFits dAσ))
            (λ rho fits2 _ accD ->
              subst
                (λ T -> Computable n (isType [] T))
                (sym
                  (cong (λ theta -> subTy rho (subTy theta B)) (liftSubstCompKeep sigma)
                    ∙ subTyComp rho (liftSubst sigma) B))
                (substDerivTyCompCF
                  dB
                  (composeOneBinder sigmaFits dAσ fits2) (fitsToCompFits (composeOneBinder sigmaFits dAσ fits2)) (LexLt-wf _)))
            (λ rho eta fitsEq2 _ accD ->
              subst
                (λ J -> Computable n J)
                (sym
                  (cong₂ (typeEq [])
                    (cong (λ theta -> subTy rho (subTy theta B)) (liftSubstCompKeep sigma)
                      ∙ subTyComp rho (liftSubst sigma) B)
                    (cong (λ theta -> subTy eta (subTy theta B)) (liftSubstCompKeep sigma)
                      ∙ subTyComp eta (liftSubst sigma) B)))
                (eqSubDerivTyCompCF
                  dB
                  (composeOneBinderEq sigmaFits dAσ fitsEq2) (fitsEqToCompFitsEq (composeOneBinderEq sigmaFits dAσ fitsEq2)) (LexLt-wf _))))
      compbdRaw = eqSubDerivTmEqCompCF dbd fitsEq cFitsEq (LexLt-wf _)
      compbd =
        subst
          (λ T -> Computable n (termEq [] (subTm sigma b) (subTm tau d) T))
          (subTyComp sigma (singleSubst a) B
            ∙ cong (λ rho -> subTy rho B) (sym (singleSubstCompLift sigma a))
            ∙ sym (subTyComp (singleSubst (subTm sigma a)) (liftSubst sigma) B))
          compbdRaw
      compa = compTmEqLeft compac
      compcA = compTmEqRightClosed compac
      compb = compTmEqLeft compbd
      compdA = compTmEqRightClosed compbd
      compd =
        compConvTmClosed compdA (compSingleEqSubstTyClosed compB compac (LexLt-wf _))
      compPairLeft = compISigmaClosed compa compb (compFSigmaClosed compA (hypCompToDerivable compB))
      compPairRight = compISigmaClosed compcA compd (compFSigmaClosed compA (hypCompToDerivable compB))
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
  eqSubDerivTmEqCompCF {n} {gamma = gamma} {sigma = sigma} {tau = tau}
    (eSigmaEq {A = A} {B = B} {M = M} {d = d} {d' = d'} {m = m} {m' = m'} dM dd dmL dm) fitsEq cFitsEq (acc rs) =
    let
      sigmaFits = fitsEqSubstLeft fitsEq
      compdd = eqSubDerivTmEqCompCF dd fitsEq cFitsEq (LexLt-wf _)
      compSigma = compTmToCompTy (compTmEqLeft compdd)
      dSigmaσ = compToDerivable compSigma
      compM =
        subst
          (λ T -> HypComputable (suc n) (isType (subTy sigma (tySigma A B) ∷ []) T))
          (cong (λ rho -> subTy rho M) (liftSubstCompKeep sigma))
          (hypTyOpen
            nonemptyNeNil
            (substTyRule dM (liftFitsOne sigmaFits dSigmaσ))
            (λ rho fits2 _ accD ->
              subst
                (λ T -> Computable n (isType [] T))
                (sym
                  (cong (λ theta -> subTy rho (subTy theta M)) (liftSubstCompKeep sigma)
                    ∙ subTyComp rho (liftSubst sigma) M))
                (substDerivTyCompCF
                  dM
                  (composeOneBinder sigmaFits dSigmaσ fits2) (fitsToCompFits (composeOneBinder sigmaFits dSigmaσ fits2)) (LexLt-wf _)))
            (λ rho eta fitsEq2 _ accD ->
              subst
                (λ J -> Computable n J)
                (sym
                  (cong₂ (typeEq [])
                    (cong (λ theta -> subTy rho (subTy theta M)) (liftSubstCompKeep sigma)
                      ∙ subTyComp rho (liftSubst sigma) M)
                    (cong (λ theta -> subTy eta (subTy theta M)) (liftSubstCompKeep sigma)
                      ∙ subTyComp eta (liftSubst sigma) M)))
                (eqSubDerivTyCompCF
                  dM
                  (composeOneBinderEq sigmaFits dSigmaσ fitsEq2) (fitsEqToCompFitsEq (composeOneBinderEq sigmaFits dSigmaσ fitsEq2)) (LexLt-wf _))))
  
      tyInv = invertSigmaTy compSigma evalSigma
      compAσ = ClosedSigmaTyInv.sigmaTyCompHead tyInv
      dAσ = compToDerivable compAσ
      dBσ = ClosedSigmaTyInv.sigmaTyFamDeriv tyInv
  
      -- Stage 3 v29: raw dmm' for eqSub-eSigmaEq. Uses eqSubTmEqRule dm lifted2Eq + transport.
      dmm' : Derivable
        (termEq (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ [])
          (subTm (liftSubst (liftSubst sigma)) m)
          (subTm (liftSubst (liftSubst tau)) m')
          (sigmaBranchTy (subTy (liftSubst sigma) M)))
      dmm' =
        let
          lifted1EqOuter :
            FitsEqSubst (subTy sigma A ∷ []) (A ∷ gamma)
              (liftSubst sigma)
              (liftSubst tau)
          lifted1EqOuter =
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
          lifted2EqOuter :
            FitsEqSubst (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) (B ∷ A ∷ gamma)
              (liftSubst (liftSubst sigma))
              (liftSubst (liftSubst tau))
          lifted2EqOuter =
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
                (liftFitsEq lifted1EqOuter dBσ))
        in
        subst
          (λ T ->
            Derivable (termEq (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ [])
              (subTm (liftSubst (liftSubst sigma)) m)
              (subTm (liftSubst (liftSubst tau)) m') T))
          (sigmaBranchTyLiftComp sigma M)
          (eqSubTmEqRule dm lifted2EqOuter)

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
      (λ J -> Computable n J)
      (sym resultPath)
      (compESigmaClosed compTransTmClosed compConvTmEqClosed compM compdd dmm' (LexLt-wf _))
  eqSubDerivTmEqCompCF {n} {gamma = gamma} {sigma = sigma} {tau = tau}
    (cSigma {A = A} {B = B} {M = M} {b = b} {c = c} {m = m} dM dSigma db dc dm) fitsEq cFitsEq (acc rs) =
    let
      sigmaFits = fitsEqSubstLeft fitsEq
      compb = eqSubDerivTmCompCF db fitsEq cFitsEq (LexLt-wf _)
      compSigma = substDerivTyCompCF dSigma sigmaFits (fitsToCompFits sigmaFits) (LexLt-wf _)
      dSigmaσ = compToDerivable compSigma
      tyInv = invertSigmaTy compSigma evalSigma
      compAσ = ClosedSigmaTyInv.sigmaTyCompHead tyInv
      dAσ = compToDerivable compAσ
      compBσ = sigmaTyFamHypClosed compSigma
      dBσ = hypCompToDerivable compBσ
      compM =
        subst
          (λ T -> HypComputable (suc n) (isType (subTy sigma (tySigma A B) ∷ []) T))
          (cong (λ rho -> subTy rho M) (liftSubstCompKeep sigma))
          (hypTyOpen
            nonemptyNeNil
            (substTyRule dM (liftFitsOne sigmaFits dSigmaσ))
            (λ rho fits2 _ accD ->
              subst
                (λ T -> Computable n (isType [] T))
                (sym
                  (cong (λ theta -> subTy rho (subTy theta M)) (liftSubstCompKeep sigma)
                    ∙ subTyComp rho (liftSubst sigma) M))
                (substDerivTyCompCF
                  dM
                  (composeOneBinder sigmaFits dSigmaσ fits2) (fitsToCompFits (composeOneBinder sigmaFits dSigmaσ fits2)) (LexLt-wf _)))
            (λ rho eta fitsEq2 _ accD ->
              subst
                (λ J -> Computable n J)
                (sym
                  (cong₂ (typeEq [])
                    (cong (λ theta -> subTy rho (subTy theta M)) (liftSubstCompKeep sigma)
                      ∙ subTyComp rho (liftSubst sigma) M)
                    (cong (λ theta -> subTy eta (subTy theta M)) (liftSubstCompKeep sigma)
                      ∙ subTyComp eta (liftSubst sigma) M)))
                (eqSubDerivTyCompCF
                  dM
                  (composeOneBinderEq sigmaFits dSigmaσ fitsEq2) (fitsEqToCompFitsEq (composeOneBinderEq sigmaFits dSigmaσ fitsEq2)) (LexLt-wf _))))
  
      compcRaw = eqSubDerivTmCompCF dc fitsEq cFitsEq (LexLt-wf _)
      compc =
        subst
          (λ T -> Computable n (termEq [] (subTm sigma c) (subTm tau c) T))
          (subTyComp sigma (singleSubst b) B
            ∙ cong (λ rho -> subTy rho B) (sym (singleSubstCompLift sigma b))
            ∙ sym (subTyComp (singleSubst (subTm sigma b)) (liftSubst sigma) B))
          compcRaw
      lifted1 : FitsSubst (subTy sigma A ∷ []) (A ∷ gamma) (liftSubst sigma)
      lifted1 =
        subst
          (λ rho -> FitsSubst (subTy sigma A ∷ []) (A ∷ gamma) rho)
          (liftSubstCompKeep sigma)
          (liftFitsOne sigmaFits dAσ)
  
      branchFitsEqData =
        sigmaCompComputableFitsEqHelper compb compc
  
      branchFitsEq : FitsEqSubst [] (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ [])
        (sigmaCompSub (subTm sigma b) (subTm sigma c))
        (sigmaCompSub (subTm tau b) (subTm tau c))
      branchFitsEq = fst branchFitsEqData
  
      branchCompFitsEq : 
        ComputableFitsEq n branchFitsEq
      branchCompFitsEq = snd branchFitsEqData
      dBranch =
        subst
          (λ T ->
            Derivable (isType (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) T))
          (sigmaBranchTyLiftComp sigma M)
          (subst
            (λ T ->
              Derivable (isType (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) T))
            (cong (λ rho -> subTy rho (sigmaBranchTy M))
              (liftSubstCompKeep (liftSubst sigma)))
            (substTyRule (assocTy dm) (liftFits lifted1 dBσ)))
      compBranchTy =
        subst
          (λ T ->
            HypComputable (suc n) (isType (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) T))
          (sym (sigmaBranchTyLiftComp sigma M))
          (sigmaBranchTyHypFromMotive dBranch compAσ compBσ compM)
  
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
            (fitsToCompFits sigmaFits)
            dAσ
            dBσ
            compBranchTy
            dm
            (LexLt-wf _))
          (λ rho fits2 _ accD ->
            let
              composedFitsEq = composeFitsEq fits2 lifted2Eq
            in
            subst
              (λ J -> Computable n J)
              (sym
                (cong₃ (termEq [])
                  (subTmComp rho (liftSubst (liftSubst sigma)) m)
                  (subTmComp rho (liftSubst (liftSubst tau)) m)
                  (subTyComp rho (liftSubst (liftSubst sigma))
                    (sigmaBranchTy M))))
              (eqSubDerivTmCompCF
                dm
                composedFitsEq
                (fitsEqToCompFitsEq composedFitsEq) (LexLt-wf _)))
          (λ rho eta fitsEq2 _ accD ->
            let
              composedFitsEq = composeEqFitsEq fitsEq2 lifted2Eq
            in
            subst
              (λ J -> Computable n J)
              (sym
                (cong₃ (termEq [])
                  (subTmComp rho (liftSubst (liftSubst sigma)) m)
                  (subTmComp eta (liftSubst (liftSubst tau)) m)
                  (subTyComp rho (liftSubst (liftSubst sigma))
                    (sigmaBranchTy M))))
              (eqSubDerivTmCompCF
                dm
                composedFitsEq
                (fitsEqToCompFitsEq composedFitsEq) (LexLt-wf _)))
  
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
          (λ J -> Computable n J)
          leftCanPath
          (substDerivTmEqCompCF (cSigma dM dSigma db dc dm) sigmaFits (fitsToCompFits sigmaFits) (LexLt-wf _))
  
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
      (λ J -> Computable n J)
      (sym resultPath)
      (compTransTmClosed leftCan compdmEq)
    where
    branchSubEq : 
      (branchFitsEq :
        FitsEqSubst [] (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ [])
          (sigmaCompSub (subTm sigma b) (subTm sigma c))
          (sigmaCompSub (subTm tau b) (subTm tau c)))
      -> ComputableFitsEq n branchFitsEq
      -> HypComputable (suc n)
           (termEq (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ [])
             (subTm (liftSubst (liftSubst sigma)) m)
             (subTm (liftSubst (liftSubst tau)) m)
             (subTy (liftSubst (liftSubst sigma)) (sigmaBranchTy M)))
      -> Computable n
           (termEq []
             (subTm (sigmaCompSub (subTm sigma b) (subTm sigma c))
               (subTm (liftSubst (liftSubst sigma)) m))
             (subTm (sigmaCompSub (subTm tau b) (subTm tau c))
               (subTm (liftSubst (liftSubst tau)) m))
             (subTy (singleSubst (tmPair (subTm sigma b) (subTm sigma c)))
               (subTy (liftSubst sigma) M)))
    branchSubEq branchFitsEq branchCompFitsEq (hypTmEqOpen _ _ _ _ subEqdm) =
      subst
        (λ J -> Computable n J)
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
          branchCompFitsEq
          (LexLt-wf _))
  eqSubDerivTmEqCompCF {n} (iEqEq d) fitsEq cFitsEq (acc rs) =
    compReflTm (compIEqClosed (compTmEqLeft (eqSubDerivTmEqCompCF d fitsEq cFitsEq (LexLt-wf _))))
  eqSubDerivTmEqCompCF {n} (eEqStar dp dA da db) fitsEq cFitsEq (acc rs) =
    let
      compp = eqSubDerivTmCompCF dp fitsEq cFitsEq (LexLt-wf _)
      compab = compEEqClosed (compTmEqLeft compp)
      compbb' = eqSubDerivTmCompCF db fitsEq cFitsEq (LexLt-wf _)
    in
    compTransTmClosed compab compbb'
  eqSubDerivTmEqCompCF {n} (cEq dp dA da db) fitsEq cFitsEq (acc rs) =
    compCEqClosed (compTmEqLeft (eqSubDerivTmCompCF dp fitsEq cFitsEq (LexLt-wf _)))
  eqSubDerivTmEqCompCF {n} (iQtrEq da db) fitsEq cFitsEq (acc rs) =
    let
      compab = eqSubDerivTmCompCF da fitsEq cFitsEq (LexLt-wf _)
      compcd = eqSubDerivTmCompCF db fitsEq cFitsEq (LexLt-wf _)
    in
    compIQtrEqClosed (compTmEqLeft compab) (compTmEqRightClosed compcd)
  eqSubDerivTmEqCompCF {n} {gamma = gamma} {sigma = sigma} {tau = tau}
    (eQtrEq {A = A} {L = L} {l = l} {l' = l'} {p = p} {p' = p'}
      dL dp dBranch dlL dlR dl dcoh dcoh') fitsEq cFitsEq (acc rs) =
    -- Phase F.2 (eqSubDeriv eQtrEq): inlined body of eqSubDerivTmEqCompEQtrEqCF.
    let
      sigmaFits = fitsEqSubstLeft fitsEq
      compp = eqSubDerivTmEqCompCF dp fitsEq cFitsEq
        (rs _ (lift-lex-eq refl (substMeasure-eQtrEq-p< dL dp dBranch dlL dlR dl dcoh dcoh')))
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
      wkCtxWFAssoc : CtxWF (subTy (liftSubst sigma) (wkTyBy 1 A) ∷ subTy sigma A ∷ [])
      wkCtxWFAssoc = wfCons (wfCons wfNil dAσ) dWkAσ
      wkCtxWF : CtxWF (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
      wkCtxWF = wfCons (wfCons wfNil dAσ) dWkBaseσ
      compL =
        subst
          (λ T -> HypComputable (suc n) (isType (subTy sigma (tyQtr A) ∷ []) T))
          (cong (λ rho -> subTy rho L) (liftSubstCompKeep sigma))
          (hypTyOpen
            nonemptyNeNil
            (substTyRule dL (liftFitsOne sigmaFits dQtrσ))
            -- Phase F.2 (Scope B): destructure closure Acc, use accRs _ proof<
            (λ rho fits2 _ accD ->
              subst
                (λ T -> Computable n (isType [] T))
                (sym
                  (cong (λ theta -> subTy rho (subTy theta L)) (liftSubstCompKeep sigma)
                    ∙ subTyComp rho (liftSubst sigma) L))
                (substDerivTyCompCF
                  dL
                  (composeOneBinder sigmaFits dQtrσ fits2) (fitsToCompFits (composeOneBinder sigmaFits dQtrσ fits2)) (access accD _ (lift-lex-eq (sym (tyDepth-subTy _ L)) (substMeasure-substTyRule< dL (liftFitsOne sigmaFits dQtrσ))))))
            -- Phase F.2 (Scope B): destructure closure Acc, use accRs _ proof<
            (λ rho eta fitsEq2 _ accD ->
              subst
                (λ J -> Computable n J)
                (sym
                  (cong₂ (typeEq [])
                    (cong (λ theta -> subTy rho (subTy theta L)) (liftSubstCompKeep sigma)
                      ∙ subTyComp rho (liftSubst sigma) L)
                    (cong (λ theta -> subTy eta (subTy theta L)) (liftSubstCompKeep sigma)
                      ∙ subTyComp eta (liftSubst sigma) L)))
                (eqSubDerivTyCompCF
                  dL
                  (composeOneBinderEq sigmaFits dQtrσ fitsEq2) (fitsEqToCompFitsEq (composeOneBinderEq sigmaFits dQtrσ fitsEq2)) (access accD _ (lift-lex-eq (sym (tyDepth-subTy _ L)) (substMeasure-substTyRule< dL (liftFitsOne sigmaFits dQtrσ)))))))
      compBranchTy =
        subst
          (λ T -> HypComputable (suc n) (isType (subTy sigma A ∷ []) T))
          (cong (λ rho -> subTy rho (qtrBranchTy L)) (liftSubstCompKeep sigma))
          (hypTyOpen
            nonemptyNeNil
            (substTyRule dBranch (liftFitsOne sigmaFits dAσ))
            -- Phase F.2 (Scope B): destructure closure Acc, use accRs _ proof<
            (λ rho fits2 _ accD ->
              subst
                (λ T -> Computable n (isType [] T))
                (sym
                  (cong (λ theta -> subTy rho (subTy theta (qtrBranchTy L)))
                    (liftSubstCompKeep sigma)
                    ∙ subTyComp rho (liftSubst sigma) (qtrBranchTy L)))
                (substDerivTyCompCF
                  dBranch
                  (composeOneBinder sigmaFits dAσ fits2) (fitsToCompFits (composeOneBinder sigmaFits dAσ fits2)) (access accD _ (lift-lex-eq (sym (tyDepth-subTy _ (qtrBranchTy L))) (substMeasure-substTyRule< dBranch (liftFitsOne sigmaFits dAσ))))))
            -- Phase F.2 (Scope B): destructure closure Acc, use accRs _ proof<
            (λ rho eta fitsEq2 _ accD ->
              subst
                (λ J -> Computable n J)
                (sym
                  (cong₂ (typeEq [])
                    (cong (λ theta -> subTy rho (subTy theta (qtrBranchTy L)))
                      (liftSubstCompKeep sigma)
                      ∙ subTyComp rho (liftSubst sigma) (qtrBranchTy L))
                    (cong (λ theta -> subTy eta (subTy theta (qtrBranchTy L)))
                      (liftSubstCompKeep sigma)
                      ∙ subTyComp eta (liftSubst sigma) (qtrBranchTy L))))
                (eqSubDerivTyCompCF
                  dBranch
                  (composeOneBinderEq sigmaFits dAσ fitsEq2) (fitsEqToCompFitsEq (composeOneBinderEq sigmaFits dAσ fitsEq2)) (access accD _ (lift-lex-eq (sym (tyDepth-subTy _ (qtrBranchTy L))) (substMeasure-substTyRule< dBranch (liftFitsOne sigmaFits dAσ)))))))
      -- Phase F.2 (Scope A): use rs _ proof< for dlL recursion
      complAssoc = openHypTm1 substDerivTmCompCF eqSubDerivTmCompCF composeCompFits fitsEqToCompFitsEq sigmaFits (fitsToCompFits sigmaFits) dAσ compBranchTy dlL
        (rs _ (lift-lex-eq refl (substMeasure-eQtrEq-dlL< dL dp dBranch dlL dlR dl dcoh dcoh')))
      -- Phase F.2 (Scope A): use rs _ proof< for dlR recursion
      complAssocRight = openHypTm1 substDerivTmCompCF eqSubDerivTmCompCF composeCompFits fitsEqToCompFitsEq sigmaFits (fitsToCompFits sigmaFits) dAσ compBranchTy dlR
        (rs _ (lift-lex-eq refl (substMeasure-eQtrEq-dlR< dL dp dBranch dlL dlR dl dcoh dcoh')))
  
      branchEq =
        subst
          (λ T ->
            HypComputable (suc n)
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
             complAssoc
             -- Phase F.2 (Scope B): destructure closure Acc, dl via eqSubTmEqRule
             (λ rho fits2 _ accD ->
               let
                 composedFitsEq = composeFitsEq fits2 liftedEq
               in
               subst
                 (λ J -> Computable n J)
                 (sym
                   (cong₃ (termEq [])
                     (subTmComp rho (liftSubst sigma) l)
                     (subTmComp rho (liftSubst tau) l')
                     (subTyComp rho (liftSubst sigma) (qtrBranchTy L))))
                 (eqSubDerivTmEqCompCF
                   dl
                   composedFitsEq
                   (fitsEqToCompFitsEq composedFitsEq) (access accD _ (lift-lex-eq (sym (tyDepth-subTy _ (qtrBranchTy L))) (substMeasure-eqSubTmEqRule< dl liftedEq)))))
             -- Phase F.2 (Scope B): destructure closure Acc, dl via eqSubTmEqRule
             (λ rho eta fitsEq2 _ accD ->
               let
                 composedFitsEq = composeEqFitsEq fitsEq2 liftedEq
               in
               subst
                 (λ J -> Computable n J)
                 (sym
                   (cong₃ (termEq [])
                     (subTmComp rho (liftSubst sigma) l)
                     (subTmComp eta (liftSubst tau) l')
                     (subTyComp rho (liftSubst sigma) (qtrBranchTy L))))
                 (eqSubDerivTmEqCompCF
                   dl
                   composedFitsEq
                   (fitsEqToCompFitsEq composedFitsEq) (access accD _ (lift-lex-eq (sym (tyDepth-subTy _ (qtrBranchTy L))) (substMeasure-eqSubTmEqRule< dl liftedEq))))))
  
      branchEqRight =
        subst
          (λ T ->
            HypComputable (suc n)
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
             (eqSubTmRule dlR liftedEq)
             complAssocRight
             -- Phase F.2 (Scope B): destructure closure Acc, dlR via eqSubTmRule
             (λ rho fits2 _ accD ->
               let
                 composedFitsEq = composeFitsEq fits2 liftedEq
               in
               subst
                 (λ J -> Computable n J)
                 (sym
                   (cong₃ (termEq [])
                     (subTmComp rho (liftSubst sigma) l')
                     (subTmComp rho (liftSubst tau) l')
                     (subTyComp rho (liftSubst sigma) (qtrBranchTy L))))
                 (eqSubDerivTmCompCF
                   dlR
                   composedFitsEq
                   (fitsEqToCompFitsEq composedFitsEq)
                   (access accD _ (lift-lex-eq (sym (tyDepth-subTy _ (qtrBranchTy L)))
                     (substMeasure-eqSubTmRule< dlR liftedEq)))))
             (λ rho eta fitsEq2 _ accD ->
               let
                 composedFitsEq = composeEqFitsEq fitsEq2 liftedEq
               in
               subst
                 (λ J -> Computable n J)
                 (sym
                   (cong₃ (termEq [])
                     (subTmComp rho (liftSubst sigma) l')
                     (subTmComp eta (liftSubst tau) l')
                     (subTyComp rho (liftSubst sigma) (qtrBranchTy L))))
                 (eqSubDerivTmCompCF
                   dlR
                   composedFitsEq
                   (fitsEqToCompFitsEq composedFitsEq)
                   (access accD _ (lift-lex-eq (sym (tyDepth-subTy _ (qtrBranchTy L)))
                     (substMeasure-eqSubTmRule< dlR liftedEq))))))
  
      branchEqRightWk =
        subst
          (λ J -> HypComputable (suc n) J)
          (cong
            (λ T ->
              termEq (wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ [])
                (wkTmBy 1 (subTm (liftSubst sigma) l'))
                (wkTmBy 1 (subTm (liftSubst tau) l'))
                T)
            (qtrBranchTyWk (subTy (liftSubst sigma) L)))
          (weakenOneOpenTmEq branchEqRight wkCtxWF)
      compcohAssoc =
        subst
          (λ J -> HypComputable (suc n) J)
          (cong₂
            (hasTy (subTy (liftSubst sigma) (wkTyBy 1 A) ∷ subTy sigma A ∷ []))
            (sym (wkTmLiftSubst (liftSubst sigma) l))
            (qtrBranchTyWk (subTy (liftSubst sigma) L)
              ∙ sym (qtrCohTyLiftComp sigma L)))
          (weakenOneOpenTm (hypTmEqLeft branchEq) wkCtxWFAssoc)
  
      cohσ =
        subst
          (λ J -> HypComputable (suc n) J)
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
          -- Phase F.2 (Scope A): use rs _ proof< for dcoh recursion
          (openHypTmEq2
            sigmaFits
            dAσ
            dWkAσ
            compcohAssoc
            dcoh
            (rs _ (lift-lex-eq refl (substMeasure-eQtrEq-dcoh< dL dp dBranch dlL dlR dl dcoh dcoh'))))
      compcohAssoc' =
        subst
          (λ J -> HypComputable (suc n) J)
          (cong₂
            (hasTy (subTy (liftSubst sigma) (wkTyBy 1 A) ∷ subTy sigma A ∷ []))
            (sym (wkTmLiftSubst (liftSubst sigma) l'))
            (qtrBranchTyWk (subTy (liftSubst sigma) L)
              ∙ sym (qtrCohTyLiftComp sigma L)))
          (weakenOneOpenTm (hypTmEqLeft branchEqRight) wkCtxWFAssoc)
  
      coh'στ =
        subst
          (λ J -> HypComputable (suc n) J)
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
             compcohAssoc'
             -- Phase F.2 (Scope B): destructure closure Acc, dcoh' via eqSubTmEqRule
             (λ rho fits2 _ accD ->
               let
                 composedFitsEq = composeFitsEq fits2 lifted2Eq
               in
               subst
                 (λ J -> Computable n J)
                 (sym
                   (cong₃ (termEq [])
                     (subTmComp rho (liftSubst (liftSubst sigma)) (wkTmBy 1 l'))
                     (subTmComp rho (liftSubst (liftSubst tau)) (renTm qtrSecondBranchRen l'))
                     (subTyComp rho (liftSubst (liftSubst sigma)) (qtrCohTy L))))
                 (eqSubDerivTmEqCompCF
                   dcoh'
                   composedFitsEq
                   (fitsEqToCompFitsEq composedFitsEq)
                   (access accD _ (lift-lex-eq (sym (tyDepth-subTy _ (qtrCohTy L)))
                     (substMeasure-eqSubTmEqRule< dcoh' lifted2Eq)))))
             (λ rho eta fitsEq2 _ accD ->
               let
                 composedFitsEq = composeEqFitsEq fitsEq2 lifted2Eq
               in
               subst
                 (λ J -> Computable n J)
                 (sym
                   (cong₃ (termEq [])
                     (subTmComp rho (liftSubst (liftSubst sigma)) (wkTmBy 1 l'))
                     (subTmComp eta (liftSubst (liftSubst tau)) (renTm qtrSecondBranchRen l'))
                     (subTyComp rho (liftSubst (liftSubst sigma)) (qtrCohTy L))))
                 (eqSubDerivTmEqCompCF
                   dcoh'
                   composedFitsEq
                   (fitsEqToCompFitsEq composedFitsEq)
                   (access accD _ (lift-lex-eq (sym (tyDepth-subTy _ (qtrCohTy L)))
                     (substMeasure-eqSubTmEqRule< dcoh' lifted2Eq))))))
  
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
      -- Stage 3 v29: extract raw Derivables + <-wellfounded for compEQtrClosed (eqSub-eQtr case).
      dll'Arg = hypCompToDerivable branchEq
      dcohArg = hypCompToDerivable cohσ
      dcoh'Arg = hypCompToDerivable cohτ
    in
    subst
      (λ J -> Computable n J)
      (sym resultPath)
      (compEQtrClosed compTransTmClosed compSymTmClosed compConvTmEqClosed
        compL compp dll'Arg (LexLt-wf _) dcohArg dcoh'Arg (LexLt-wf _))

  eqSubDerivTmEqCompCF {n} {gamma = gamma} {sigma = sigma} {tau = tau}
    (cQtr {A = A} {L = L} {a = a} {l = l}
      dL da dBranch dl dcoh) fitsEq cFitsEq (acc rs) =
    -- Phase F.2 (eqSubDeriv cQtr): inlined body of eqSubDerivTmEqCompCQtr.
    let
      sigmaFits = fitsEqSubstLeft fitsEq
      compa = eqSubDerivTmCompCF da fitsEq (fitsEqToCompFitsEq fitsEq)
        (rs _ (lift-lex-eq refl (substMeasure-cQtr-a< dL da dBranch dl dcoh)))
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
      wkCtxWF : CtxWF (subTy (liftSubst sigma) (wkTyBy 1 A) ∷ subTy sigma A ∷ [])
      wkCtxWF = wfCons (wfCons wfNil dAσ) dWkAσ
      compL =
        subst
          (λ T -> HypComputable (suc n) (isType (subTy sigma (tyQtr A) ∷ []) T))
          (cong (λ rho -> subTy rho L) (liftSubstCompKeep sigma))
          (hypTyOpen
            nonemptyNeNil
            (substTyRule dL (liftFitsOne sigmaFits dQtrσ))
            -- Phase F.2 (Scope B): dL via substTyRule
            (λ rho fits2 _ accD ->
              subst
                (λ T -> Computable n (isType [] T))
                (sym
                  (cong (λ theta -> subTy rho (subTy theta L)) (liftSubstCompKeep sigma)
                    ∙ subTyComp rho (liftSubst sigma) L))
                (substDerivTyCompCF
                  dL
                  (composeOneBinder sigmaFits dQtrσ fits2) (fitsToCompFits (composeOneBinder sigmaFits dQtrσ fits2)) (access accD _ (lift-lex-eq (sym (tyDepth-subTy _ L)) (substMeasure-substTyRule< dL liftFitsOne sigmaFits dQtrσ)))))
            -- Phase F.2 (Scope B): dL via substTyRule
            (λ rho eta fitsEq2 _ accD ->
              subst
                (λ J -> Computable n J)
                (sym
                  (cong₂ (typeEq [])
                    (cong (λ theta -> subTy rho (subTy theta L)) (liftSubstCompKeep sigma)
                      ∙ subTyComp rho (liftSubst sigma) L)
                    (cong (λ theta -> subTy eta (subTy theta L)) (liftSubstCompKeep sigma)
                      ∙ subTyComp eta (liftSubst sigma) L)))
                (eqSubDerivTyCompCF
                  dL
                  (composeOneBinderEq sigmaFits dQtrσ fitsEq2) (fitsEqToCompFitsEq (composeOneBinderEq sigmaFits dQtrσ fitsEq2)) (access accD _ (lift-lex-eq (sym (tyDepth-subTy _ L)) (substMeasure-substTyRule< dL liftFitsOne sigmaFits dQtrσ))))))
      compBranchTy =
        subst
          (λ T -> HypComputable (suc n) (isType (subTy sigma A ∷ []) T))
          (cong (λ rho -> subTy rho (qtrBranchTy L)) (liftSubstCompKeep sigma))
          (hypTyOpen
            nonemptyNeNil
            (substTyRule dBranch (liftFitsOne sigmaFits dAσ))
            -- Phase F.2 (Scope B): dBranch via substTyRule
            (λ rho fits2 _ accD ->
              subst
                (λ T -> Computable n (isType [] T))
                (sym
                  (cong (λ theta -> subTy rho (subTy theta (qtrBranchTy L)))
                    (liftSubstCompKeep sigma)
                    ∙ subTyComp rho (liftSubst sigma) (qtrBranchTy L)))
                (substDerivTyCompCF
                  dBranch
                  (composeOneBinder sigmaFits dAσ fits2) (fitsToCompFits (composeOneBinder sigmaFits dAσ fits2)) (access accD _ (lift-lex-eq (sym (tyDepth-subTy _ (qtrBranchTy L))) (substMeasure-substTyRule< dBranch liftFitsOne sigmaFits dAσ)))))
            -- Phase F.2 (Scope B): dBranch via substTyRule
            (λ rho eta fitsEq2 _ accD ->
              subst
                (λ J -> Computable n J)
                (sym
                  (cong₂ (typeEq [])
                    (cong (λ theta -> subTy rho (subTy theta (qtrBranchTy L)))
                      (liftSubstCompKeep sigma)
                      ∙ subTyComp rho (liftSubst sigma) (qtrBranchTy L))
                    (cong (λ theta -> subTy eta (subTy theta (qtrBranchTy L)))
                      (liftSubstCompKeep sigma)
                      ∙ subTyComp eta (liftSubst sigma) (qtrBranchTy L))))
                (eqSubDerivTyCompCF
                  dBranch
                  (composeOneBinderEq sigmaFits dAσ fitsEq2) (fitsEqToCompFitsEq (composeOneBinderEq sigmaFits dAσ fitsEq2)) (access accD _ (lift-lex-eq (sym (tyDepth-subTy _ (qtrBranchTy L))) (substMeasure-substTyRule< dBranch liftFitsOne sigmaFits dAσ))))))
  
      -- Build dBranchSubσ and dlSubσ for the new compCQtrClosed signature
      liftedOneARawσ : FitsSubst (subTy sigma A ∷ []) (A ∷ gamma)
        (consSubst (var zero) (compSub (keepSubstBy 1) sigma))
      liftedOneARawσ = liftFitsOne sigmaFits dAσ
      dBranchSubσ : Derivable
        (isType (subTy sigma A ∷ []) (qtrBranchTy (subTy (liftSubst sigma) L)))
      dBranchSubσ =
        subst
          (λ T -> Derivable (isType (subTy sigma A ∷ []) T))
          (cong (λ rho -> subTy rho (qtrBranchTy L)) (liftSubstCompKeep sigma)
            ∙ qtrBranchTyLiftComp sigma L)
          (substTyRule dBranch liftedOneARawσ)
      dlSubσ : Derivable
        (hasTy (subTy sigma A ∷ []) (subTm (liftSubst sigma) l)
          (qtrBranchTy (subTy (liftSubst sigma) L)))
      dlSubσ =
        subst
          (λ J -> Derivable J)
          (cong₂
            (hasTy (subTy sigma A ∷ []))
            (cong (λ rho -> subTm rho l) (liftSubstCompKeep sigma))
            (cong (λ rho -> subTy rho (qtrBranchTy L)) (liftSubstCompKeep sigma)
              ∙ qtrBranchTyLiftComp sigma L))
          (substTmRule dl liftedOneARawσ)
      -- Build rawBodyσ via SCC 2 on original dl with <-wellfounded (this helper doesn't receive Acc)
      lBodyFitsσ : CompFitsBundle n (subTy sigma A ∷ []) (qtrCompSub (subTm sigma a))
      lBodyFitsσ = qtrCompComputableFitsHelper {A = subTy sigma A} compaσ
      composedFitsLσ :
        FitsSubst [] (A ∷ gamma)
          (compSub (qtrCompSub (subTm sigma a)) (liftSubst sigma))
      composedFitsLσ = composeOneBinder sigmaFits dAσ (fst lBodyFitsσ)
      composedFitsLFinalσ :
        FitsSubst [] (A ∷ gamma) (compSub sigma (qtrCompSub a))
      composedFitsLFinalσ =
        subst
          (λ rho -> FitsSubst [] (A ∷ gamma) rho)
          (sym (qtrCompSubLiftComp sigma a))
          composedFitsLσ
      composedCFitsLFinalσ : ComputableFits n composedFitsLFinalσ
      composedCFitsLFinalσ = fitsToCompFits composedFitsLFinalσ
      rawBodyRawσ : Computable n
        (hasTy [] (subTm (compSub sigma (qtrCompSub a)) l)
          (subTy (compSub sigma (qtrCompSub a)) (qtrBranchTy L)))
      rawBodyRawσ =
        -- Phase F.2 (Scope A): dl via substMeasure-cQtr-l<
        substDerivTmCompCF dl composedFitsLFinalσ composedCFitsLFinalσ
          (rs _ (lift-lex-eq refl (substMeasure-cQtr-l< dL da dBranch dl dcoh)))
      rawBodyσ : Computable n
        (hasTy [] (subTm (qtrCompSub (subTm sigma a)) (subTm (liftSubst sigma) l))
          (subTy (qtrCompSub (subTm sigma a)) (qtrBranchTy (subTy (liftSubst sigma) L))))
      rawBodyσ =
        subst
          (λ J -> Computable n J)
          (cong₂ (hasTy [])
            (cong (λ rho -> subTm rho l) (qtrCompSubLiftComp sigma a)
              ∙ sym (subTmComp (qtrCompSub (subTm sigma a)) (liftSubst sigma) l))
            (cong (λ rho -> subTy rho (qtrBranchTy L)) (qtrCompSubLiftComp sigma a)
              ∙ sym (subTyComp (qtrCompSub (subTm sigma a)) (liftSubst sigma) (qtrBranchTy L))
              ∙ cong (subTy (qtrCompSub (subTm sigma a))) (qtrBranchTyLiftComp sigma L)))
          rawBodyRawσ
      -- complσ (unchanged - still needed for compcohAssoc/compcohσ)
      complσ =
        subst
          (λ T ->
            HypComputable (suc n)
              (hasTy (subTy sigma A ∷ [])
                (subTm (liftSubst sigma) l)
                T))
          (qtrBranchTyLiftComp sigma L)
          -- Phase F.2 (Scope A): dl via substMeasure-cQtr-l<
          (openHypTm1 substDerivTmCompCF eqSubDerivTmCompCF composeCompFits fitsEqToCompFitsEq
            sigmaFits
            (fitsToCompFits sigmaFits)
            dAσ
            compBranchTy
            dl
            (rs _ (lift-lex-eq refl (substMeasure-cQtr-l< dL da dBranch dl dcoh))))
      compcohAssoc =
        subst
          (λ J -> HypComputable (suc n) J)
          (cong₂
            (hasTy (subTy (liftSubst sigma) (wkTyBy 1 A) ∷ subTy sigma A ∷ []))
            (sym (wkTmLiftSubst (liftSubst sigma) l))
            (qtrBranchTyWk (subTy (liftSubst sigma) L)
              ∙ sym (qtrCohTyLiftComp sigma L)))
          (weakenOneOpenTm complσ wkCtxWF)
  
      compcohσ =
        subst
          (λ J -> HypComputable (suc n) J)
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
          -- Phase F.2 (Scope A): dcoh via substMeasure-cQtr-dcoh<
          (openHypTmEq2
            sigmaFits
            dAσ
            dWkAσ
            compcohAssoc
            dcoh
            (rs _ (lift-lex-eq refl (substMeasure-cQtr-dcoh< dL da dBranch dl dcoh))))
  
      leftCan = compCQtrClosed compL compaσ dBranchSubσ dlSubσ rawBodyσ compcohσ
  
      complEq =
        subst
          (λ T ->
            HypComputable (suc n)
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
             -- Phase F.2 (Scope A): dl via substMeasure-cQtr-l<
             (openHypTm1 substDerivTmCompCF eqSubDerivTmCompCF composeCompFits fitsEqToCompFitsEq
               sigmaFits
               (fitsToCompFits sigmaFits)
               dAσ
               compBranchTy
               dl
               (rs _ (lift-lex-eq refl (substMeasure-cQtr-l< dL da dBranch dl dcoh))))
             -- Phase F.2 (Scope B): dl via eqSubTmRule
             (λ rho fits2 _ accD ->
               let
                 composedFitsEq = composeFitsEq fits2 liftedEq
               in
               subst
                 (λ J -> Computable n J)
                 (sym
                   (cong₃ (termEq [])
                     (subTmComp rho (liftSubst sigma) l)
                     (subTmComp rho (liftSubst tau) l)
                     (subTyComp rho (liftSubst sigma) (qtrBranchTy L))))
                 (eqSubDerivTmCompCF
                   dl
                   composedFitsEq (fitsEqToCompFitsEq composedFitsEq) (access accD _ (lift-lex-eq (sym (tyDepth-subTy _ (qtrBranchTy L))) (substMeasure-eqSubTmRule< dl liftedEq)))))
             -- Phase F.2 (Scope B): dl via eqSubTmRule
             (λ rho eta fitsEq2 _ accD ->
               let
                 composedFitsEq = composeEqFitsEq fitsEq2 liftedEq
               in
               subst
                 (λ J -> Computable n J)
                 (sym
                   (cong₃ (termEq [])
                     (subTmComp rho (liftSubst sigma) l)
                     (subTmComp eta (liftSubst tau) l)
                     (subTyComp rho (liftSubst sigma) (qtrBranchTy L))))
                 (eqSubDerivTmCompCF
                   dl
                   composedFitsEq (fitsEqToCompFitsEq composedFitsEq) (access accD _ (lift-lex-eq (sym (tyDepth-subTy _ (qtrBranchTy L))) (substMeasure-eqSubTmRule< dl liftedEq))))))
  
      branchFitsEqData =
        qtrCompComputableFitsEqHelper compa
  
      branchFitsEq :
        FitsEqSubst [] (subTy sigma A ∷ [])
          (qtrCompSub (subTm sigma a))
          (qtrCompSub (subTm tau a))
      branchFitsEq = fst branchFitsEqData
  
      branchCompFitsEq : 
        ComputableFitsEq n branchFitsEq
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
      (λ J -> Computable n J)
      (sym resultPath)
      (compTransTmClosed leftCan compBodyEq)
    where
    branchSubEq : (branchFitsEq :
        FitsEqSubst [] (subTy sigma A ∷ [])
          (qtrCompSub (subTm sigma a))
          (qtrCompSub (subTm tau a)))
      -> ComputableFitsEq n branchFitsEq
      -> HypComputable (suc n)
           (termEq (subTy sigma A ∷ [])
             (subTm (liftSubst sigma) l)
             (subTm (liftSubst tau) l)
             (qtrBranchTy (subTy (liftSubst sigma) L)))
      -> Computable n
           (termEq []
             (subTm (qtrCompSub (subTm sigma a)) (subTm (liftSubst sigma) l))
             (subTm (qtrCompSub (subTm tau a)) (subTm (liftSubst tau) l))
             (subTy (singleSubst (tmClass (subTm sigma a))) (subTy (liftSubst sigma) L)))
    branchSubEq branchFitsEq branchCompFitsEq (hypTmEqOpen _ _ _ _ subEqdl) =
      subst
        (λ J -> Computable n J)
        (cong
          (termEq []
            (subTm (qtrCompSub (subTm sigma a)) (subTm (liftSubst sigma) l))
            (subTm (qtrCompSub (subTm tau a)) (subTm (liftSubst tau) l)))
          (qtrBranchTyComp (subTm sigma a) (subTy (liftSubst sigma) L)))
        (subEqdl
          (qtrCompSub (subTm sigma a))
          (qtrCompSub (subTm tau a))
          branchFitsEq
          branchCompFitsEq
          (LexLt-wf _))
  

  eqSubDerivTmEqCompCF {n} {sigma = sigma} {tau = tau}
    (weakenTmEq {delta = delta} {t = t} {u = u} {A = A} d wf) fitsEq cFitsEq (acc rs) =
    subst
      (λ J -> Computable n J)
      (cong₃ (termEq [])
        (sym (subTmWkBy sigma (length delta) t))
        (sym (subTmWkBy tau (length delta) u))
        (sym (subTyWkBy sigma (length delta) A)))
      (eqSubDerivTmEqCompCF d (dropFitsEq delta fitsEq) (dropCompFitsEq delta cFitsEq) (LexLt-wf _))
  eqSubDerivTmEqCompCF {n} {sigma = sigma} {tau = tau}
    (substTmEqRule {sigma = sigma'} {t = t} {u = u} {A = A} d fits') fitsEq cFitsEq (acc rs) =
    let
      composedFitsEq = composeEqFits fitsEq fits'
      composedCFitsEq = composeCompEqFits fitsEq cFitsEq fits' (iTop (fitsSubstCtxWF fits')) (LexLt-wf _)
    in
    subst
      (λ J -> Computable n J)
      (cong₃ (termEq [])
        (sym (subTmComp sigma sigma' t))
        (sym (subTmComp tau sigma' u))
        (sym (subTyComp sigma sigma' A)))
      (eqSubDerivTmEqCompCF d composedFitsEq composedCFitsEq (LexLt-wf _))
  eqSubDerivTmEqCompCF {n} {sigma = sigma} {tau = tau}
    (eqSubTmRule {sigma = sigma'} {tau = tau'} {t = t} {A = A} d fitsEq') fitsEq cFitsEq (acc rs) =
    let
      composedFitsEq = composeEqFitsEq fitsEq fitsEq'
      composedCFitsEq =
        composeCompEqFitsEq fitsEq cFitsEq fitsEq'
          (reflTm (iTop (fitsEqSubstCtxWF fitsEq')))
          (LexLt-wf _)
    in
    subst
      (λ J -> Computable n J)
      (cong₃ (termEq [])
        (sym (subTmComp sigma sigma' t))
        (sym (subTmComp tau tau' t))
        (sym (subTyComp sigma sigma' A)))
      (eqSubDerivTmCompCF d composedFitsEq composedCFitsEq (LexLt-wf _))
  eqSubDerivTmEqCompCF {n} {sigma = sigma} {tau = tau}
    (eqSubTmEqRule {sigma = sigma'} {tau = tau'} {t = t} {u = u} {A = A} d fitsEq') fitsEq cFitsEq (acc rs) =
    let
      composedFitsEq = composeEqFitsEq fitsEq fitsEq'
      composedCFitsEq =
        composeCompEqFitsEq fitsEq cFitsEq fitsEq'
          (reflTm (iTop (fitsEqSubstCtxWF fitsEq')))
          (LexLt-wf _)
    in
    subst
      (λ J -> Computable n J)
      (cong₃ (termEq [])
        (sym (subTmComp sigma sigma' t))
        (sym (subTmComp tau tau' u))
        (sym (subTyComp sigma sigma' A)))
      (eqSubDerivTmEqCompCF d composedFitsEq composedCFitsEq (LexLt-wf _))
  substTmClosed : {n : ℕ} -> {delta : Ctx} {t : RawTerm} {A : RawType} {sigma : Subst}
    -> Derivable (hasTy delta t A)
    -> FitsSubst [] delta sigma
    -> Computable n (hasTy [] (subTm sigma t) (subTy sigma A))
  substTmClosed {n} d fits = substDerivTmCompCF d fits (fitsToCompFits fits) (LexLt-wf _)
  
  substTmEqClosed : {n : ℕ} -> {delta : Ctx} {t u : RawTerm} {A : RawType} {sigma : Subst}
    -> Derivable (termEq delta t u A)
    -> FitsSubst [] delta sigma
    -> Computable n (termEq [] (subTm sigma t) (subTm sigma u) (subTy sigma A))
  substTmEqClosed {n} d fits = substDerivTmEqCompCF d fits (fitsToCompFits fits) (LexLt-wf _)
  
  mkHypComputableTy : {n : ℕ} -> {gamma : Ctx} {A : RawType}
    -> ((gamma ≡ []) -> ⊥)
    -> (d : Derivable (isType gamma A))
    -> Acc LexLt (substTaskLexMeasure d)
    -> HypComputable (suc n) (isType gamma A)
  mkHypComputableTy {n} neq d acc0 =
    hypTyOpen
      neq
      d
      (λ sigma fits cFits _ -> substDerivTyCompCF d fits cFits acc0)
      (λ sigma tau fitsEq cFitsEq _ -> eqSubDerivTyCompCF d fitsEq cFitsEq acc0)

  mkHypComputableTyEq : {n : ℕ} -> {gamma : Ctx} {A B : RawType}
    -> ((gamma ≡ []) -> ⊥)
    -> Derivable (typeEq gamma A B)
    -> HypComputable (suc n) (typeEq gamma A B)
  mkHypComputableTyEq {n} neq d =
    hypTyEqOpen
      neq
      d
      (mkHypComputableTy neq (leftTyWitnessEq d) (LexLt-wf _))
      (λ sigma fits cFits accD -> substDerivTyEqCompCF d fits cFits accD)
      (λ sigma tau fitsEq cFitsEq accD -> eqSubDerivTyEqCompCF d fitsEq cFitsEq accD)
  
  hypComputableTyEq : {n : ℕ} -> {A B C : RawType} {gamma : Ctx}
    -> Derivable (typeEq (C ∷ gamma) A B)
    -> HypComputable (suc n) (typeEq (C ∷ gamma) A B)
  hypComputableTyEq {n} = mkHypComputableTyEq nonemptyNeNil
  
  hypTyEqRight : {n : ℕ} -> {gamma : Ctx} {A B : RawType}
    -> HypComputable (suc n) (typeEq gamma A B)
    -> HypComputable (suc n) (isType gamma B)
  hypTyEqRight {n} (hypTyEqOpen neq d _ sub subEq) =
    hypTyOpen
      neq
      (assocTyRight d)
      (λ sigma fits cFits accD ->
        compTyEqRightClosed (sub sigma fits cFits (LexLt-wf _)))
      (λ sigma tau fitsEq cFitsEq accD ->
        compTransTyClosed
          (compSymTyClosed
            (sub sigma (fitsEqSubstLeft fitsEq) (compFitsEqLeft cFitsEq) (LexLt-wf _)))
          (subEq sigma tau fitsEq cFitsEq (LexLt-wf _)))

  hypTmEqRight : {n : ℕ} -> {gamma : Ctx} {t u : RawTerm} {A : RawType}
    -> HypComputable (suc n) (termEq gamma t u A)
    -> HypComputable (suc n) (hasTy gamma u A)
  hypTmEqRight {n} (hypTmEqOpen neq d (hypTmOpen _ _ compA _ _) sub subEq) =
    hypTmOpen
      neq
      (assocTmRight d)
      compA
      (λ sigma fits cFits accD ->
        compTmEqRightClosed (sub sigma fits cFits (LexLt-wf _)))
      (λ sigma tau fitsEq cFitsEq accD ->
        compTransTmClosed
          (compSymTmClosed
            (sub sigma (fitsEqSubstLeft fitsEq) (compFitsEqLeft cFitsEq) (LexLt-wf _)))
          (subEq sigma tau fitsEq cFitsEq (LexLt-wf _)))
  
  compTransportFamilyTy : {n : ℕ} -> {A C D : RawType}
    -> Computable n (typeEq [] A C)
    -> HypComputable (suc n) (isType (A ∷ []) D)
    -> HypComputable (suc n) (isType (C ∷ []) D)
  compTransportFamilyTy {n} {A = A} {C = C} {D = D} compAC (hypTyOpen _ dD subD subEqD) =
    hypTyOpen
      nonemptyNeNil
      (transportFamilyTy dAC dC dD)
      (λ sigma fits _ accD ->
        let
          composedFits = composeFits fits (headTypeTransportFits dAC dC)
        in
        subst
          (λ T -> Computable n (isType [] T))
          (sym (subTyComp sigma idSubst D)
            ∙ cong (λ T -> subTy sigma T) (subTyId D))
          (subD
            (compSub sigma idSubst)
            composedFits
            (singleBinderComputableFits composedFits)
            (LexLt-wf _)))
      (λ sigma tau fitsEq _ accD ->
        let
          composedFitsEq = composeEqFits fitsEq (headTypeTransportFits dAC dC)
        in
        subst
          (λ J -> Computable n J)
          (cong₂ (typeEq [])
            (sym (subTyComp sigma idSubst D)
              ∙ cong (λ T -> subTy sigma T) (subTyId D))
            (sym (subTyComp tau idSubst D)
              ∙ cong (λ T -> subTy tau T) (subTyId D)))
          (subEqD
            (compSub sigma idSubst)
            (compSub tau idSubst)
            composedFitsEq
            (singleBinderComputableFitsEq composedFitsEq)
            (LexLt-wf _)))
    where
    dAC : Derivable (typeEq [] A C)
    dAC = compToDerivable compAC
  
    dC : Derivable (isType [] C)
    dC = compToDerivable (compTyEqRightClosed compAC)
  
  compTransportFamilyTyEq : {n : ℕ} -> {A C D F : RawType}
    -> Computable n (typeEq [] A C)
    -> HypComputable (suc n) (typeEq (A ∷ []) D F)
    -> HypComputable (suc n) (typeEq (C ∷ []) D F)
  compTransportFamilyTyEq {n} {A = A} {C = C} {D = D} {F = F}
    compAC (hypTyEqOpen _ dDF compD subDF subEqDF) =
    hypTyEqOpen
      nonemptyNeNil
      (transportFamilyTyEq dAC dC dDF)
      (compTransportFamilyTy compAC compD)
      (λ sigma fits _ accD ->
        let
          composedFits = composeFits fits (headTypeTransportFits dAC dC)
        in
        subst
          (λ J -> Computable n J)
          (cong₂ (typeEq [])
            (sym (subTyComp sigma idSubst D)
              ∙ cong (λ T -> subTy sigma T) (subTyId D))
            (sym (subTyComp sigma idSubst F)
              ∙ cong (λ T -> subTy sigma T) (subTyId F)))
          (subDF
            (compSub sigma idSubst)
            composedFits
            (singleBinderComputableFits composedFits)
            (LexLt-wf _)))
      (λ sigma tau fitsEq _ accD ->
        let
          composedFitsEq = composeEqFits fitsEq (headTypeTransportFits dAC dC)
        in
        subst
          (λ J -> Computable n J)
          (cong₂ (typeEq [])
            (sym (subTyComp sigma idSubst D)
              ∙ cong (λ T -> subTy sigma T) (subTyId D))
            (sym (subTyComp tau idSubst F)
              ∙ cong (λ T -> subTy tau T) (subTyId F)))
          (subEqDF
            (compSub sigma idSubst)
            (compSub tau idSubst)
            composedFitsEq
            (singleBinderComputableFitsEq composedFitsEq)
            (LexLt-wf _)))
    where
    dAC : Derivable (typeEq [] A C)
    dAC = compToDerivable compAC
  
    dC : Derivable (isType [] C)
    dC = compToDerivable (compTyEqRightClosed compAC)
  
  compTransTyOpenHelper : {n : ℕ} -> {gamma : Ctx} {A B C : RawType}
    -> HypComputable (suc n) (typeEq gamma A B)
    -> HypComputable (suc n) (typeEq gamma B C)
    -> HypComputable (suc n) (typeEq gamma A C)
  compTransTyOpenHelper {n} compAB@(hypTyEqOpen neq _ _ _ _) compBC =
    mkHypComputableTyEq neq
      (transTy (hypCompToDerivable compAB) (hypCompToDerivable compBC))
  
  compSymTransportFamilyTyEq : {n : ℕ} -> {A C D F : RawType}
    -> Computable n (typeEq [] A C)
    -> HypComputable (suc n) (typeEq (A ∷ []) D F)
    -> HypComputable (suc n) (typeEq (C ∷ []) F D)
  compSymTransportFamilyTyEq {n} {A = A} {C = C} {D = D} {F = F} compAC compDF =
    hypComputableTyEq
      (symTy
        (hypCompToDerivable transportedComp)
        (hypCompToDerivable (hypTyEqRight transportedComp)))
    where
    dAC : Derivable (typeEq [] A C)
    dAC = compToDerivable compAC
  
    dC : Derivable (isType [] C)
    dC = compToDerivable (compTyEqRightClosed compAC)
  
    transportedComp : HypComputable (suc n) (typeEq (C ∷ []) D F)
    transportedComp = compTransportFamilyTyEq compAC compDF
  
  compTransTm : {n : ℕ} -> {gamma : Ctx} {t u v : RawTerm} {A : RawType}
    -> HypComputable (suc n) (termEq gamma t u A)
    -> HypComputable (suc n) (termEq gamma u v A)
    -> HypComputable (suc n) (termEq gamma t v A)
  compTransTm {n} (hypTmEqOpen neq d₁ compTy₁ sub₁ subEq₁) (hypTmEqOpen _ d₂ _ sub₂ subEq₂) =
    hypTmEqOpen neq
      (transTm d₁ d₂)
      compTy₁
      (λ sigma fits cFits accD ->
        compTransTmClosed
          (sub₁ sigma fits cFits (LexLt-wf _))
          (sub₂ sigma fits cFits (LexLt-wf _)))
      (λ sigma tau fitsEq cFitsEq accD ->
        let sigmaFits = fitsEqSubstLeft fitsEq
            sigmaCFits = compFitsEqLeft cFitsEq
        in
        compTransTmClosed
          (sub₁ sigma sigmaFits sigmaCFits (LexLt-wf _))
          (subEq₂ sigma tau fitsEq cFitsEq (LexLt-wf _)))

  compSymTm : {n : ℕ} -> {gamma : Ctx} {t u : RawTerm} {A : RawType}
    -> HypComputable (suc n) (termEq gamma t u A)
    -> HypComputable (suc n) (termEq gamma u t A)
  compSymTm {n} (hypTmEqOpen neq d compTy@(hypTmOpen _ _ _ subT subEqT) sub subEq) =
    hypTmEqOpen neq
      (symTm d (assocTmRight d) (assocTmTy d))
      (hypTmEqRight (hypTmEqOpen neq d compTy sub subEq))
      (λ sigma fits cFits accD ->
        compSymTmClosed (sub sigma fits cFits (LexLt-wf _)))
      (λ sigma tau fitsEq cFitsEq accD ->
        -- Goal: Computable (termEq [] (subTm sigma u) (subTm tau t) (subTy sigma A))
        -- Chain, composing stored closures only (no SCC 2 call):
        --   sub σ           : (σt) = (σu) : σA
        --   sym of above    : (σu) = (σt) : σA
        --   subEqT σ τ      : (σt) = (τt) : σA    [from compTy's own subEq closure]
        --   trans           : (σu) = (τt) : σA  ✓
        let sigmaFits = fitsEqSubstLeft fitsEq
            sigmaCFits = compFitsEqLeft cFitsEq
            tuSigma = sub sigma sigmaFits sigmaCFits (LexLt-wf _)
            utSigma = compSymTmClosed tuSigma
            tSigmaTau = subEqT sigma tau fitsEq cFitsEq (LexLt-wf _)
        in compTransTmClosed utSigma tSigmaTau)

  weakenOneOpenTy : {n : ℕ} -> {A B C : RawType}
    -> HypComputable (suc n) (isType (A ∷ []) B)
    -> CtxWF (C ∷ A ∷ [])
    -> HypComputable (suc n) (isType (C ∷ A ∷ []) (wkTyBy 1 B))
  weakenOneOpenTy {n} {A = A} {B = B} {C = C} (hypTyOpen _ d sub subEq) wf =
    hypTyOpen
      nonemptyNeNil
      (weakenTy {gamma = A ∷ []} {delta = C ∷ []} d wf)
      (λ sigma fits cFits accD ->
        subst
          (λ T -> Computable n (isType [] T))
          (sym (subTyWkBy sigma 1 B))
          (sub
            (dropSubstBy 1 sigma)
            (dropFits (C ∷ []) fits)
            (singleBinderComputableFits (dropFits (C ∷ []) fits))
            (LexLt-wf _)))
      (λ sigma tau fitsEq cFitsEq accD ->
        subst
          (λ J -> Computable n J)
          (cong₂
            (typeEq [])
            (sym (subTyWkBy sigma 1 B))
            (sym (subTyWkBy tau 1 B)))
          (subEq
            (dropSubstBy 1 sigma)
            (dropSubstBy 1 tau)
            (dropFitsEq (C ∷ []) fitsEq)
            (singleBinderComputableFitsEq (dropFitsEq (C ∷ []) fitsEq))
            (LexLt-wf _)))

  weakenOneOpenTm : {n : ℕ} -> {A B C : RawType} {t : RawTerm}
    -> HypComputable (suc n) (hasTy (A ∷ []) t B)
    -> CtxWF (C ∷ A ∷ [])
    -> HypComputable (suc n) (hasTy (C ∷ A ∷ []) (wkTmBy 1 t) (wkTyBy 1 B))
  weakenOneOpenTm {n} {A = A} {B = B} {C = C} {t = t} (hypTmOpen _ d compB sub subEq) wf =
    hypTmOpen
      nonemptyNeNil
      (weakenTm {gamma = A ∷ []} {delta = C ∷ []} d wf)
      (weakenOneOpenTy compB wf)
      (λ sigma fits cFits accD ->
        subst
          (λ J -> Computable n J)
          (cong₂
            (hasTy [])
            (sym (subTmWkBy sigma 1 t))
            (sym (subTyWkBy sigma 1 B)))
          (sub
            (dropSubstBy 1 sigma)
            (dropFits (C ∷ []) fits)
            (singleBinderComputableFits (dropFits (C ∷ []) fits))
            (LexLt-wf _)))
      (λ sigma tau fitsEq cFitsEq accD ->
        subst
          (λ J -> Computable n J)
          (cong₃
            (termEq [])
            (sym (subTmWkBy sigma 1 t))
            (sym (subTmWkBy tau 1 t))
            (sym (subTyWkBy sigma 1 B)))
          (subEq
            (dropSubstBy 1 sigma)
            (dropSubstBy 1 tau)
            (dropFitsEq (C ∷ []) fitsEq)
            (singleBinderComputableFitsEq (dropFitsEq (C ∷ []) fitsEq))
            (LexLt-wf _)))
  
  weakenOneOpenTmEq : {n : ℕ} -> {A B C : RawType} {t u : RawTerm}
    -> HypComputable (suc n) (termEq (A ∷ []) t u B)
    -> CtxWF (C ∷ A ∷ [])
    -> HypComputable (suc n) (termEq (C ∷ A ∷ []) (wkTmBy 1 t) (wkTmBy 1 u) (wkTyBy 1 B))
  weakenOneOpenTmEq {n} {A = A} {B = B} {C = C} {t = t} {u = u}
    (hypTmEqOpen _ d compt sub subEq) wf =
    hypTmEqOpen
      nonemptyNeNil
      (weakenTmEq {gamma = A ∷ []} {delta = C ∷ []} d wf)
      (weakenOneOpenTm compt wf)
      (λ sigma fits cFits accD ->
        subst
          (λ J -> Computable n J)
          (cong₃
            (termEq [])
            (sym (subTmWkBy sigma 1 t))
            (sym (subTmWkBy sigma 1 u))
            (sym (subTyWkBy sigma 1 B)))
          (sub
            (dropSubstBy 1 sigma)
            (dropFits (C ∷ []) fits)
            (singleBinderComputableFits (dropFits (C ∷ []) fits))
            (LexLt-wf _)))
      (λ sigma tau fitsEq cFitsEq accD ->
        subst
          (λ J -> Computable n J)
          (cong₃
            (termEq [])
            (sym (subTmWkBy sigma 1 t))
            (sym (subTmWkBy tau 1 u))
            (sym (subTyWkBy sigma 1 B)))
          (subEq
            (dropSubstBy 1 sigma)
            (dropSubstBy 1 tau)
            (dropFitsEq (C ∷ []) fitsEq)
            (singleBinderComputableFitsEq (dropFitsEq (C ∷ []) fitsEq))
            (LexLt-wf _)))
  
  sigmaBranchTyHypFromMotive : {n : ℕ} -> {A B M : RawType}
    -> Derivable (isType (B ∷ A ∷ []) (sigmaBranchTy M))
    -> Computable n (isType [] A)
    -> HypComputable (suc n) (isType (A ∷ []) B)
    -> HypComputable (suc n) (isType ((tySigma A B) ∷ []) M)
    -> HypComputable (suc n) (isType (B ∷ A ∷ []) (sigmaBranchTy M))
  sigmaBranchTyHypFromMotive {n} {A = A} {B = B} {M = M}
    dBranch compA (hypTyOpen _ dB subB subEqB) (hypTyOpen _ dM subM subEqM) =
    hypTyOpen
      nonemptyNeNil
      dBranch
      branchSub
      branchSubEq
    where
    dA : Derivable (isType [] A)
    dA = compToDerivable compA
  
    oneBinderCompFits : 
      {sigma rho : Subst}
      -> (fits2 : FitsSubst [] (subTy sigma A ∷ []) rho)
      -> ComputableFits n fits2
      -> Σ
           (FitsSubst [] (A ∷ []) (compSub rho (liftSubst sigma)))
           (ComputableFits n)
    oneBinderCompFits {sigma = sigma}
      (fitsCons {sigma = theta} {t = t} (fitsNil wf) dt)
      (compFitsCons {sigma = theta} compFitsNil compt) =
      subst
        (λ zeta -> CompFitsBundle n (A ∷ []) zeta)
        (oneBinderCompSub (consSubst t theta) sigma)
        ( fitsCons
            {sigma = compSub theta sigma}
            (fitsNil {gamma = []} {delta = []} {sigma = compSub theta sigma} wf)
            (subst
              (λ T -> Derivable (hasTy [] t T))
              (subTyComp theta sigma A)
              dt)
        , compFitsCons
            {sigma = compSub theta sigma}
            compFitsNil
            (subst
              (λ T -> Computable n (hasTy [] t T))
              (subTyComp theta sigma A)
              compt))

    oneBinderCompFitsEq : 
      {sigma rho eta : Subst}
      -> (fitsEq2 : FitsEqSubst [] (subTy sigma A ∷ []) rho eta)
      -> ComputableFitsEq n fitsEq2
      -> Σ
           (FitsEqSubst [] (A ∷ [])
             (compSub rho (liftSubst sigma))
             (compSub eta (liftSubst sigma)))
           (ComputableFitsEq n)
    oneBinderCompFitsEq {sigma = sigma}
      (fitsEqCons {sigma = theta} {tau = iota} {t = t} {u = u}
        (fitsEqNil wf) dtu)
      (compFitsEqCons {sigma = theta} {tau = iota} compFitsEqNil comptu) =
      subst
        (λ zeta ->
          Σ
            (FitsEqSubst [] (A ∷ [])
              zeta
              (compSub (consSubst u iota) (liftSubst sigma)))
            (ComputableFitsEq n))
        (oneBinderCompSub (consSubst t theta) sigma)
        (subst
          (λ zeta ->
            Σ
              (FitsEqSubst [] (A ∷ [])
                (consSubst t (compSub theta sigma))
                zeta)
              (ComputableFitsEq n))
          (oneBinderCompSub (consSubst u iota) sigma)
          ( fitsEqCons
              {sigma = compSub theta sigma}
              {tau = compSub iota sigma}
              (fitsEqNil
                {gamma = []} {delta = []}
                {sigma = compSub theta sigma}
                {tau = compSub iota sigma}
                wf)
              (subst
                (λ T -> Derivable (termEq [] t u T))
                (subTyComp theta sigma A)
                dtu)
          , compFitsEqCons
              {sigma = compSub theta sigma}
              {tau = compSub iota sigma}
              compFitsEqNil
              (subst
                (λ T -> Computable n (termEq [] t u T))
                (subTyComp theta sigma A)
                comptu)))
  
    branchSub : 
      (rho : Subst)
      -> (fits :
           FitsSubst [] (B ∷ A ∷ []) rho)
      -> ComputableFits n fits
      -> Acc LexLt (substTaskLexMeasure dBranch)
      -> Computable n (isType [] (subTy rho (sigmaBranchTy M)))
    branchSub
      _
      (fitsCons
        {t = c}
        (fitsCons
          {sigma = sigma}
          {t = b}
          (fitsNil {sigma = sigma} wf)
          db)
        dc)
      (compFitsCons
        (compFitsCons {sigma = sigma} compFitsNil compb)
        compcRaw)
      _ =
      let
        compAσ = compTmToCompTy compb
        dAσ = compToDerivable compAσ
        compBσ =
          subst
            (λ T -> HypComputable (suc n) (isType (subTy sigma A ∷ []) T))
            (cong (λ rho -> subTy rho B) (liftSubstCompKeep sigma))
            (hypTyOpen
              nonemptyNeNil
              (substTyRule dB (liftFitsOne (fitsNil {gamma = []} {delta = []} {sigma = sigma} wf) dAσ))
              (λ rho fits2 compFits2 accD ->
                let
                  composed = oneBinderCompFits {sigma = sigma} fits2 compFits2
                in
                subst
                  (λ T -> Computable n (isType [] T))
                  (sym
                    (cong (λ theta -> subTy rho (subTy theta B)) (liftSubstCompKeep sigma)
                      ∙ subTyComp rho (liftSubst sigma) B))
                  (subB
                    (compSub rho (liftSubst sigma))
                    (fst composed)
                    (snd composed)
                    (LexLt-wf _)))
              (λ rho eta fitsEq2 compFitsEq2 accD ->
                let
                  composedEq = oneBinderCompFitsEq {sigma = sigma} fitsEq2 compFitsEq2
                in
                subst
                  (λ J -> Computable n J)
                  (sym
                    (cong₂ (typeEq [])
                      (cong (λ theta -> subTy rho (subTy theta B)) (liftSubstCompKeep sigma)
                        ∙ subTyComp rho (liftSubst sigma) B)
                      (cong (λ theta -> subTy eta (subTy theta B)) (liftSubstCompKeep sigma)
                        ∙ subTyComp eta (liftSubst sigma) B)))
                  (subEqB
                    (compSub rho (liftSubst sigma))
                    (compSub eta (liftSubst sigma))
                    (fst composedEq)
                    (snd composedEq)
                    (LexLt-wf _))))
        compSigma = compFSigmaClosed compAσ (hypCompToDerivable compBσ)
        compc =
          subst
            (λ T -> Computable n (hasTy [] c T))
            (cong
              (λ rho -> subTy rho B)
              (cong (consSubst b) (sym (compSubIdLeft sigma))
                ∙ oneBinderCompSub (singleSubst b) sigma)
              ∙ sym (subTyComp (singleSubst b) (liftSubst sigma) B))
            compcRaw
        compPair = compISigmaClosed compb compc compSigma
        pairFits : 
          FitsSubst [] ((tySigma A B) ∷ []) (consSubst (tmPair b c) sigma)
        pairFits =
          fitsCons
            (fitsNil {gamma = []} {delta = []} {sigma = sigma} wf)
            (compToDerivable compPair)
        pairCompFits : ComputableFits n pairFits
        pairCompFits =
          compFitsCons {sigma = sigma} compFitsNil compPair
      in
      subst
        (λ T -> Computable n (isType [] T))
        (sym (sigmaBranchTyCompTail sigma b c M))
        (subM (consSubst (tmPair b c) sigma) pairFits pairCompFits (LexLt-wf _))
  
    branchSubEq : 
      (rho eta : Subst)
      -> (fitsEq :
           FitsEqSubst [] (B ∷ A ∷ []) rho eta)
      -> ComputableFitsEq n fitsEq
      -> Acc LexLt (substTaskLexMeasure dBranch)
      -> Computable n (typeEq [] (subTy rho (sigmaBranchTy M)) (subTy eta (sigmaBranchTy M)))
    branchSubEq
      _
      _
      (fitsEqCons
        {t = c}
        {u = f}
        (fitsEqCons
          {sigma = sigma}
          {tau = tau}
          {t = b}
          {u = e}
          (fitsEqNil {sigma = sigma} {tau = tau} wf)
          dbe)
        dcf)
      (compFitsEqCons
        (compFitsEqCons {sigma = sigma} {tau = tau} compFitsEqNil compbe)
        compcfRaw)
      _ =
      let
        compb = compTmEqLeft compbe
        compAσ = compTmToCompTy compb
        dAσ = compToDerivable compAσ
        compBσ =
          subst
            (λ T -> HypComputable (suc n) (isType (subTy sigma A ∷ []) T))
            (cong (λ rho -> subTy rho B) (liftSubstCompKeep sigma))
            (hypTyOpen
              nonemptyNeNil
              (substTyRule dB (liftFitsOne (fitsNil {gamma = []} {delta = []} {sigma = sigma} wf) dAσ))
              (λ rho fits2 compFits2 accD ->
                let
                  composed = oneBinderCompFits {sigma = sigma} fits2 compFits2
                in
                subst
                  (λ T -> Computable n (isType [] T))
                  (sym
                    (cong (λ theta -> subTy rho (subTy theta B)) (liftSubstCompKeep sigma)
                      ∙ subTyComp rho (liftSubst sigma) B))
                  (subB
                    (compSub rho (liftSubst sigma))
                    (fst composed)
                    (snd composed)
                    (LexLt-wf _)))
              (λ rho eta fitsEq2 compFitsEq2 accD ->
                let
                  composedEq = oneBinderCompFitsEq {sigma = sigma} fitsEq2 compFitsEq2
                in
                subst
                  (λ J -> Computable n J)
                  (sym
                    (cong₂ (typeEq [])
                      (cong (λ theta -> subTy rho (subTy theta B)) (liftSubstCompKeep sigma)
                        ∙ subTyComp rho (liftSubst sigma) B)
                      (cong (λ theta -> subTy eta (subTy theta B)) (liftSubstCompKeep sigma)
                        ∙ subTyComp eta (liftSubst sigma) B)))
                  (subEqB
                    (compSub rho (liftSubst sigma))
                    (compSub eta (liftSubst sigma))
                    (fst composedEq)
                    (snd composedEq)
                    (LexLt-wf _))))
        compSigma = compFSigmaClosed compAσ (hypCompToDerivable compBσ)
        compcf =
          subst
            (λ T -> Computable n (termEq [] c f T))
            (cong
              (λ rho -> subTy rho B)
            (cong (consSubst b) (sym (compSubIdLeft sigma))
                ∙ oneBinderCompSub (singleSubst b) sigma)
              ∙ sym (subTyComp (singleSubst b) (liftSubst sigma) B))
            compcfRaw
        compeA = compTmEqRightClosed compbe
        compc = compTmEqLeft compcf
        compfA = compTmEqRightClosed compcf
        compf =
          compConvTmClosed compfA (compSingleEqSubstTyClosed compBσ compbe (LexLt-wf _))
        compPairLeft = compISigmaClosed compb compc compSigma
        compPairRight = compISigmaClosed compeA compf compSigma
        compPairEq =
          compTmEqClosedSigma
            (iSigmaEq
              (compToDerivable compbe)
              (compToDerivable compcf)
              dAσ
              (hypCompToDerivable compBσ))
            compPairLeft
            compPairRight
            evalSigma
            evalPair
            evalPair
            compbe
            compcf
        pairFitsEq : 
          FitsEqSubst [] ((tySigma A B) ∷ [])
            (consSubst (tmPair b c) sigma)
            (consSubst (tmPair e f) tau)
        pairFitsEq =
          fitsEqCons
            (fitsEqNil {gamma = []} {delta = []} {sigma = sigma} {tau = tau} wf)
            (compToDerivable compPairEq)
        pairCompFitsEq : ComputableFitsEq n pairFitsEq
        pairCompFitsEq =
          compFitsEqCons {sigma = sigma} {tau = tau} compFitsEqNil compPairEq
      in
      subst
        (λ J -> Computable n J)
        (sym
          (cong₂
            (typeEq [])
            (sigmaBranchTyCompTail sigma b c M)
            (sigmaBranchTyCompTail tau e f M)))
        (subEqM
          (consSubst (tmPair b c) sigma)
          (consSubst (tmPair e f) tau)
          pairFitsEq
          pairCompFitsEq
          (LexLt-wf _))
  
  abstract
    sigmaTyFamHypClosed : {n : ℕ} -> {A B : RawType}
      -> Computable n (isType [] (tySigma A B))
      -> HypComputable (suc n) (isType (A ∷ []) B)
    sigmaTyFamHypClosed
      {n} (compTyClosedSigma {B = A} {C = B} _ evalSigma _ _ dB) =
      mkHypComputableTy nonemptyNeNil dB (LexLt-wf _)
    sigmaTyFamHypClosed (compTyClosedTop _ () _)
    sigmaTyFamHypClosed (compTyClosedEq _ () _ _ _ _)
    sigmaTyFamHypClosed (compTyClosedQtr _ () _ _)

    sigmaTyFamEqSubClosed : {n : ℕ} -> {A B : RawType} {t u : RawTerm}
      -> Computable n (isType [] (tySigma A B))
      -> Computable n (termEq [] t u A)
      -> Computable n (typeEq [] (subTy (singleSubst t) B) (subTy (singleSubst u) B))
    sigmaTyFamEqSubClosed {n} compSigma comptu =
      compSingleEqSubstTyClosed (sigmaTyFamHypClosed compSigma) comptu (LexLt-wf _)
  
  compConvTmClosedAcc : {n : ℕ} -> {t : RawTerm} {A B : RawType}
    -> Computable n (hasTy [] t A)
    -> Computable n (typeEq [] A B)
    -> Acc _<_ (closedTaskMeasure A)
    -> Computable n (hasTy [] t B)
  compConvTmClosedAcc {n} comp (compTyEqClosedTop dAB compA compB evA evB) (acc rs) =
    let
      inv = invertTopTm comp evA
      open ClosedTopTmInv inv
      tyInv = invertTopTy (compTmToCompTy comp) evA
      open ClosedTopTyInv tyInv
      topEqB = transTy (symTy topTyCorr (fTop wfNil)) dAB
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
      sigmaEqB =
        transTy
          (symTy
            sigmaTyCorr
            (fSigma (compToDerivable sigmaTyCompHead)
              sigmaTyFamDeriv))
          dAB
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
      compDFa = compSingleSubstTyEqClosed (hypComputableTyEq dDF) sigmaTmCompFst (LexLt-wf _)
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
      eqEqB =
        transTy
          (symTy
            eqTyCorr
            (fEq
              (compToDerivable eqTyCompBase)
              (compToDerivable eqTyCompLeft)
              (compToDerivable eqTyCompRight)))
          dAB
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
      qtrEqB =
        transTy
          (symTy qtrTyCorr (fQtr (compToDerivable qtrTyCompBase)))
          dAB
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
  
  compConvTmEqClosedAcc : {n : ℕ} -> {t u : RawTerm} {A B : RawType}
    -> Computable n (termEq [] t u A)
    -> Computable n (typeEq [] A B)
    -> Acc _<_ (openTaskMeasure A)
    -> Computable n (termEq [] t u B)
  compConvTmEqClosedAcc
    {n} {t = t} {u = u} {A = A} {B = B}
    comp
    compAB@(compTyEqClosedTop dAB compA compB evA evB)
    (acc rs) =
    let
      comp' =
        subst
          (λ X -> Computable n (termEq [] t u X))
          (evalTopPath evA)
          comp
      inv = invertTopTmEq0 comp'
      open ClosedTopTmEqInv inv
      compAB' = subst (λ X -> Computable n (typeEq [] X B)) (evalTopPath evA) compAB
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
    {n} {t = t} {u = u} {A = A} {B = B}
    comp
    compAB@(compTyEqClosedSigma {C = C} {D = D} dAB compA compB evA evB compCE dDF)
    (acc rs) =
    let
      comp' =
        subst
          (λ X -> Computable n (termEq [] t u X))
          (evalSigmaPath evA)
          comp
      inv = invertSigmaTmEq0 comp'
      open ClosedSigmaTmEqInv inv
      compA' =
        subst
          (λ X -> Computable n (isType [] X))
          (evalSigmaPath evA)
          compA
      tyInv = invertSigmaTy compA' evalSigma
      open ClosedSigmaTyInv tyInv
      compAB' = subst (λ X -> Computable n (typeEq [] X B)) (evalSigmaPath evA) compAB
      compLeftA : Computable n (hasTy [] t (tySigma C D))
      compLeftA = sigmaTmEqCompLeft
      compRightA : Computable n (hasTy [] u (tySigma C D))
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
      compDFa = compSingleSubstTyEqClosed (hypComputableTyEq dDF) (compTmEqLeft sigmaTmEqCompFst) (LexLt-wf _)
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
    {n} {t = t} {u = u} {A = A} {B = B}
    comp
    compAB@(compTyEqClosedEq {C = C} {a = a} {b = b} dAB compA compB evA evB compCD compac compbd)
    (acc rs) =
    let
      comp' =
        subst
          (λ X -> Computable n (termEq [] t u X))
          (evalEqPath evA)
          comp
      inv = invertEqTmEq0 comp'
      open ClosedEqTmEqInv inv
      compA' =
        subst
          (λ X -> Computable n (isType [] X))
          (evalEqPath evA)
          compA
      tyInv = invertEqTy compA' evalEq
      open ClosedEqTyInv tyInv
      compAB' = subst (λ X -> Computable n (typeEq [] X B)) (evalEqPath evA) compAB
      compLeftA : Computable n (hasTy [] t (tyEq C a b))
      compLeftA = eqTmEqCompLeft
      compRightA : Computable n (hasTy [] u (tyEq C a b))
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
    {n} {t = t} {u = u} {A = A} {B = B}
    comp
    compAB@(compTyEqClosedQtr {C = C} dAB compA compB evA evB compCD)
    (acc rs) =
    let
      comp' =
        subst
          (λ X -> Computable n (termEq [] t u X))
          (evalQtrPath evA)
          comp
      inv = invertQtrTmEq0 comp'
      open ClosedQtrTmEqInv inv
      compA' =
        subst
          (λ X -> Computable n (isType [] X))
          (evalQtrPath evA)
          compA
      tyInv = invertQtrTy compA' evalQtr
      open ClosedQtrTyInv tyInv
      compAB' = subst (λ X -> Computable n (typeEq [] X B)) (evalQtrPath evA) compAB
      compLeftA : Computable n (hasTy [] t (tyQtr C))
      compLeftA = qtrTmEqCompLeft
      compRightA : Computable n (hasTy [] u (tyQtr C))
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
  
  compSymTmClosedAcc : {n : ℕ} -> {t u : RawTerm} {A : RawType}
    -> Computable n (termEq [] t u A)
    -> Acc _<_ (closedTaskMeasure A)
    -> Computable n (termEq [] u t A)
  compSymTmClosedAcc {n} (compTmEqClosedTop d compt compu evA evt evu) (acc rs) =
    compTmEqClosedTop
      (symTm
        d
        (compToDerivable compu)
        (compToDerivable (compTmToCompTy compt)))
      compu
      compt
      evA
      evu
      evt
  compSymTmClosedAcc
    {n} comp@(compTmEqClosedSigma {a = a} {A = B} {B = C} d compt compu evA evt evu compac compbd)
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
          (λ X -> Computable n (isType [] X))
          (evalSigmaPath evA)
          (compTmToCompTy compt)
      compca = compSymTmClosedAcc compac acFst
      compdb = compSymTmClosedAcc compbd acSndClosed
      compBac = sigmaTyFamEqSubClosed compSigma compac
      compdb' = compConvTmEqClosedAcc compdb compBac acSndOpen
    in
    compTmEqClosedSigma
      (symTm
        d
        (compToDerivable compu)
        (compToDerivable (compTmToCompTy compt)))
      compu
      compt
      evA
      evu
      evt
      compca
      compdb'
  compSymTmClosedAcc {n} (compTmEqClosedEq d compt compu evA evt evu compab) (acc rs) =
    compTmEqClosedEq
      (symTm
        d
        (compToDerivable compu)
        (compToDerivable (compTmToCompTy compt)))
      compu
      compt
      evA
      evu
      evt
      compab
  compSymTmClosedAcc {n} (compTmEqClosedQtr d compt compu evA evt evu compa compb) (acc rs) =
    compTmEqClosedQtr
      (symTm
        d
        (compToDerivable compu)
        (compToDerivable (compTmToCompTy compt)))
      compu
      compt
      evA
      evu
      evt
      compb
      compa
  
  compTransTmClosedAcc : {n : ℕ} -> {t u v : RawTerm} {A : RawType}
    -> Computable n (termEq [] t u A)
    -> Computable n (termEq [] u v A)
    -> Acc _<_ (closedTaskMeasure A)
    -> Computable n (termEq [] t v A)
  compTransTmClosedAcc {n} (compTmEqClosedTop d₁ compt _ evA evt evu) comp₂ (acc rs) =
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
    {n} comp₁@(compTmEqClosedSigma {a = a} {b = b} {c = c} {d = d} {A = C} {B = D}
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
          (λ x -> Computable n (termEq [] x sigmaTmEqRightFst C))
          (sym c≡left)
          sigmaTmEqCompFst
      compdfC =
        subst
          (λ x -> Computable n (termEq [] x sigmaTmEqRightSnd (subTy (singleSubst c) D)))
          (sym d≡left)
          (subst
            (λ T -> Computable n (termEq [] sigmaTmEqLeftSnd sigmaTmEqRightSnd T))
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
          (λ X -> Computable n (isType [] X))
          (evalSigmaPath evA)
          (compTmToCompTy compt)
      compca = compSymTmClosedAcc compac acFst
      compae = compTransTmClosedAcc compac compce acFst
      compDca = sigmaTyFamEqSubClosed compSigma compca
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
  compTransTmClosedAcc {n} comp₁@(compTmEqClosedEq d₁ compt _ evA evt evu compab) comp₂ (acc rs) =
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
  compTransTmClosedAcc {n} comp₁@(compTmEqClosedQtr d₁ compt _ evA evt evu compa compb) comp₂ (acc rs) =
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
  
  compConvTmClosed : {n : ℕ} -> {t : RawTerm} {A B : RawType}
    -> Computable n (hasTy [] t A)
    -> Computable n (typeEq [] A B)
    -> Computable n (hasTy [] t B)
  compConvTmClosed {n} {A = A} comp compAB =
    compConvTmClosedAcc comp compAB (<-wellfounded (closedTaskMeasure A))
  
  compConvTmEqClosed : {n : ℕ} -> {t u : RawTerm} {A B : RawType}
    -> Computable n (termEq [] t u A)
    -> Computable n (typeEq [] A B)
    -> Computable n (termEq [] t u B)
  compConvTmEqClosed {n} {A = A} comp compAB =
    compConvTmEqClosedAcc comp compAB (<-wellfounded (openTaskMeasure A))
  
  compSymTmClosed : {n : ℕ} -> {t u : RawTerm} {A : RawType}
    -> Computable n (termEq [] t u A)
    -> Computable n (termEq [] u t A)
  compSymTmClosed {n} {A = A} comp =
    compSymTmClosedAcc comp (<-wellfounded (closedTaskMeasure A))
  
  compTransTmClosed : {n : ℕ} -> {t u v : RawTerm} {A : RawType}
    -> Computable n (termEq [] t u A)
    -> Computable n (termEq [] u v A)
    -> Computable n (termEq [] t v A)
  compTransTmClosed {n} {A = A} comp₁ comp₂ =
    compTransTmClosedAcc comp₁ comp₂ (<-wellfounded (closedTaskMeasure A))
  
  compSymTyClosedAcc : {n : ℕ} -> {A B : RawType}
    -> Computable n (typeEq [] A B)
    -> Acc _<_ (closedTaskMeasure A)
    -> Computable n (typeEq [] B A)
  compSymTyClosedAcc {n} (compTyEqClosedTop d compA compB evA evB) (acc rs) =
    compTyEqClosedTop (symTy d (compToDerivable compB)) compB compA evB evA
  compSymTyClosedAcc
    {n} {A = AΣ}
    (compTyEqClosedSigma {C = C} {D = D} {E = E} {F = F} d compA compB evA evB compCE compDF)
    (acc rs) =
    let
      acHead =
        rs _ (rewriteClosedUpper {H = tySigma C D} (evalSigmaPath evA)
          (smallerClosedTask<ClosedTask {A = C} {B = tySigma C D}
            (tyDepth-fst<Sigma C D)))
    in
      compTyEqClosedSigma
        (symTy d (compToDerivable compB))
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
    {n} (compTyEqClosedEq {C = C} {a = a} {b = b} d compA compB evA evB compCD compac compbd)
    (acc rs) =
    let
      acBase =
        rs _ (rewriteClosedUpper {H = tyEq C a b} (evalEqPath evA)
          (smallerClosedTask<ClosedTask {A = C} {B = tyEq C a b}
            (tyDepth-base<Eq C a b)))
    in
    compTyEqClosedEq
      (symTy d (compToDerivable compB))
      compB
      compA
      evB
      evA
      (compSymTyClosedAcc compCD acBase)
      (compConvTmEqClosed (compSymTmClosed compac) compCD)
      (compConvTmEqClosed (compSymTmClosed compbd) compCD)
  compSymTyClosedAcc
    {n} (compTyEqClosedQtr {C = C} d compA compB evA evB compCD)
    (acc rs) =
    let
      acBase =
        rs _ (rewriteClosedUpper {H = tyQtr C} (evalQtrPath evA)
          (smallerClosedTask<ClosedTask {A = C} {B = tyQtr C}
            (tyDepth-base<Qtr C)))
    in
    compTyEqClosedQtr
      (symTy d (compToDerivable compB))
      compB
      compA
      evB
      evA
      (compSymTyClosedAcc compCD acBase)
  
  compTransTyClosedAcc : {n : ℕ} -> {A B C : RawType}
    -> Computable n (typeEq [] A B)
    -> Computable n (typeEq [] B C)
    -> Acc _<_ (closedTaskMeasure A)
    -> Computable n (typeEq [] A C)
  compTransTyClosedAcc
    {n} (compTyEqClosedTop dAB compA compB evA evB)
    (compTyEqClosedTop dBC _ compC evB' evC)
    (acc rs) =
    compTyEqClosedTop
      (transTy dAB dBC)
      compA
      compC
      evA
      evC
  compTransTyClosedAcc
    {n} (compTyEqClosedTop _ _ _ _ evB)
    (compTyEqClosedSigma _ _ _ evB' _ _ _)
    _ =
    Empty.rec (topNeSigma (sym (evalTopPath evB) ∙ evalSigmaPath evB'))
  compTransTyClosedAcc
    {n} (compTyEqClosedTop _ _ _ _ evB)
    (compTyEqClosedEq _ _ _ evB' _ _ _ _)
    _ =
    Empty.rec (topNeEq (sym (evalTopPath evB) ∙ evalEqPath evB'))
  compTransTyClosedAcc
    {n} (compTyEqClosedTop _ _ _ _ evB)
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
    {n} (compTyEqClosedEq {C = C} {a = a} {b = b} dAB compA compB evA evB compCD compac compbd)
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
    {n} (compTyEqClosedQtr {C = C} dAB compA compB evA evB compCD)
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
  
  compSymTyClosed : {n : ℕ} -> {A B : RawType}
    -> Computable n (typeEq [] A B)
    -> Computable n (typeEq [] B A)
  compSymTyClosed {n} {A = A} comp =
    compSymTyClosedAcc comp (<-wellfounded (closedTaskMeasure A))
  
  compTransTyClosed : {n : ℕ} -> {A B C : RawType}
    -> Computable n (typeEq [] A B)
    -> Computable n (typeEq [] B C)
    -> Computable n (typeEq [] A C)
  compTransTyClosed {n} {A = A} comp₁ comp₂ =
    compTransTyClosedAcc comp₁ comp₂ (<-wellfounded (closedTaskMeasure A))
  
  computableTmClosedCore : {n : ℕ} -> {t : RawTerm} {A : RawType}
    -> Derivable (hasTy [] t A)
    -> Computable n (hasTy [] t A)
  computableTmClosedCore {n} {t = t} {A = A} d =
    subst
      (λ J -> Computable n J)
      (cong₂ (hasTy []) (subTmId t) (subTyId A))
      (substTmClosed d (fitsNil {gamma = []} {delta = []} {sigma = idSubst} wfNil))
  
  computableTmEqClosedCore : {n : ℕ} -> {t u : RawTerm} {A : RawType}
    -> Derivable (termEq [] t u A)
    -> Computable n (termEq [] t u A)
  computableTmEqClosedCore {n} {t = t} {u = u} {A = A} d =
    subst
      (λ J -> Computable n J)
      (cong₃ (termEq []) (subTmId t) (subTmId u) (subTyId A))
      (substTmEqClosed d (fitsNil {gamma = []} {delta = []} {sigma = idSubst} wfNil))
  
  computableTmClosed : {n : ℕ} -> {t : RawTerm} {A : RawType}
    -> Derivable (hasTy [] t A)
    -> Computable n (hasTy [] t A)
  computableTmClosed {n} = computableTmClosedCore
  
  computableTmEqClosed : {n : ℕ} -> {t u : RawTerm} {A : RawType}
    -> Derivable (termEq [] t u A)
    -> Computable n (termEq [] t u A)
  computableTmEqClosed {n} = computableTmEqClosedCore

computableTyClosedCore : {n : ℕ} -> {A : RawType}
  -> Derivable (isType [] A)
  -> Computable n (isType [] A)
computableTyClosedCore {n} {A = A} d =
  subst
    (λ T -> Computable n (isType [] T))
    (subTyId A)
    (substDerivTyCompCF
      d
      (fitsNil {gamma = []} {delta = []} {sigma = idSubst} wfNil) (fitsToCompFits (fitsNil {gamma = []} {delta = []} {sigma = idSubst} wfNil)) (LexLt-wf _))

computableTyEqClosedCore : {n : ℕ} -> {A B : RawType}
  -> Derivable (typeEq [] A B)
  -> Computable n (typeEq [] A B)
computableTyEqClosedCore {n} {A = A} {B = B} d =
  subst
    (λ J -> Computable n J)
    (cong₂ (typeEq []) (subTyId A) (subTyId B))
    (substDerivTyEqCompCF
      d
      (fitsNil {gamma = []} {delta = []} {sigma = idSubst} wfNil) (fitsToCompFits (fitsNil {gamma = []} {delta = []} {sigma = idSubst} wfNil)) (LexLt-wf _))

computableTyClosed : {n : ℕ} -> {A : RawType}
  -> Derivable (isType [] A)
  -> Computable n (isType [] A)
computableTyClosed {n} = computableTyClosedCore

computableTyEqClosed : {n : ℕ} -> {A B : RawType}
  -> Derivable (typeEq [] A B)
  -> Computable n (typeEq [] A B)
computableTyEqClosed {n} = computableTyEqClosedCore

substDerivTyComp : {n : ℕ} -> {gamma : Ctx} {A : RawType} {sigma : Subst}
  -> Derivable (isType gamma A)
  -> FitsSubst [] gamma sigma
  -> Computable n (isType [] (subTy sigma A))
substDerivTyComp {n} d fits = substDerivTyCompCF d fits (fitsToCompFits fits) (LexLt-wf _)

substDerivTmComp : {n : ℕ} -> {gamma : Ctx} {t : RawTerm} {A : RawType} {sigma : Subst}
  -> Derivable (hasTy gamma t A)
  -> FitsSubst [] gamma sigma
  -> Computable n (hasTy [] (subTm sigma t) (subTy sigma A))
substDerivTmComp {n} d fits = substDerivTmCompCF d fits (fitsToCompFits fits) (LexLt-wf _)

substDerivTmEqComp : {n : ℕ} -> {gamma : Ctx} {t u : RawTerm} {A : RawType} {sigma : Subst}
  -> Derivable (termEq gamma t u A)
  -> FitsSubst [] gamma sigma
  -> Computable n (termEq [] (subTm sigma t) (subTm sigma u) (subTy sigma A))
substDerivTmEqComp {n} d fits = substDerivTmEqCompCF d fits (fitsToCompFits fits) (LexLt-wf _)

substDerivTyEqComp : {n : ℕ} -> {gamma : Ctx} {A B : RawType} {sigma : Subst}
  -> Derivable (typeEq gamma A B)
  -> FitsSubst [] gamma sigma
  -> Computable n (typeEq [] (subTy sigma A) (subTy sigma B))
substDerivTyEqComp {n} d fits = substDerivTyEqCompCF d fits (fitsToCompFits fits) (LexLt-wf _)

eqSubDerivTyComp : {n : ℕ} -> {gamma : Ctx} {A : RawType} {sigma tau : Subst}
  -> Derivable (isType gamma A)
  -> FitsEqSubst [] gamma sigma tau
  -> Computable n (typeEq [] (subTy sigma A) (subTy tau A))
eqSubDerivTyComp {n} d fitsEq = eqSubDerivTyCompCF d fitsEq (fitsEqToCompFitsEq fitsEq) (LexLt-wf _)

eqSubDerivTmComp : {n : ℕ} -> {gamma : Ctx} {t : RawTerm} {A : RawType} {sigma tau : Subst}
  -> Derivable (hasTy gamma t A)
  -> FitsEqSubst [] gamma sigma tau
  -> Computable n (termEq [] (subTm sigma t) (subTm tau t) (subTy sigma A))
eqSubDerivTmComp {n} d fitsEq = eqSubDerivTmCompCF d fitsEq (fitsEqToCompFitsEq fitsEq) (LexLt-wf _)

eqSubDerivTmEqComp : {n : ℕ} -> {gamma : Ctx} {t u : RawTerm} {A : RawType} {sigma tau : Subst}
  -> Derivable (termEq gamma t u A)
  -> FitsEqSubst [] gamma sigma tau
  -> Computable n (termEq [] (subTm sigma t) (subTm tau u) (subTy sigma A))
eqSubDerivTmEqComp {n} d fitsEq = eqSubDerivTmEqCompCF d fitsEq (fitsEqToCompFitsEq fitsEq) (LexLt-wf _)

eqSubDerivTyEqComp : {n : ℕ} -> {gamma : Ctx} {A B : RawType} {sigma tau : Subst}
  -> Derivable (typeEq gamma A B)
  -> FitsEqSubst [] gamma sigma tau
  -> Computable n (typeEq [] (subTy sigma A) (subTy tau B))
eqSubDerivTyEqComp {n} d fitsEq = eqSubDerivTyEqCompCF d fitsEq (fitsEqToCompFitsEq fitsEq) (LexLt-wf _)

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
  canonicalType (computableTyClosed {n = 0} d)
canonicalFormTheorem {J = typeEq [] A B} d =
  canonicalTypeEq (computableTyEqClosed {n = 0} d)
canonicalFormTheorem {J = hasTy [] t A} d =
  canonicalTerm (computableTmClosed {n = 0} d)
canonicalFormTheorem {J = termEq [] t u A} d =
  canonicalTermEq (computableTmEqClosed {n = 0} d)
canonicalFormTheorem {J = isType (_ ∷ _) A} d = tt
canonicalFormTheorem {J = typeEq (_ ∷ _) A B} d = tt
canonicalFormTheorem {J = hasTy (_ ∷ _) t A} d = tt
canonicalFormTheorem {J = termEq (_ ∷ _) t u A} d = tt
