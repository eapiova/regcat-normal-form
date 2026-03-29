
{-# OPTIONS --safe #-}

module TReg.MainTheorem where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Empty.Base as Empty using (rec)
open import Cubical.Data.Sigma using (Σ-syntax ; _×_ ; _,_)
open import Cubical.Data.List.Base using ([] ; _∷_)

open import TReg.Syntax
open import TReg.Context
open import TReg.Evaluation
open import TReg.Derivability
open import TReg.Computability
open import TReg.Inversion

canonicalType :
  {A : RawType} ->
  Computable (isType [] A) ->
  Σ[ G ∈ RawType ] (A =>t G) × Derivable (typeEq [] A G)
canonicalType (compTyClosedTop _ ev corr) = tyTop , (ev , corr)
canonicalType (compTyClosedSigma {B = B} {C = C} _ ev corr _ _) =
  tySigma B C , (ev , corr)
canonicalType (compTyClosedEq {B = B} {a = a} {b = b} _ ev corr _ _ _) =
  tyEq B a b , (ev , corr)
canonicalType (compTyClosedQtr {B = B} _ ev corr _) =
  tyQtr B , (ev , corr)
canonicalType (compTyOpen neq _ _ _) = Empty.rec (neq refl)

canonicalTypeEq :
  {A B : RawType} ->
  Computable (typeEq [] A B) ->
  Σ[ G ∈ RawType ] Σ[ H ∈ RawType ] (A =>t G) × (B =>t H)
canonicalTypeEq (compTyEqClosedTop _ _ _ evA evB) =
  tyTop , tyTop , (evA , evB)
canonicalTypeEq (compTyEqClosedSigma {C = C} {D = D} {E = E} {F = F} _ _ _ evA evB _ _) =
  tySigma C D , tySigma E F , (evA , evB)
canonicalTypeEq (compTyEqClosedEq _ _ _ evA evB _ _ _) with evA | evB
... | evalEq {A = C} {a = a} {b = b} | evalEq {A = D} {a = c} {b = d} =
  tyEq C a b , tyEq D c d , (evA , evB)
canonicalTypeEq (compTyEqClosedQtr {C = C} {D = D} _ _ _ evA evB _) =
  tyQtr C , tyQtr D , (evA , evB)
canonicalTypeEq (compTyEqOpen neq _ _ _ _) = Empty.rec (neq refl)

canonicalTerm :
  {t : RawTerm} {A : RawType} ->
  Computable (hasTy [] t A) ->
  Σ[ g ∈ RawTerm ] Σ[ G ∈ RawType ] (t =>e g) × (A =>t G)
canonicalTerm (compTmClosedTop _ _ evA evt _) =
  tmStar , tyTop , (evt , evA)
canonicalTerm (compTmClosedSigma {a = a} {b = b} {A = A} {B = B} _ _ evG evt _ _ _) =
  tmPair a b , tySigma A B , (evt , evG)
canonicalTerm (compTmClosedEq {t = t₀} {a = a₀} {b = b₀} {A = A₀} {G = G₀}
  _ _ evG evt _ _) =
  tmR , tyEq A₀ a₀ b₀ , (evt , evG)
canonicalTerm (compTmClosedQtr {a = a} {A = A} _ _ evG evt _ _) =
  tmClass a , tyQtr A , (evt , evG)
canonicalTerm (compTmOpen neq _ _ _ _) = Empty.rec (neq refl)

canonicalTermEq :
  {t u : RawTerm} {A : RawType} ->
  Computable (termEq [] t u A) ->
  Σ[ g ∈ RawTerm ] Σ[ h ∈ RawTerm ] Σ[ G ∈ RawType ] (t =>e g) × (u =>e h) × (A =>t G)
canonicalTermEq (compTmEqClosedTop _ _ _ evA evt evu) =
  tmStar , tmStar , tyTop , (evt , evu , evA)
canonicalTermEq (compTmEqClosedSigma {a = a} {b = b} {c = c} {d = d} {A = A} {B = B}
  _ _ _ evG evt evu _ _) =
  tmPair a b , tmPair c d , tySigma A B , (evt , evu , evG)
canonicalTermEq (compTmEqClosedEq {t = t₀} {u = u₀} {a = a₀} {b = b₀}
  {A = A₀} {G = G₀} _ _ _ evG evt evu _) =
  tmR , tmR , tyEq A₀ a₀ b₀ , (evt , evu , evG)
canonicalTermEq (compTmEqClosedQtr {a = a} {b = b} {A = A} _ _ _ evG evt evu _ _) =
  tmClass a , tmClass b , tyQtr A , (evt , evu , evG)
canonicalTermEq (compTmEqOpen neq _ _ _ _) = Empty.rec (neq refl)
