{-# OPTIONS --safe #-}

module Tait.Env where

open import Tait.Prelude
open import Data.List.Base using ([] ; _∷_ ; _++_ ; length)
open import Data.Nat using (ℕ ; zero ; suc)

open import Tait.Syntax
open import Tait.Context
open import Tait.Substitution
open import Tait.Computable

data Env : Ctx -> Subst -> Type where
  -- The empty context constrains no variable, so any substitution
  -- fits it: `Env []` is total in the substitution. (Needed by
  -- `fundFits` on `fitsNil`, which must yield `Env [] (compSub σ τ)`.)
  envNil : {sigma : Subst} -> Env [] sigma
  envCons : {gamma : Ctx} {A : RawType} {sigma : Subst} {a : RawTerm}
    -> Env gamma sigma
    -> Computable (subTy sigma A) a
    -> Env (A ∷ gamma) (consSubst a sigma)

envExtend : {gamma : Ctx} {A : RawType} {sigma : Subst} {a : RawTerm}
  -> Env gamma sigma
  -> Computable (subTy sigma A) a
  -> Env (A ∷ gamma) (consSubst a sigma)
envExtend = envCons

wkTyBy-zero : (A : RawType) -> wkTyBy 0 A ≡ A
wkTyBy-zero A =
  renTyKeepSubstBy 0 A ∙ subTyId A

lookupWkCancel : (sigma : Subst) (a : RawTerm) (k : ℕ) (A : RawType)
  -> subTy (consSubst a sigma) (wkTyBy (suc k) A)
       ≡ subTy sigma (wkTyBy k A)
lookupWkCancel sigma a k A =
  subTyRen (consSubst a sigma) (addRen (suc k)) A
  ∙ sym (subTyRen sigma (addRen k) A)

lookupHereTy : (sigma : Subst) (a : RawTerm) (A : RawType)
  -> subTy (consSubst a sigma) (wkTyBy 1 A) ≡ subTy sigma A
lookupHereTy sigma a A =
  lookupWkCancel sigma a 0 A ∙ cong (subTy sigma) (wkTyBy-zero A)

envLookup : {gamma delta : Ctx} {A : RawType} {sigma : Subst}
  -> Env (delta ++ (A ∷ gamma)) sigma
  -> Computable (subTy sigma (wkTyBy (suc (length delta)) A))
       (applySubst sigma (length delta))
envLookup {delta = []} {A = A} (envCons {sigma = sigma} {a = a} ρ ca) =
  subst (λ X -> Computable X a) (sym (lookupHereTy sigma a A)) ca
envLookup {delta = D ∷ delta} {A = A} (envCons {sigma = sigma} {a = a} ρ ca) =
  subst
    (λ X -> Computable X (applySubst sigma (length delta)))
    (sym (lookupWkCancel sigma a (suc (length delta)) A))
    (envLookup {delta = delta} ρ)
