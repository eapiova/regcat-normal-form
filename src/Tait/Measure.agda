{-# OPTIONS --safe #-}

module Tait.Measure where

open import Tait.Prelude
open import Data.Nat using (ℕ ; zero ; suc ; _+_ ; _<_)
open import Data.Nat.Base using () renaming (s≤s to suc-≤-suc)
open import Data.Nat.Properties using ()
  renaming (m≤m+n to ≤SumLeft ; m≤n+m to ≤SumRight)

open import Tait.Syntax
open import Tait.Substitution

-- Type depth: measures the nesting of type constructors
tyDepth : RawType -> ℕ
tyDepth tyTop = 0
tyDepth (tySigma A B) = suc (tyDepth A + tyDepth B)

-- Substitution preserves type depth
tyDepth-subTy : (sigma : Subst) -> (A : RawType) -> tyDepth (subTy sigma A) ≡ tyDepth A
tyDepth-subTy sigma tyTop = refl
tyDepth-subTy sigma (tySigma A B) =
  cong suc (cong₂ _+_ (tyDepth-subTy sigma A) (tyDepth-subTy (liftSubst sigma) B))

-- Renaming preserves type depth
tyDepth-renTy : (rho : Ren) -> (A : RawType) -> tyDepth (renTy rho A) ≡ tyDepth A
tyDepth-renTy rho tyTop = refl
tyDepth-renTy rho (tySigma A B) =
  cong suc (cong₂ _+_ (tyDepth-renTy rho A) (tyDepth-renTy (raiseRen rho) B))

-- Weakening preserves type depth
tyDepth-wkTy : (k : ℕ) -> (A : RawType) -> tyDepth (wkTyBy k A) ≡ tyDepth A
tyDepth-wkTy k A = tyDepth-renTy (addRen k) A

-- Comparison lemmas for Sigma components
tyDepth-fst<Sigma : (A B : RawType) -> tyDepth A < suc (tyDepth A + tyDepth B)
tyDepth-fst<Sigma A B = suc-≤-suc (≤SumLeft (tyDepth A) (tyDepth B))

tyDepth-snd<Sigma : (A B : RawType) -> tyDepth B < suc (tyDepth A + tyDepth B)
tyDepth-snd<Sigma A B = suc-≤-suc (≤SumRight (tyDepth B) (tyDepth A))
