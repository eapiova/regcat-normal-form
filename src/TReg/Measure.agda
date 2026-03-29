{-# OPTIONS --safe #-}

module TReg.Measure where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_)
open import Cubical.Data.Nat.Properties using (max ; maxSuc)
open import Cubical.Data.Nat.Order using (_<_ ; _≤_ ; ≤-refl ; ≤-suc ; suc-≤-suc ; ≤SumLeft ; ≤SumRight ; <-wellfounded ; maxLUB)
open import Cubical.Induction.WellFounded using (Acc ; acc ; WellFounded)

open import TReg.Syntax
open import TReg.Substitution using (Subst ; subTy ; subTm ; liftSubst)

-- Type depth: measures the nesting of type constructors
tyDepth : RawType -> ℕ
tyDepth tyTop = 0
tyDepth (tySigma A B) = suc (tyDepth A + tyDepth B)
tyDepth (tyEq A a b) = suc (tyDepth A)
tyDepth (tyQtr A) = suc (tyDepth A)

-- Substitution preserves type depth
tyDepth-subTy : (sigma : Subst) -> (A : RawType) -> tyDepth (subTy sigma A) ≡ tyDepth A
tyDepth-subTy sigma tyTop = refl
tyDepth-subTy sigma (tySigma A B) =
  cong suc (cong₂ _+_ (tyDepth-subTy sigma A) (tyDepth-subTy (liftSubst sigma) B))
tyDepth-subTy sigma (tyEq A a b) = cong suc (tyDepth-subTy sigma A)
tyDepth-subTy sigma (tyQtr A) = cong suc (tyDepth-subTy sigma A)

-- Comparison lemmas for Sigma components
tyDepth-fst<Sigma : (A B : RawType) -> tyDepth A < suc (tyDepth A + tyDepth B)
tyDepth-fst<Sigma A B = suc-≤-suc (≤SumLeft {tyDepth A} {tyDepth B})

tyDepth-snd<Sigma : (A B : RawType) -> tyDepth B < suc (tyDepth A + tyDepth B)
tyDepth-snd<Sigma A B = suc-≤-suc (≤SumRight {tyDepth B} {tyDepth A})

-- Comparison lemmas for Eq and Qtr components (n < suc n)
tyDepth-base<Eq : (A : RawType) (a b : RawTerm) -> tyDepth A < tyDepth (tyEq A a b)
tyDepth-base<Eq A a b = ≤-refl

tyDepth-base<Qtr : (A : RawType) -> tyDepth A < tyDepth (tyQtr A)
tyDepth-base<Qtr A = ≤-refl

max3 : ℕ -> ℕ -> ℕ -> ℕ
max3 a b c = max a (max b c)

max-< : {a b n : ℕ} -> a < n -> b < n -> max a b < n
max-< {a = a} {b = b} a<n b<n =
  subst (_≤ _) (maxSuc {n = a} {m = b}) (maxLUB a<n b<n)

max3-< : {a b c n : ℕ} -> a < n -> b < n -> c < n -> max3 a b c < n
max3-< a<n b<n c<n = max-< a<n (max-< b<n c<n)
