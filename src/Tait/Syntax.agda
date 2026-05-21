{-# OPTIONS --safe #-}

-- Tait-style rebuild prototype (Phase K). Top + Sigma fragment.
--
-- Restricted fork of TReg.Syntax: types are tyTop / tySigma only,
-- terms are var / tmStar / tmPair / tmElSigma only. Dropping equality
-- types and equality terms removes the type/term cross-dependency, so RawType and RawTerm
-- are now fully independent inductive types (no `mutual` block).

module Tait.Syntax where

open import Tait.Prelude
open import Data.Nat using (ℕ ; zero ; suc)

data RawType : Type where
  tyTop   : RawType
  tySigma : RawType -> RawType -> RawType

data RawTerm : Type where
  var       : ℕ -> RawTerm
  tmStar    : RawTerm
  tmPair    : RawTerm -> RawTerm -> RawTerm
  tmElSigma : RawTerm -> RawTerm -> RawTerm
