-- Cannot use --safe because CompTheorem.agda uses {-# TERMINATING #-}
{-# OPTIONS --cubical --guardedness #-}

module TReg.Everything where

open import TReg.Syntax public
open import TReg.Context public
open import TReg.Substitution public
open import TReg.Evaluation public
open import TReg.Derivability public
open import TReg.Computability public
open import TReg.Presupposition public
open import TReg.Inversion public
open import TReg.Structural public
open import TReg.TopComp public
open import TReg.SigmaComp public
open import TReg.EqComp public
open import TReg.QtrComp public
open import TReg.CompTheorem public
open import TReg.MainTheorem public
