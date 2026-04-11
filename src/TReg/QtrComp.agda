-- Cannot use --safe because CompTheorem.agda uses {-# TERMINATING #-}
{-# OPTIONS #-}

module TReg.QtrComp where

open import TReg.CompTheorem public
  using
    ( compFQtrClosed
    ; compIQtrClosed
    ; compIQtrEqClosed
    ; compCQtrClosed
    ; compEQtrClosed
    )
