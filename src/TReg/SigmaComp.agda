-- Cannot use --safe because CompTheorem.agda uses {-# TERMINATING #-}
{-# OPTIONS #-}

module TReg.SigmaComp where

open import TReg.CompTheorem public
  using
    ( compFSigmaClosed
    ; compISigmaClosed
    ; compCSigmaClosed
    ; compESigmaClosed
    )
