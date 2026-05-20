{-# OPTIONS --safe #-}

module TReg.SigmaComp where

open import TReg.FitsHelpers public
  using
    ( compFSigmaClosed
    ; compISigmaClosed
    ; compCSigmaClosed
    )

open import TReg.OpenHyp public
  using
    ( compESigmaClosed
    )
