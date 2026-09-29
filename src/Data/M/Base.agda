{-# OPTIONS --guardedness #-}

module Data.M.Base where

open import Data.Cont using (Cont; ⟦_⟧)

------------------------------------------------------------------------
-- Definition

record M (SP : Cont) : Set where
  coinductive
  field
    inf : ⟦ SP ⟧ (M SP)
open M
