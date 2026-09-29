module Data.W.Base where

open import Agda.Primitive using (Level)
open import Data.Product using (_,_)
open import Function using (_∘_)
open import Data.Cont.Base using (Cont; ⟦_⟧)

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- Definition

data W (SP : Cont) : Set where
  sup : ⟦ SP ⟧ (W SP) → W SP

elimW : {SP : Cont} (open Cont SP)
        (Q : W SP → Set ℓ) →
        (h : (s : S) (f : P s → W SP)
             → ((p : P s) → Q (f p))
             → Q (sup (s , f)))
        (w : W SP) → Q w
elimW Q h (sup (s , f)) = h s f (elimW Q h ∘ f)
